import MeraConstraints.GlobalModel.Prefix
import MeraConstraints.Reconstruction

/-!
# Deriving the ordered Markov equations from independent mechanisms

The cumulative conditioning set `C_i` contains every earlier member of the
current block and every external parent of its members up to and including
`i`. Consequently, the two block prefix masses appearing in the observed
prefix conditional depend only on `C_i` and the current value. This statement
is proved directly from the parent-restricted response functions.

To remove the other observed predecessors, partition the `C_i` assignment
event into fibers indexed by their complete predecessor assignments. Every
nonempty fiber has the same conditional ratio, and the finite averaging
lemma therefore gives that ratio for the whole conditioning event. The
ordered conditional-independence cross-product equation follows.

Thus `Reconstruction.OrderedMarkov` is a theorem for the generated independent
profile model, rather than an assumption about that generated law. Strict
positivity is the manuscript's standing support assumption. This does not
yet establish every graphical separation theorem for arbitrary latent
measures; it proves exactly the ordered equations used in reconstruction.
-/

namespace MeraConstraints.GlobalModel

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [Fintype D] [DecidableEq D] (block : Fin n → D)

omit [Fintype D] in
private theorem member_mem_conditioning_or_current (i j : Fin n)
    (hj : j.val < i.val + 1) (hb : block j = block i) :
    j ∈ Reconstruction.conditioningVariables G block i ∨ j = i := by
  by_cases hji : j = i
  · exact Or.inr hji
  · left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inl ⟨?_, hb⟩⟩
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    omega

omit [Fintype D] in
private theorem parent_mem_conditioning (i j l : Fin n)
    (hj : j.val < i.val + 1) (hb : block j = block i) (hl : l ∈ G.parents j) :
    l ∈ Reconstruction.conditioningVariables G block i := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hji : j ≤ i := by change j.val ≤ i.val; omega
  by_cases hbl : block l = block i
  · exact Or.inl ⟨lt_of_lt_of_le (G.parents_lt hl) hji, hbl⟩
  · exact Or.inr ⟨j, hji, hb, hl, hbl⟩

omit [Fintype D] in
/-- Prefix equations of the current block depend only on `C_i` and `V_i`.
The cutoff may be either side of the current observation. -/
theorem prefixCompatible_congr_conditioning (w v : FullAssign val) (i : Fin n)
    (k : ℕ) (hk : k ≤ i.val + 1)
    (hC : ∀ j ∈ Reconstruction.conditioningVariables G block i, w j = v j)
    (hi : w i = v i) (r : Profile G val block (block i)) :
    PrefixCompatible G val block (block i) k w r ↔
      PrefixCompatible G val block (block i) k v r := by
  have hmember : ∀ j : {j : Fin n // block j = block i}, j.1.val < k → w j = v j := by
    intro j hj
    rcases j with ⟨j, hjblock⟩
    rcases member_mem_conditioning_or_current G block i j (Nat.lt_of_lt_of_le hj hk) hjblock with h | h
    · exact hC j h
    · subst j
      exact hi
  have hparents : ∀ j : {j : Fin n // block j = block i}, j.1.val < k →
      PaAssign.restrict (G := G) w j = PaAssign.restrict (G := G) v j := by
    intro j hj
    funext l
    exact hC l (parent_mem_conditioning G block i j l (Nat.lt_of_lt_of_le hj hk) j.2 l.2)
  constructor
  · intro h j hj
    rw [← hparents j hj, ← hmember j hj]
    exact h j hj
  · intro h j hj
    rw [hparents j hj, hmember j hj]
    exact h j hj

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [Fintype D] in
/-- The associated linear block prefix masses have the same dependence. -/
theorem prefixFactor_congr_conditioning (q : ∀ d, Profile G val block d → ℝ)
    (w v : FullAssign val) (i : Fin n) (k : ℕ) (hk : k ≤ i.val + 1)
    (hC : ∀ j ∈ Reconstruction.conditioningVariables G block i, w j = v j)
    (hi : w i = v i) :
    prefixFactor G val block q (block i) k w = prefixFactor G val block q (block i) k v := by
  classical
  unfold prefixFactor
  apply Finset.sum_congr rfl
  intro r _
  rw [prefixCompatible_congr_conditioning G val block w v i k hk hC hi r]

/-- The global-prefix conditional is constant when `C_i` and the current
value are fixed, even if the other global predecessors change. -/
theorem prefixConditional_congr_conditioning (q : ∀ d, Profile G val block d → ℝ)
    (hpos : ∀ z, 0 < observed G val block q z) (w v : FullAssign val) (i : Fin n)
    (hC : ∀ j ∈ Reconstruction.conditioningVariables G block i, w j = v j)
    (hi : w i = v i) :
    prefixConditional val (observed G val block q) w i =
      prefixConditional val (observed G val block q) v i := by
  rw [prefixConditional_eq_prefixFactor_ratio G val block q w i
      (prefix_mass_pos val _ hpos w i.val).ne',
    prefixConditional_eq_prefixFactor_ratio G val block q v i
      (prefix_mass_pos val _ hpos v i.val).ne']
  rw [prefixFactor_congr_conditioning G val block q w v i (i.val + 1) le_rfl hC hi,
    prefixFactor_congr_conditioning G val block q w v i i.val (Nat.le_succ _) hC hi]

/-- Values of all global predecessors of one observed coordinate. -/
abbrev PredecessorAssign (i : Fin n) :=
  ∀ j : {j : Fin n // j.val < i.val}, val j

/-- Extend a predecessor assignment using the reference assignment for the
current and later variables. The construction preserves the current value. -/
def prefixRepresentative (w : FullAssign val) (i : Fin n)
    (b : PredecessorAssign val i) : FullAssign val :=
  fun j => if hj : j.val < i.val then b ⟨j, hj⟩ else w j

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
@[simp] theorem prefixRepresentative_current (w : FullAssign val) (i : Fin n)
    (b : PredecessorAssign val i) : prefixRepresentative val w i b i = w i := by
  simp [prefixRepresentative]

/-- The fiber of a predecessor assignment is its full observed prefix event. -/
theorem predecessor_fiber_eq_prefix (w : FullAssign val) (i : Fin n)
    (b : PredecessorAssign val i) :
    fiber (fun z : FullAssign val => fun j : {j : Fin n // j.val < i.val} => z j) b =
      prefixEvent val (prefixRepresentative val w i b) i.val := by
  ext z
  simp only [fiber, prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j hj
    have heq := congrFun h ⟨j, hj⟩
    simpa only [prefixRepresentative, dif_pos hj] using heq
  · intro h
    funext j
    simpa only [prefixRepresentative, dif_pos j.2] using h j j.2

omit [Fintype D] in
/-- Finite averaging removes predecessors outside `C_i` for any positive
mass function whose prefix conditional has the stated dependence. This
probability lemma does not require a response-profile representation. -/
theorem prefixConditional_eq_conditioning_of_congr (p : FullAssign val → ℝ)
    (hpos : ∀ z, 0 < p z)
    (hcongr : ∀ (w v : FullAssign val) (i : Fin n),
      (∀ j ∈ Reconstruction.conditioningVariables G block i, w j = v j) → w i = v i →
      prefixConditional val p w i = prefixConditional val p v i)
    (w : FullAssign val) (i : Fin n) :
    prefixConditional val p w i =
      conditional p (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) := by
  classical
  let A := valueEvent val w i
  let C := Reconstruction.conditioningEvent G val block w i
  let Z := fun z : FullAssign val => fun j : {j : Fin n // j.val < i.val} => z j
  have hCpos : mass p C ≠ 0 :=
    (mass_pos_of_mem hpos (Reconstruction.self_mem_conditioningEvent G val block w i)).ne'
  symm
  apply conditional_eq_of_fiberwise_mass p A C Z _ hCpos
  intro b
  let v := prefixRepresentative val w i b
  have hB : fiber Z b = prefixEvent val v i.val := predecessor_fiber_eq_prefix val w i b
  by_cases hvC : v ∈ C
  · have hvC' : ∀ j ∈ Reconstruction.conditioningVariables G block i, v j = w j :=
      (Finset.mem_filter.mp hvC).2
    have hBC : prefixEvent val v i.val ⊆ C := by
      intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      exact ((Finset.mem_filter.mp hz).2 j (Reconstruction.conditioningVariables_lt G block i j hj)).trans
        (hvC' j hj)
    have hCB : C ∩ fiber Z b = prefixEvent val v i.val := by
      rw [hB, Finset.inter_eq_right.mpr hBC]
    have hA : A = valueEvent val v i := by
      ext z
      simp only [A, valueEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      change z i = w i ↔ z i = prefixRepresentative val w i b i
      rw [prefixRepresentative_current]
    have hcond : conditional p (valueEvent val v i) (prefixEvent val v i.val) =
        prefixConditional val p w i := by
      exact (hcongr w v i
        (fun j hj => (hvC' j hj).symm) (prefixRepresentative_current val w i b).symm).symm
    rw [Finset.inter_assoc, hCB, hA]
    have hm := conditional_mul_mass p (valueEvent val v i) (prefixEvent val v i.val)
      (prefix_mass_pos val p hpos v i.val).ne'
    rw [hcond] at hm
    exact hm.symm
  · have hCB : C ∩ fiber Z b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzC, hzB⟩ := Finset.mem_inter.mp hz
      apply hvC
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      have hzprefix : z ∈ prefixEvent val v i.val := hB ▸ hzB
      have hzv := (Finset.mem_filter.mp hzprefix).2 j
        (Reconstruction.conditioningVariables_lt G block i j hj)
      exact hzv.symm.trans ((Finset.mem_filter.mp hzC).2 j hj)
    rw [Finset.inter_assoc, hCB]
    simp [mass]

/-- The profile construction supplies the dependence needed by the generic
finite-averaging theorem. -/
theorem prefixConditional_eq_conditioning (q : ∀ d, Profile G val block d → ℝ)
    (hpos : ∀ z, 0 < observed G val block q z) (w : FullAssign val) (i : Fin n) :
    prefixConditional val (observed G val block q) w i =
      conditional (observed G val block q) (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) :=
  prefixConditional_eq_conditioning_of_congr G val block _ hpos
    (prefixConditional_congr_conditioning G val block q hpos) w i

/-- Generated independent-profile laws satisfy the precise ordered local
Markov equations used in the manuscript's reconstruction proof. -/
theorem observed_orderedMarkov (q : ∀ d, Profile G val block d → ℝ)
    (hpos : ∀ z, 0 < observed G val block q z) :
    Reconstruction.OrderedMarkov G val block (observed G val block q) := by
  intro w i
  let p := observed G val block q
  let A := valueEvent val w i
  let B := prefixEvent val w i.val
  let C := Reconstruction.conditioningEvent G val block w i
  have hB : mass p B ≠ 0 := (prefix_mass_pos val _ hpos w i.val).ne'
  have hC : mass p C ≠ 0 :=
    (mass_pos_of_mem hpos (Reconstruction.self_mem_conditioningEvent G val block w i)).ne'
  have hBC : B ∩ C = B := Finset.inter_eq_left.mpr
    (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i)
  have h := prefixConditional_eq_conditioning G val block q hpos w i
  change mass p (A ∩ B) / mass p B = mass p (A ∩ C) / mass p C at h
  change mass p ((A ∩ B) ∩ C) * mass p C = mass p (A ∩ C) * mass p (B ∩ C)
  rw [Finset.inter_assoc, hBC]
  exact (div_eq_div_iff hB hC).mp h

end MeraConstraints.GlobalModel
