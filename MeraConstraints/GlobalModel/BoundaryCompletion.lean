import MeraConstraints.GlobalModel.BoundaryObservation

/-!
# Boundary completion of district constraints

Remark `rmk:positivity` leaves a district row free if its first unsupported
conditional occurs before a supported zero. A known row is therefore either
fully defined, or has a supported zero conditional. The nesting of the
cumulative `C_i` events makes this equivalent to the ordered reading in the
remark; the associated known value is zero in the latter case and the
observable product in the former. Values of free rows are never constrained.

The key reconstruction argument does not assume an observed factorization.
At a positive observed atom, every conditioning event needed for the chain
rule is supported, so the ordered Markov equations identify the product of
known district rows with that atom's mass. At a zero atom, the first zero
global prefix supplies a supported zero conditional in one district. Matching
that known row forces the constructed model's atom to zero as well.

Thus normalized independent profile laws matching the known rows reconstruct
the complete observed law. The final equivalence expresses completion by
either simplex feasibility or a checked H-representation. Connecting this
finite-profile characterization to an original hidden-variable graph uses
the separate canonicalization and c-degree-one realization theorems.
-/

namespace MeraConstraints.BoundaryCompletion

open FiniteProbability GlobalModel

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D)
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- All cumulative factors of this district row are supported. -/
def AllDefined (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : Prop :=
  ∀ i : Fin n, block i = d → mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0

/-- A supported zero decides the entire district row, regardless of later
unsupported factors. Such a zero cannot follow an unsupported earlier factor. -/
def SupportedZero (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : Prop :=
  ∃ i : Fin n, block i = d ∧ mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0 ∧
    conditional p (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i) = 0

/-- Precisely the district rows determined by the observed law. -/
def Known (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : Prop :=
  AllDefined G val block p d w ∨ SupportedZero G val block p d w

/-- Known zero rows are assigned zero before inspecting later factors.
On fully defined rows without a zero this is the usual observable product.
This function is used only under `Known`; its values at free rows are ignored. -/
noncomputable def knownValue (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : ℝ := by
  classical
  exact if SupportedZero G val block p d w then 0 else Reconstruction.observableFactor G val block p d w

theorem observableFactor_zero_of_supportedZero (p : FullAssign val → ℝ) (d : D)
    (w : FullAssign val) (hz : SupportedZero G val block p d w) :
    Reconstruction.observableFactor G val block p d w = 0 := by
  obtain ⟨i, hid, _, hi⟩ := hz
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, hid⟩ : {i : Fin n // block i = d})) hi

theorem knownValue_eq_observableFactor (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) :
    knownValue G val block p d w = Reconstruction.observableFactor G val block p d w := by
  classical
  by_cases hz : SupportedZero G val block p d w
  · simp only [knownValue, if_pos hz, observableFactor_zero_of_supportedZero G val block p d w hz]
  · simp only [knownValue, if_neg hz]

theorem knownValue_zero_of_supportedZero (p : FullAssign val → ℝ) (d : D)
    (w : FullAssign val) (hz : SupportedZero G val block p d w) :
    knownValue G val block p d w = 0 := by
  classical
  simp only [knownValue, if_pos hz]

theorem prefix_mass_ne_zero_of_point_nonzero (p : FullAssign val → ℝ)
    (hp : ∀ z, 0 ≤ p z) (w : FullAssign val) (hw : p w ≠ 0) (k : ℕ) :
    mass p (prefixEvent val w k) ≠ 0 := by
  intro hz
  have h := mass_zero_of_subset hp
    (Finset.singleton_subset_iff.mpr (self_mem_prefixEvent val w k)) hz
  exact hw (by simpa only [mass_singleton] using h)

theorem conditioning_mass_ne_zero_of_point_nonzero (p : FullAssign val → ℝ)
    (hp : ∀ z, 0 ≤ p z) (w : FullAssign val) (hw : p w ≠ 0) (i : Fin n) :
    mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0 := by
  intro hz
  have h := mass_zero_of_subset hp
    (Finset.singleton_subset_iff.mpr (Reconstruction.self_mem_conditioningEvent G val block w i)) hz
  exact hw (by simpa only [mass_singleton] using h)

/-- The finite chain rule needs support of the atom being evaluated, rather
than strict positivity of every atom in the observed law. -/
theorem assignment_eq_prod_prefixConditional_of_nonzero (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (w : FullAssign val) (hw : p w ≠ 0) :
    p w = ∏ i : Fin n, prefixConditional val p w i := by
  simp_rw [prefixConditional_eq_ratio]
  rw [Fin.prod_univ_eq_prod_range
    (fun k => mass p (prefixEvent val w (k + 1)) / mass p (prefixEvent val w k)) n]
  have h0 : mass p (prefixEvent val w 0) = 1 := by simpa using hp.2
  rw [prod_successive_ratios _ n h0
    (fun k _ => prefix_mass_ne_zero_of_point_nonzero val p hp.1 w hw k)]
  simp

variable [Fintype D]

/-- Pointwise reconstruction on supported atoms, using the actual chain rule
and the stated ordered Markov equations. -/
theorem point_eq_prod_observableFactor_of_nonzero (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hMarkov : Reconstruction.OrderedMarkov G val block p)
    (w : FullAssign val) (hw : p w ≠ 0) :
    p w = ∏ d, Reconstruction.observableFactor G val block p d w := by
  change p w = ∏ d, ∏ i : {i : Fin n // block i = d},
    conditional p (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i)
  rw [Fintype.prod_fiberwise block (fun i : Fin n =>
    conditional p (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i))]
  rw [assignment_eq_prod_prefixConditional_of_nonzero val p hp w hw]
  apply Finset.prod_congr rfl
  intro i _
  exact conditional_eq_of_subset_independent p _ _ _
    (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i) (hMarkov w i)
    (prefix_mass_ne_zero_of_point_nonzero val p hp.1 w hw i.val)
    (conditioning_mass_ne_zero_of_point_nonzero G val block p hp.1 w hw i)

private theorem exists_first_zero_step (a : ℕ → ℝ) (n : ℕ) (ha0 : a 0 ≠ 0)
    (han : a n = 0) : ∃ k < n, a k ≠ 0 ∧ a (k + 1) = 0 := by
  induction n with
  | zero => exact (ha0 han).elim
  | succ n ih =>
    by_cases hn : a n = 0
    · obtain ⟨k, hk, hk0, hks⟩ := ih hn
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), hk0, hks⟩
    · exact ⟨n, Nat.lt_succ_self n, hn, han⟩

omit [Fintype D] in
/-- The first zero global prefix of a zero observed atom gives a supported
zero cumulative conditional in some district. -/
theorem zero_point_has_supportedZero (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hMarkov : Reconstruction.OrderedMarkov G val block p)
    (w : FullAssign val) (hw : p w = 0) :
    ∃ d, SupportedZero G val block p d w := by
  have h0 : mass p (prefixEvent val w 0) ≠ 0 := by simp [hp.2]
  have hn : mass p (prefixEvent val w n) = 0 := by simpa using hw
  obtain ⟨k, hk, hpre, hnext⟩ := exists_first_zero_step
    (fun k => mass p (prefixEvent val w k)) n h0 hn
  let i : Fin n := ⟨k, hk⟩
  have hC : mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0 := by
    intro hz
    exact hpre (mass_zero_of_subset hp.1
      (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i) hz)
  have hprefix : prefixConditional val p w i = 0 := by
    rw [prefixConditional_eq_ratio, hnext, zero_div]
  have hrepl := conditional_eq_of_subset_independent p _ _ _
    (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i) (hMarkov w i) hpre hC
  exact ⟨block i, i, rfl, hC, hrepl.symm.trans hprefix⟩

/-- A generated model agrees with the observed law on every known district
row. No support restriction is imposed on the other observed configurations. -/
theorem factor_eq_knownValue_on_known (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d)) (d : D) (w : FullAssign val)
    (hKnown : Known G val block (observed G val block q) d w) :
    factor G val block q d w = knownValue G val block (observed G val block q) d w := by
  rw [knownValue_eq_observableFactor]
  rcases hKnown with hDefined | ⟨i, hid, hC, hz⟩
  · rw [factor_eq_prod_conditioning_of_supported G val block q hq d w hDefined]
    exact Finset.prod_subtype _ (by intro i; simp) _
  · have hfactor := factor_zero_of_supported_zero_conditional G val block q hq w i hC hz
    rw [hid] at hfactor
    rw [hfactor, observableFactor_zero_of_supportedZero G val block _ d w ⟨i, hid, hC, hz⟩]

/-- Full boundary reconstruction from matching known rows. Free rows impose
no matching requirement. The proof handles supported and zero atoms separately. -/
theorem observed_eq_of_known_rows (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hMarkov : Reconstruction.OrderedMarkov G val block p)
    (q : ∀ d, Profile G val block d → ℝ)
    (hmatch : ∀ d w, Known G val block p d w → factor G val block q d w = knownValue G val block p d w) :
    observed G val block q = p := by
  funext w
  rw [observed_eq_prod_factor]
  by_cases hw : p w = 0
  · obtain ⟨d, hd⟩ := zero_point_has_supportedZero G val block p hp hMarkov w hw
    rw [hw]
    apply Finset.prod_eq_zero (Finset.mem_univ d)
    exact (hmatch d w (Or.inr hd)).trans (knownValue_zero_of_supportedZero G val block p d w hd)
  · rw [point_eq_prod_observableFactor_of_nonzero G val block p hp hMarkov w hw]
    apply Finset.prod_congr rfl
    intro d _
    have hd : Known G val block p d w := Or.inl
      (fun i _ => conditioning_mass_ne_zero_of_point_nonzero G val block p hp.1 w hw i)
    exact (hmatch d w hd).trans (knownValue_eq_observableFactor G val block p d w)

/-- Reduced simplex feasibility: impose matrix equations only on known rows. -/
def FeasibleKnownRows (p : FullAssign val → ℝ) : Prop :=
  ∀ d, ∃ qd ∈ stdSimplex ℝ (Profile G val block d), ∀ w,
    Known G val block p d w → (matrix G val block d).mulVec qd w = knownValue G val block p d w

/-- Assemble independently feasible district completions and reconstruct the
whole observed law, including all zero-probability configurations. -/
theorem realize_of_known_rows_feasible (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hMarkov : Reconstruction.OrderedMarkov G val block p)
    (hfeasible : FeasibleKnownRows G val block p) :
    ∃ q : ∀ d, Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (Profile G val block d)) ∧ observed G val block q = p := by
  classical
  choose q hq hmatch using hfeasible
  refine ⟨q, hq, observed_eq_of_known_rows G val block p hp hMarkov q ?_⟩
  intro d w hw
  rw [factor_eq_mulVec]
  exact hmatch d w hw

/-- Boundary completion theorem for the finite independent-profile model.
The ordered equations are necessary by structural derivation, not assumed
about a generated model. Simplex feasibility is required only on known rows. -/
theorem finite_profile_iff_known_rows (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    (∃ q : ∀ d, Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (Profile G val block d)) ∧ observed G val block q = p) ↔
    Reconstruction.OrderedMarkov G val block p ∧ FeasibleKnownRows G val block p := by
  constructor
  · rintro ⟨q, hq, hobs⟩
    constructor
    · simpa [hobs] using observed_orderedMarkov_boundary G val block q hq
    · intro d
      refine ⟨q d, hq d, ?_⟩
      intro w hw
      have h := factor_eq_knownValue_on_known G val block q hq d w (by simpa [hobs] using hw)
      rw [factor_eq_mulVec] at h
      simpa [hobs] using h
  · rintro ⟨hMarkov, hfeasible⟩
    exact realize_of_known_rows_feasible G val block p hp hMarkov hfeasible

/-- Existence of full district vectors satisfying the checked H-system and
agreeing with the determined rows. The other entries are free variables. -/
def HCompletion {I E : D → Type*}
    (H : ∀ d, Polytope.HRep (matrix G val block d) (I d) (E d))
    (p : FullAssign val → ℝ) : Prop :=
  ∀ d, ∃ f : FullAssign val → ℝ,
    ((∀ i, ∑ w, (H d).inequalities i w * f w ≤ (H d).upper i) ∧
      (∀ e, ∑ w, (H d).equalities e w * f w = (H d).target e)) ∧
    ∀ w, Known G val block p d w → f w = knownValue G val block p d w

omit [Fintype D] in
theorem feasibleKnownRows_iff_HCompletion {I E : D → Type*}
    (H : ∀ d, Polytope.HRep (matrix G val block d) (I d) (E d)) (p : FullAssign val → ℝ) :
    FeasibleKnownRows G val block p ↔ HCompletion G val block H p := by
  constructor
  · intro h d
    obtain ⟨qd, hqd, hmatch⟩ := h d
    exact ⟨(matrix G val block d).mulVec qd,
      ((H d).exact_representation _).mp ⟨qd, hqd, rfl⟩, hmatch⟩
  · intro h d
    obtain ⟨f, hH, hmatch⟩ := h d
    obtain ⟨qd, hqd, heq⟩ := ((H d).exact_representation f).mpr hH
    refine ⟨qd, hqd, ?_⟩
    intro w hw
    rw [heq]
    exact hmatch w hw

/-- The H-completion and reduced-LP formulations in `rmk:positivity` are
equivalent characterizations of the same finite profile model. -/
theorem finite_profile_iff_HCompletion {I E : D → Type*}
    (H : ∀ d, Polytope.HRep (matrix G val block d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    (∃ q : ∀ d, Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (Profile G val block d)) ∧ observed G val block q = p) ↔
    Reconstruction.OrderedMarkov G val block p ∧ HCompletion G val block H p := by
  rw [finite_profile_iff_known_rows G val block p hp, feasibleKnownRows_iff_HCompletion G val block H p]

/-- All earlier factors of this same district are supported and positive. -/
def EarlierPositive (p : FullAssign val → ℝ) (w : FullAssign val) (i : Fin n) : Prop :=
  ∀ j : Fin n, block j = block i → j < i →
    mass p (Reconstruction.conditioningEvent G val block w j) ≠ 0 ∧
      0 < conditional p (valueEvent val w j) (Reconstruction.conditioningEvent G val block w j)

def AllPositive (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : Prop :=
  ∀ i : Fin n, block i = d → mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0 ∧
    0 < conditional p (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i)

/-- The first factor not positive is a supported zero. -/
def FirstZero (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : Prop :=
  ∃ i : Fin n, block i = d ∧ EarlierPositive G val block p w i ∧
    mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0 ∧
    conditional p (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i) = 0

/-- The first factor not positive is undefined, making this district row free. -/
def FirstUndefined (p : FullAssign val → ℝ) (d : D) (w : FullAssign val) : Prop :=
  ∃ i : Fin n, block i = d ∧ EarlierPositive G val block p w i ∧
    mass p (Reconstruction.conditioningEvent G val block w i) = 0

omit [Fintype D] in
theorem conditioningEvent_subset_of_earlier (w : FullAssign val) (j i : Fin n)
    (hji : j ≤ i) (hb : block j = block i) :
    Reconstruction.conditioningEvent G val block w i ⊆ Reconstruction.conditioningEvent G val block w j := by
  intro z hz
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, fun k hk => (Finset.mem_filter.mp hz).2 k
    (Reconstruction.conditioningVariables_mono G block j i hji hb hk)⟩

omit [Fintype D] in
/-- A supported later cumulative event forces all earlier district factors
to be supported and strictly positive. This justifies reading the row until
its first zero or undefined factor. -/
theorem earlierPositive_of_supported (p : FullAssign val → ℝ) (hp : ∀ z, 0 ≤ p z)
    (w : FullAssign val) (i : Fin n)
    (hCi : mass p (Reconstruction.conditioningEvent G val block w i) ≠ 0) :
    EarlierPositive G val block p w i := by
  intro j hb hji
  have hsubC := conditioningEvent_subset_of_earlier G val block w j i hji.le hb
  have hsubA : Reconstruction.conditioningEvent G val block w i ⊆ valueEvent val w j := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2 j ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hji, hb⟩⟩
  have hsubAC : Reconstruction.conditioningEvent G val block w i ⊆
      valueEvent val w j ∩ Reconstruction.conditioningEvent G val block w j := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hsubA hz, hsubC hz⟩
  have hnum : mass p (valueEvent val w j ∩ Reconstruction.conditioningEvent G val block w j) ≠ 0 := by
    intro hz
    exact hCi (mass_zero_of_subset hp hsubAC hz)
  have hden : mass p (Reconstruction.conditioningEvent G val block w j) ≠ 0 := by
    intro hz
    exact hCi (mass_zero_of_subset hp hsubC hz)
  exact ⟨hden, div_pos (lt_of_le_of_ne (mass_nonneg hp _) (Ne.symm hnum))
    (lt_of_le_of_ne (mass_nonneg hp _) (Ne.symm hden))⟩

omit [Fintype D] in
theorem supportedZero_iff_firstZero (p : FullAssign val → ℝ) (hp : ∀ z, 0 ≤ p z)
    (d : D) (w : FullAssign val) : SupportedZero G val block p d w ↔ FirstZero G val block p d w := by
  constructor
  · rintro ⟨i, hid, hC, hz⟩
    exact ⟨i, hid, earlierPositive_of_supported G val block p hp w i hC, hC, hz⟩
  · rintro ⟨i, hid, _, hC, hz⟩
    exact ⟨i, hid, hC, hz⟩

omit [Fintype D] in
/-- The known predicate exactly follows the manuscript's ordered rule:
all factors positive, or the first nonpositive factor is a supported zero. -/
theorem known_iff_allPositive_or_firstZero (p : FullAssign val → ℝ) (hp : ∀ z, 0 ≤ p z)
    (d : D) (w : FullAssign val) :
    Known G val block p d w ↔ AllPositive G val block p d w ∨ FirstZero G val block p d w := by
  classical
  constructor
  · intro hKnown
    by_cases hz : SupportedZero G val block p d w
    · exact Or.inr ((supportedZero_iff_firstZero G val block p hp d w).mp hz)
    · rcases hKnown with hdef | hzero
      · left
        intro i hid
        have hC := hdef i hid
        have hcond : conditional p (valueEvent val w i)
            (Reconstruction.conditioningEvent G val block w i) ≠ 0 :=
          fun hi => hz ⟨i, hid, hC, hi⟩
        exact ⟨hC, lt_of_le_of_ne (conditional_nonneg hp _ _) (Ne.symm hcond)⟩
      · exact (hz hzero).elim
  · rintro (hpos | hzero)
    · exact Or.inl (fun i hid => (hpos i hid).1)
    · exact Or.inr ((supportedZero_iff_firstZero G val block p hp d w).mpr hzero)

omit [Fintype D] in
/-- Exactly the rows whose first failure is undefined remain free. -/
theorem not_known_iff_firstUndefined (p : FullAssign val → ℝ) (hp : ∀ z, 0 ≤ p z)
    (d : D) (w : FullAssign val) :
    ¬ Known G val block p d w ↔ FirstUndefined G val block p d w := by
  classical
  constructor
  · intro hnot
    have hex : ∃ i : Fin n, block i = d ∧ mass p (Reconstruction.conditioningEvent G val block w i) = 0 := by
      by_contra hnone
      apply hnot
      left
      intro i hid hz
      exact hnone ⟨i, hid, hz⟩
    let U := Finset.univ.filter fun i : Fin n =>
      block i = d ∧ mass p (Reconstruction.conditioningEvent G val block w i) = 0
    have hU : U.Nonempty := by
      obtain ⟨i, hid, hz⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hid, hz⟩⟩
    let i := U.min' hU
    have hiU : i ∈ U := Finset.min'_mem U hU
    obtain ⟨hid, hi0⟩ := (Finset.mem_filter.mp hiU).2
    refine ⟨i, hid, ?_, hi0⟩
    intro j hjblock hji
    have hjd : block j = d := hjblock.trans hid
    have hC : mass p (Reconstruction.conditioningEvent G val block w j) ≠ 0 := by
      intro hz
      have hjU : j ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjd, hz⟩
      exact (not_le_of_gt hji) (Finset.min'_le U j hjU)
    have hcond : conditional p (valueEvent val w j)
        (Reconstruction.conditioningEvent G val block w j) ≠ 0 :=
      fun hz => hnot (Or.inr ⟨j, hjd, hC, hz⟩)
    exact ⟨hC, lt_of_le_of_ne (conditional_nonneg hp _ _) (Ne.symm hcond)⟩
  · rintro ⟨i, hid, hprev, hi0⟩ (hdef | ⟨j, hjd, hCj, hj0⟩)
    · exact hdef i hid hi0
    · rcases lt_trichotomy j i with hji | heq | hij
      · exact (ne_of_gt (hprev j (hjd.trans hid.symm) hji).2) hj0
      · subst j
        exact hCj hi0
      · exact (earlierPositive_of_supported G val block p hp w j hCj i (hid.trans hjd.symm) hij).1 hi0

end MeraConstraints.BoundaryCompletion
