import MeraConstraints.GlobalModel.OrderedMarkov

/-!
# Ordered Markov equations on the boundary of the probability simplex

Remark `rmk:positivity` distinguishes observed conditionals on their support
from entries left undetermined by zero conditioning probabilities. The
strictly positive derivation of the ordered Markov property can be extended
without assigning interpretations to such unsupported conditional values.

For a supported global prefix, the prefix-factor ratio remains valid. Its
constancy across supported predecessor fibers follows from the same cumulative
`C_i` dependence lemma. A fiber of zero mass contributes zero to the numerator
as well, by nonnegativity and event inclusion. Finite averaging therefore
still removes the other predecessors. If the original global prefix has
zero mass, its conditional-independence cross-product equation is simply a
zero equation. Thus all generated normalized profile models satisfy the
ordered Markov equations, including those on the boundary.

This is the Markov and supported factor-replacement step needed by the
boundary remark. It does not yet prove the full free-entry completion rule
or the boundary completeness theorem.
-/

namespace MeraConstraints.FiniteProbability

variable {Ω : Type*}

/-- Nonnegative finite mass is monotone under inclusion of events. -/
theorem mass_mono_of_nonneg {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x)
    {A B : Finset Ω} (hAB : A ⊆ B) : mass p A ≤ mass p B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hp x)

/-- Every subevent of a zero-mass event has zero mass under a nonnegative law. -/
theorem mass_zero_of_subset {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x)
    {A B : Finset Ω} (hAB : A ⊆ B) (hB : mass p B = 0) : mass p A = 0 := by
  apply le_antisymm
  · exact (mass_mono_of_nonneg hp hAB).trans_eq hB
  · exact mass_nonneg hp A

end MeraConstraints.FiniteProbability

namespace MeraConstraints.GlobalModel

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [Fintype D] [DecidableEq D] (block : Fin n → D)
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Prefix conditional constancy needs support of just the two prefixes,
not strict positivity of the whole observed distribution. -/
theorem prefixConditional_congr_conditioning_of_supported
    (q : ∀ d, Profile G val block d → ℝ) (w v : FullAssign val) (i : Fin n)
    (hw : mass (observed G val block q) (prefixEvent val w i.val) ≠ 0)
    (hv : mass (observed G val block q) (prefixEvent val v i.val) ≠ 0)
    (hC : ∀ j ∈ Reconstruction.conditioningVariables G block i, w j = v j)
    (hi : w i = v i) :
    prefixConditional val (observed G val block q) w i =
      prefixConditional val (observed G val block q) v i := by
  rw [prefixConditional_eq_prefixFactor_ratio G val block q w i hw,
    prefixConditional_eq_prefixFactor_ratio G val block q v i hv]
  rw [prefixFactor_congr_conditioning G val block q w v i (i.val + 1) le_rfl hC hi,
    prefixFactor_congr_conditioning G val block q w v i i.val (Nat.le_succ _) hC hi]

/-- Supported factor replacement for generated laws, with no global strict
positivity assumption. Unsupported predecessor fibers contribute zero mass. -/
theorem prefixConditional_eq_conditioning_of_supported
    (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (w : FullAssign val) (i : Fin n)
    (hw : mass (observed G val block q) (prefixEvent val w i.val) ≠ 0) :
    prefixConditional val (observed G val block q) w i =
      conditional (observed G val block q) (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) := by
  classical
  let p := observed G val block q
  let A := valueEvent val w i
  let C := Reconstruction.conditioningEvent G val block w i
  let Z := fun z : FullAssign val => fun j : {j : Fin n // j.val < i.val} => z j
  have hp : ∀ z, 0 ≤ p z := (observed_mem_stdSimplex G val block q hq).1
  have hCpos : mass p C ≠ 0 := by
    intro hCzero
    exact hw (mass_zero_of_subset hp
      (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i) hCzero)
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
    rw [Finset.inter_assoc, hCB, hA]
    by_cases hv : mass p (prefixEvent val v i.val) = 0
    · rw [mass_zero_of_subset hp Finset.inter_subset_right hv, hv, mul_zero]
    · have hcond : conditional p (valueEvent val v i) (prefixEvent val v i.val) =
          prefixConditional val p w i := by
        exact (prefixConditional_congr_conditioning_of_supported G val block q w v i hw hv
          (fun j hj => (hvC' j hj).symm) (prefixRepresentative_current val w i b).symm).symm
      have hm := conditional_mul_mass p (valueEvent val v i) (prefixEvent val v i.val) hv
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

/-- The ordered cross-product Markov equations hold for every normalized
nonnegative independent-profile model, including zero-probability strata. -/
theorem observed_orderedMarkov_boundary (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d)) :
    Reconstruction.OrderedMarkov G val block (observed G val block q) := by
  intro w i
  let p := observed G val block q
  let A := valueEvent val w i
  let B := prefixEvent val w i.val
  let C := Reconstruction.conditioningEvent G val block w i
  have hp : ∀ z, 0 ≤ p z := (observed_mem_stdSimplex G val block q hq).1
  have hBC : B ∩ C = B := Finset.inter_eq_left.mpr
    (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i)
  change mass p ((A ∩ B) ∩ C) * mass p C = mass p (A ∩ C) * mass p (B ∩ C)
  rw [Finset.inter_assoc, hBC]
  by_cases hB : mass p B = 0
  · rw [mass_zero_of_subset hp Finset.inter_subset_right hB, hB, zero_mul, mul_zero]
  · have hC : mass p C ≠ 0 := by
      intro hCzero
      exact hB (mass_zero_of_subset hp
        (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i) hCzero)
    have h := prefixConditional_eq_conditioning_of_supported G val block q hq w i hB
    change mass p (A ∩ B) / mass p B = mass p (A ∩ C) / mass p C at h
    exact (div_eq_div_iff hB hC).mp h

end MeraConstraints.GlobalModel
