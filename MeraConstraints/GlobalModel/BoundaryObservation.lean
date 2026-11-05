import MeraConstraints.GlobalModel.BoundaryMarkov

/-!
# Conditionals given C_i when some probabilities are zero

Remark 2 (`rmk:positivity`) reads the product defining an entry of the district
factor from the first member to the last. The first factor that is not positive
decides the entry: if it is zero, the entry is zero; if it is undefined because
`Pr(C_i = c_i) = 0`, the entry is free.

The event `C_i = c_i` can have positive probability although the prefix of the
entry's complete assignment has probability zero, so the ratio formula of
`GlobalModel.BoundaryMarkov` does not apply to the entry directly. If
`Pr(C_i = c_i) > 0`, some configuration with this `C_i` has positive probability.
Changing its value at `V_i` to the entry's value gives a configuration with the same
`C_i` whose prefix has positive probability. By the dependence on `C_i` alone, the
conditional of `V_i` given `C_i` is a ratio of two prefix factors with a positive
denominator (`conditioning_supported_prefixFactor_pos_and_ratio`).

Two steps of the proof of Remark 2 follow. If a defined factor is zero, the entry of
the block is zero whatever the later factors are
(`factor_zero_of_supported_zero_conditional`). If every factor is defined, the
entry is the product of the conditionals, even when the last one is zero
(`factor_eq_prod_conditioning_of_supported`). The rule that decides which entries
are free, and the equivalence in Remark 2, are in `BoundaryCompletion`.
-/

namespace MeraConstraints.GlobalModel

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [Fintype D] [DecidableEq D] (block : Fin n → D)
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [Fintype D] in
/-- A prefix factor is nonnegative when the block's profile probabilities are. -/
theorem prefixFactor_nonneg (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (d : D) (k : ℕ) (w : FullAssign val) : 0 ≤ prefixFactor G val block q d k w := by
  classical
  unfold prefixFactor
  apply Finset.sum_nonneg
  intro r _
  split
  · exact (hq d).1 r
  · exact le_rfl

/-- If `Pr(C_i = c_i) > 0`, the prefix factor of `V_i`'s block at position `i` is
positive, and the conditional of `V_i` given `C_i` is the ratio of the prefix factors
at positions `i + 1` and `i`. The prefix of `w` before `V_i` may have probability
zero. -/
theorem conditioning_supported_prefixFactor_pos_and_ratio
    (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (w : FullAssign val) (i : Fin n)
    (hC : mass (observed G val block q)
      (Reconstruction.conditioningEvent G val block w i) ≠ 0) :
    0 < prefixFactor G val block q (block i) i.val w ∧
      conditional (observed G val block q) (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) =
      prefixFactor G val block q (block i) (i.val + 1) w /
        prefixFactor G val block q (block i) i.val w := by
  classical
  let p := observed G val block q
  let C := Reconstruction.conditioningEvent G val block w i
  have hp : ∀ z, 0 ≤ p z := (observed_mem_stdSimplex G val block q hq).1
  have hCpos : 0 < mass p C := lt_of_le_of_ne (mass_nonneg hp C) (Ne.symm hC)
  obtain ⟨z, hzC, hzpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun z (_ : z ∈ C) => hp z)).mp hCpos
  let v : FullAssign val := Function.update z i (w i)
  have hvi : v i = w i := by simp [v]
  have hvz : ∀ j : Fin n, j < i → v j = z j := by
    intro j hj
    exact Function.update_of_ne (ne_of_lt hj) _ _
  have hvC : ∀ j ∈ Reconstruction.conditioningVariables G block i, v j = w j := by
    intro j hj
    exact (hvz j (Reconstruction.conditioningVariables_lt G block i j hj)).trans
      ((Finset.mem_filter.mp hzC).2 j hj)
  have hzpre : 0 < mass p (prefixEvent val z i.val) :=
    Finset.sum_pos' (fun a _ => hp a) ⟨z, self_mem_prefixEvent val z i.val, hzpos⟩
  have heqpre : prefixEvent val v i.val = prefixEvent val z i.val := by
    ext a
    simp only [prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      exact (h j hj).trans (hvz j hj)
    · intro h j hj
      exact (h j hj).trans (hvz j hj).symm
  have hvpre : mass p (prefixEvent val v i.val) ≠ 0 := by rw [heqpre]; exact hzpre.ne'
  have hCE : Reconstruction.conditioningEvent G val block v i = C := by
    ext a
    simp only [Reconstruction.conditioningEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, C]
    constructor
    · intro h j hj
      exact (h j hj).trans (hvC j hj)
    · intro h j hj
      exact (h j hj).trans (hvC j hj).symm
  have hA : valueEvent val v i = valueEvent val w i := by
    ext a
    simp only [valueEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hvi]
  have hold := prefixFactor_congr_conditioning G val block q w v i i.val (Nat.le_succ _)
    (fun j hj => (hvC j hj).symm) hvi.symm
  have hnew := prefixFactor_congr_conditioning G val block q w v i (i.val + 1) le_rfl
    (fun j hj => (hvC j hj).symm) hvi.symm
  have hprod : (∏ d, prefixFactor G val block q d i.val v) ≠ 0 := by
    rw [← prefix_mass_eq_prod_prefixFactor]
    exact hvpre
  have hden : prefixFactor G val block q (block i) i.val w ≠ 0 := by
    rw [hold]
    exact (Finset.prod_ne_zero_iff.mp hprod) (block i) (Finset.mem_univ _)
  constructor
  · exact lt_of_le_of_ne (prefixFactor_nonneg G val block q hq _ _ _) (Ne.symm hden)
  · have hcond := prefixConditional_eq_conditioning_of_supported G val block q hq v i hvpre
    have hratio := prefixConditional_eq_prefixFactor_ratio G val block q v i hvpre
    have h := hcond.symm.trans hratio
    rw [hA, hCE, ← hnew, ← hold] at h
    exact h

/-- The ratio formula for the conditional of `V_i` given `C_i`, when `Pr(C_i = c_i) > 0`. -/
theorem conditional_eq_prefixFactor_ratio_of_conditioning_supported
    (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (w : FullAssign val) (i : Fin n)
    (hC : mass (observed G val block q)
      (Reconstruction.conditioningEvent G val block w i) ≠ 0) :
    conditional (observed G val block q) (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) =
      prefixFactor G val block q (block i) (i.val + 1) w /
        prefixFactor G val block q (block i) i.val w :=
  (conditioning_supported_prefixFactor_pos_and_ratio G val block q hq w i hC).2

theorem prefixFactor_pos_of_conditioning_supported
    (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (w : FullAssign val) (i : Fin n)
    (hC : mass (observed G val block q)
      (Reconstruction.conditioningEvent G val block w i) ≠ 0) :
    0 < prefixFactor G val block q (block i) i.val w :=
  (conditioning_supported_prefixFactor_pos_and_ratio G val block q hq w i hC).1

omit [Fintype D] in
/-- For probability vectors `q d`, `factor` is at most every prefix factor. -/
theorem factor_le_prefixFactor (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (d : D) (k : ℕ) (w : FullAssign val) :
    factor G val block q d w ≤ prefixFactor G val block q d k w := by
  classical
  unfold factor prefixFactor
  apply Finset.sum_le_sum
  intro r _
  by_cases hfull : Compatible G val block d w r
  · have hpre : PrefixCompatible G val block d k w r := fun i _ => hfull i
    simp only [if_pos hfull, if_pos hpre, le_refl]
  · by_cases hpre : PrefixCompatible G val block d k w r
    · simp only [if_neg hfull, if_pos hpre]
      exact (hq d).1 r
    · simp only [if_neg hfull, if_neg hpre, le_refl]

omit [Fintype D] in
theorem factor_zero_of_prefixFactor_zero (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (d : D) (k : ℕ) (w : FullAssign val)
    (hz : prefixFactor G val block q d k w = 0) : factor G val block q d w = 0 := by
  apply le_antisymm
  · exact (factor_le_prefixFactor G val block q hq d k w).trans_eq hz
  · rw [← prefixFactor_full]
    exact prefixFactor_nonneg G val block q hq d n w

/-- A step in the proof of Remark 2 (`rmk:positivity`): if `Pr(C_i = c_i) > 0` and the
conditional of `V_i` given `C_i` is zero, the entry `factor` of the block is zero,
even if later factors are undefined. -/
theorem factor_zero_of_supported_zero_conditional
    (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (w : FullAssign val) (i : Fin n)
    (hC : mass (observed G val block q)
      (Reconstruction.conditioningEvent G val block w i) ≠ 0)
    (hz : conditional (observed G val block q) (valueEvent val w i)
      (Reconstruction.conditioningEvent G val block w i) = 0) :
    factor G val block q (block i) w = 0 := by
  obtain ⟨hden, hratio⟩ := conditioning_supported_prefixFactor_pos_and_ratio G val block q hq w i hC
  rw [hz] at hratio
  have hafter : prefixFactor G val block q (block i) (i.val + 1) w = 0 := by
    have h := (div_eq_iff hden.ne').mp hratio.symm
    simpa only [zero_mul] using h
  exact factor_zero_of_prefixFactor_zero G val block q hq (block i) (i.val + 1) w hafter

private theorem prod_range_eq_of_step (a t : ℕ → ℝ) (n : ℕ) (ha0 : a 0 = 1)
    (hstep : ∀ k < n, a (k + 1) = a k * t k) :
    (∏ k ∈ Finset.range n, t k) = a n := by
  induction n with
  | zero => simpa using ha0.symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
    exact (hstep n (Nat.lt_succ_self n)).symm

/-- A step in the proof of Remark 2 (`rmk:positivity`): if `Pr(C_i = c_i) > 0` for
every member of the block, the entry `factor` is the product of the conditionals of
the members given `C_i`. Individual factors, including the last, may be zero. -/
theorem factor_eq_prod_conditioning_of_supported
    (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (d : D) (w : FullAssign val)
    (hDefined : ∀ i : Fin n, block i = d → mass (observed G val block q)
      (Reconstruction.conditioningEvent G val block w i) ≠ 0) :
    factor G val block q d w =
      ∏ i ∈ Finset.univ.filter (fun i => block i = d),
        conditional (observed G val block q) (valueEvent val w i)
          (Reconstruction.conditioningEvent G val block w i) := by
  classical
  let p := observed G val block q
  let a := fun k => prefixFactor G val block q d k w
  let t := fun k => if hk : k < n then
      if block ⟨k, hk⟩ = d then conditional p (valueEvent val w ⟨k, hk⟩)
        (Reconstruction.conditioningEvent G val block w ⟨k, hk⟩) else 1
    else 1
  have ha0 : a 0 = 1 := by
    rw [show a 0 = ∑ r, q d r from prefixFactor_zero G val block q d w]
    exact (hq d).2
  have hstep : ∀ k < n, a (k + 1) = a k * t k := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have ht : t k = if block i = d then conditional p (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) else 1 := by
      simp only [t, dif_pos hk, i]
    rw [ht]
    by_cases hid : block i = d
    · rw [if_pos hid]
      have hden := prefixFactor_pos_of_conditioning_supported G val block q hq w i (hDefined i hid)
      have hratio := conditional_eq_prefixFactor_ratio_of_conditioning_supported G val block q hq w i
        (hDefined i hid)
      have h := (div_eq_iff hden.ne').mp hratio.symm
      rw [hid] at h
      simpa only [mul_comm] using h
    · rw [if_neg hid, mul_one]
      exact prefixFactor_succ_of_ne G val block q d i w (Ne.symm hid)
  have hprod := prod_range_eq_of_step a t n ha0 hstep
  rw [← Fin.prod_univ_eq_prod_range t n] at hprod
  have ht_fin : ∀ i : Fin n, t i.val = if block i = d then
      conditional p (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i) else 1 := by
    intro i
    simp only [t, dif_pos i.isLt]
  calc
    factor G val block q d w = a n := (prefixFactor_full G val block q d w).symm
    _ = ∏ i : Fin n, t i.val := hprod.symm
    _ = ∏ i : Fin n, if block i = d then conditional p (valueEvent val w i)
        (Reconstruction.conditioningEvent G val block w i) else 1 :=
      Finset.prod_congr rfl fun i _ => ht_fin i
    _ = _ := by rw [Finset.prod_filter]

end MeraConstraints.GlobalModel
