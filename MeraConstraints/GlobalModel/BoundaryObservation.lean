import MeraConstraints.GlobalModel.BoundaryMarkov

/-!
# Supported cumulative-conditionals on boundary strata

Remark `rmk:positivity` decides a district row from its cumulative conditional
factors until the first zero or undefined factor. A cumulative `C_i` event can
have positive mass even when the particular full-predecessor assignment used
to write that row has zero mass. Thus the supported-prefix result alone does
not justify computing its observed conditional.

Here a supported `C_i` event supplies an observed configuration with positive
mass. Changing only its current coordinate to the row's desired value keeps
its predecessor event supported, while matching `C_i` and the current value.
The cumulative dependence theorem transports both block prefix masses back
to the original row. Supported factor replacement then proves the observed
`C_i` conditional is their ratio, with a strictly positive denominator.

The final soundness results show that a supported zero conditional forces
the complete district factor to zero, regardless of later undefined factors,
and that a row whose cumulative factors are all defined equals their product.
The latter proof uses a multiplicative recurrence, allowing its last factor
to vanish. These results do not assign a conditional meaning to a zero-mass
`C_i` event or prove the full free-entry completion equivalence.
-/

namespace MeraConstraints.GlobalModel

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [Fintype D] [DecidableEq D] (block : Fin n → D)
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [Fintype D] in
/-- Nonnegative profile masses give nonnegative partial block-event masses. -/
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

/-- A supported cumulative event gives a strictly positive own-block prefix
mass and identifies its observed conditional with the next prefix-mass ratio.
No support assumption is made on the literal global prefix of `w`. -/
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

/-- Observable cumulative-conditioning ratio, on exactly its event support. -/
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
/-- The full structural event is contained in each of its prefix events. -/
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

/-- The zero-entry soundness direction of Remark `rmk:positivity`: a zero
conditional at a supported cumulative event forces the entire district row
to be zero, even when some later conditional factors are undefined. -/
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

/-- The defined-row soundness direction of Remark `rmk:positivity`: if all
cumulative conditioning events in this district row are supported, their
conditional product equals the actual structural factor. The proof uses a
multiplicative recurrence, so its last factor may be zero. -/
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
