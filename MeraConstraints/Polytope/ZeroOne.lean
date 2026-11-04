import MeraConstraints.Polytope

/-!
# A zero/one mixture point must be a generating column

If all matrix entries lie in [0,1], a zero/one point of its finite mixture
polytope equals every column with positive weight in a representing mixture.
One such column exists because the weights sum to one. Zero coordinates use
nonnegative weighted entries; one coordinates use nonnegative weighted
complements. The selected column is common to every row.

This proves the extreme-point step used in Appendix `prop:ineqstructure` (i)
without assuming an external vertex enumeration or distinct matrix columns.
-/

namespace MeraConstraints.Polytope

variable {Row Col : Type*} [Fintype Col]

theorem zero_one_mixture_is_column (B : Matrix Row Col ℝ) (p : Row → ℝ)
    (hB : ∀ i j, 0 ≤ B i j ∧ B i j ≤ 1) (hp : ∀ i, p i = 0 ∨ p i = 1)
    (hmix : p ∈ mixture B) : ∃ j, ∀ i, B i j = p i := by
  classical
  obtain ⟨q, hq, hmix⟩ := hmix
  have hex : ∃ j, 0 < q j := by
    by_contra h
    have hz : ∀ j, q j = 0 := fun j => le_antisymm
      (le_of_not_gt fun hj => h ⟨j, hj⟩) (hq.1 j)
    have hs := hq.2
    simp only [hz, Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, fun i => ?_⟩
  have hs : (∑ k, B i k * q k) = p i := congrFun hmix i
  obtain hp0 | hp1 := hp i
  · have hle : B i j * q j ≤ ∑ k, B i k * q k :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hB i k).1 (hq.1 k)) (Finset.mem_univ j)
    rw [hs, hp0] at hle
    have hz : B i j = 0 := by
      by_contra hz
      have hpos := mul_pos (lt_of_le_of_ne (hB i j).1 (Ne.symm hz)) hj
      linarith
    exact hz.trans hp0.symm
  · have hs' : (∑ k, (1 - B i k) * q k) = 0 := by
      simp_rw [sub_mul, one_mul]
      rw [Finset.sum_sub_distrib, hq.2, hs, hp1]
      ring
    have hle : (1 - B i j) * q j ≤ ∑ k, (1 - B i k) * q k :=
      Finset.single_le_sum (fun k _ => mul_nonneg (sub_nonneg.mpr (hB i k).2) (hq.1 k)) (Finset.mem_univ j)
    rw [hs'] at hle
    have ho : B i j = 1 := by
      by_contra ho
      have hpos := mul_pos (sub_pos.mpr (lt_of_le_of_ne (hB i j).2 ho)) hj
      linarith
    exact ho.trans hp1.symm

end MeraConstraints.Polytope
