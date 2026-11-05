import MeraConstraints.Polytope

/-!
# A 0/1 point of the polytope is a column

If all entries of `B` lie in `[0, 1]` and a 0/1 vector `p` lies in the district
polytope, then `p` is a column of `B`. Write `p = B r`. Some weight `r_j` is
positive because the weights sum to one. Fix `j` with `r_j > 0`. Where `p_i = 0`
the terms `B i k r_k` are nonnegative and sum to zero, so `B i j = 0`; where
`p_i = 1` the same argument applies to `1 - B i k`.

This is the fact used in type (i) of Step 3 of the proof of Remark 3
(`prop:ineqstructure`), that a 0/1 vector in the district polytope is a column of
`B`. Columns of `B` may repeat.
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
