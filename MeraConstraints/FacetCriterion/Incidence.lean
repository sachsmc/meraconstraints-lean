import MeraConstraints.FacetCriterion.RankCriterion

/-!
# The incidence matrix test

The test following Proposition 4 (`prop:nontrivial`) uses the product `I Bᵀ`. The
0/1 matrix `I` has entry one when the column of `B` lies on the facet, that is,
when its slack is zero. A row of `I Bᵀ` is therefore the sum of the columns of `B`
on that facet. Since `B` is nonnegative, an entry of the row is zero exactly when
that entry of `B` is zero at every column on the facet. So an inequality is
nontrivial exactly when every entry of its row of `I Bᵀ` is positive.
-/

namespace MeraConstraints.FacetCriterion

open Geometry

variable {Row Col I : Type*} [Fintype Row] [Fintype Col]

/-- The matrix `I`: the entry for an inequality `f` and a column `j` of `B` is `1`
if the column lies on the facet of `f`, and `0` otherwise. -/
noncomputable def incidence (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) : Matrix I Col ℝ := by
  classical
  exact fun f j => if slack (h f) (c f) (fun i => B i j) = 0 then 1 else 0

/-- An entry of `I Bᵀ` is the sum of that entry of `B` over the columns on the
facet. -/
theorem incidence_product_eq_sum (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) (f : I) (k : Row) :
    (incidence B h c * B.transpose) f k =
      ∑ j ∈ incidentIndices B (h f) (c f), B k j := by
  classical
  simp [Matrix.mul_apply, incidence, incidentIndices, Finset.sum_filter, ite_mul]

/-- An entry of `I Bᵀ` is zero exactly when that entry of `B` is zero at every
column on the facet. -/
theorem incidence_product_zero_iff (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) (hnonneg : ∀ i j, 0 ≤ B i j) (f : I) (k : Row) :
    (incidence B h c * B.transpose) f k = 0 ↔
      ∀ j, slack (h f) (c f) (fun i => B i j) = 0 → B k j = 0 := by
  classical
  rw [incidence_product_eq_sum,
    Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg k j)]
  simp only [mem_incidentIndices]

/-- Every entry of a row of `I Bᵀ` is positive exactly when no entry of `B` is zero
at every column on the facet. -/
theorem incidence_product_pos_iff (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) (hnonneg : ∀ i j, 0 ≤ B i j) (f : I) :
    (∀ k, 0 < (incidence B h c * B.transpose) f k) ↔
      ¬ ∃ k, ∀ j, slack (h f) (c f) (fun i => B i j) = 0 → B k j = 0 := by
  classical
  constructor
  · rintro hp ⟨k, hk⟩
    have hz := (incidence_product_zero_iff B h c hnonneg f k).mpr hk
    exact (ne_of_gt (hp k)) hz
  · intro hn k
    have hne : (incidence B h c * B.transpose) f k ≠ 0 := by
      intro hz
      exact hn ⟨k, (incidence_product_zero_iff B h c hnonneg f k).mp hz⟩
    have hge : 0 ≤ (incidence B h c * B.transpose) f k := by
      rw [incidence_product_eq_sum]
      exact Finset.sum_nonneg fun j _ => hnonneg k j
    exact lt_of_le_of_ne hge (Ne.symm hne)

end MeraConstraints.FacetCriterion
