import MeraConstraints.FacetCriterion.RankCriterion

/-!
# The exact incidence-matrix test

The final paragraph following Proposition `prop:nontrivial` uses the matrix
product `I Bᵀ`. Here `I` records exact zero slack, so a row of the product
adds all columns incident to that facet. For a nonnegative compatibility
matrix, an entry is zero precisely when that coordinate vanishes at every
incident column. Thus the geometric criterion is an exact finite matrix
test, including repeated compatibility columns. No numerical tolerance is
part of this definition.
-/

namespace MeraConstraints.FacetCriterion

open Geometry

variable {Row Col I : Type*} [Fintype Row] [Fintype Col]

/-- Exact facet-column incidence, with real zero/one entries. -/
noncomputable def incidence (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) : Matrix I Col ℝ := by
  classical
  exact fun f j => if slack (h f) (c f) (fun i => B i j) = 0 then 1 else 0

/-- One entry of `I Bᵀ` is the unnormalized incident-column sum. -/
theorem incidence_product_eq_sum (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) (f : I) (k : Row) :
    (incidence B h c * B.transpose) f k =
      ∑ j ∈ incidentIndices B (h f) (c f), B k j := by
  classical
  simp [Matrix.mul_apply, incidence, incidentIndices, Finset.sum_filter, ite_mul]

/-- A zero entry of the product is exactly a common zero coordinate on the
incident columns; this is the triviality side of the incidence test. -/
theorem incidence_product_zero_iff (B : Matrix Row Col ℝ) (h : I → Row → ℝ)
    (c : I → ℝ) (hnonneg : ∀ i j, 0 ≤ B i j) (f : I) (k : Row) :
    (incidence B h c * B.transpose) f k = 0 ↔
      ∀ j, slack (h f) (c f) (fun i => B i j) = 0 → B k j = 0 := by
  classical
  rw [incidence_product_eq_sum,
    Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg k j)]
  simp only [mem_incidentIndices]

/-- Every entry of the incidence product is positive precisely when no
coordinate is identically zero on the incident columns. -/
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
