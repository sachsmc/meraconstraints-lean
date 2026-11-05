import MeraConstraints.FacetCriterion

/-!
# A point of the affine hull outside the polytope violates an inequality

This is Step 2 of the proof of Remark 3 (`prop:ineqstructure`). Every equation of
an H-representation holds on the affine hull of the district polytope. So a point
of the affine hull that is not in the polytope violates some inequality of `H_i`.
If the point also lies in a given set `Q` (for the manuscript, the cross-product
of probability simplices), that inequality is not valid on the points of `Q` that
satisfy the equations, so it is nontrivial.

Nothing is assumed about facets or about the rows of `H_e` defining the affine
hull.
-/

namespace MeraConstraints.Polytope.HRep

open EqualityConstraints Geometry

variable {Row Col I E : Type*} [Fintype Row] [Fintype Col]
  {B : Matrix Row Col ℝ} (H : Polytope.HRep B I E)

theorem equalities_on_affineSpan (p : Row → ℝ) (hp : p ∈ affineSpan ℝ (Polytope.mixture B)) :
    Feasible H.equalities H.target p := by
  intro e
  exact MeraConstraints.FacetCriterion.equation_on_affineSpan (Polytope.mixture B)
    (H.equalities e) (H.target e) (fun q hq => ((H.exact_representation q).mp hq).2 e) hp

theorem exists_violated_inequality (p : Row → ℝ)
    (hp : p ∈ affineSpan ℝ (Polytope.mixture B)) (hnot : p ∉ Polytope.mixture B) :
    ∃ i, H.upper i < score (H.inequalities i) p := by
  classical
  by_contra hn
  have hi : ∀ i, score (H.inequalities i) p ≤ H.upper i :=
    fun i => le_of_not_gt fun h => hn ⟨i, h⟩
  exact hnot ((H.exact_representation p).mpr ⟨hi, H.equalities_on_affineSpan p hp⟩)

/-- If `p` is in `Q` and in the affine hull but not in the polytope, then some
inequality of `H_i` is violated at `p` and is not valid on the points of `Q` that
satisfy the equations. -/
theorem exists_nontrivial_on (Q : (Row → ℝ) → Prop) (p : Row → ℝ) (hQ : Q p)
    (hp : p ∈ affineSpan ℝ (Polytope.mixture B)) (hnot : p ∉ Polytope.mixture B) :
    ∃ i, H.upper i < score (H.inequalities i) p ∧
      ¬ ∀ q, Q q → Feasible H.equalities H.target q → 0 ≤ slack (H.inequalities i) (H.upper i) q := by
  obtain ⟨i, hi⟩ := H.exists_violated_inequality p hp hnot
  refine ⟨i, hi, ?_⟩
  intro ht
  have hs := ht p hQ (H.equalities_on_affineSpan p hp)
  change 0 ≤ H.upper i - score (H.inequalities i) p at hs
  linarith

end MeraConstraints.Polytope.HRep
