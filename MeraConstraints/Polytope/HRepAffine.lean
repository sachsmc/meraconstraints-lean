import MeraConstraints.FacetCriterion

/-!
# An affine, incompatible point forces a nontrivial H-row

Appendix `prop:ineqstructure`, Step 2. Every equality of a checked exact
H-representation holds on the whole affine hull of the mixture polytope.
An affine-hull point outside the polytope must therefore violate an inequality
row. If the point also belongs to a proposed basic probability domain, that
row cannot be valid on the basic domain intersected with the equalities.

Exact H-representation is checked input data. No facet enumeration, incidence
rank, or completeness of the equality rows as affine-hull equations is needed
for this implication.
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

/-- A witnessed violation inside the basic domain and equality set proves
nontriviality, rather than merely identifying a valid inequality row. -/
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
