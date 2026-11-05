import MeraConstraints.HiddenGraph.BellStructure
import MeraConstraints.CompactDistrict.LevelChoices
import MeraConstraints.CompactDistrict.BellNonmembership
import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.Polytope.HRepAffine

/-!
# The Bell type gives a nontrivial inequality

This is part (ii), the Bell type, of Remark 3 (`prop:ineqstructure`), for the
districts of a hidden variables DAG. The district has a Bell structure
(`BellStructure`), and its members and external parents each have at least two
levels (`HasTwoLevels`). Two values of each are chosen from this.

Then there is a point `t` in the cross-product of probability simplices, in the
affine hull of the district polytope but outside the polytope itself. It is the
PR box (`bell_affine_witness_of_two_levels`). For any H-representation `H` of the
district polytope, `t` satisfies the equalities of `H` and violates one of its
inequalities, and that inequality is not trivial in the sense of Definition 4
(`bell_nontrivial_H_witness`). So `H` contains a nontrivial inequality
(`bell_nontrivial_H_row`).

The remark is for c-degree 1, where the district polytope is the set of possible
district factors, and these statements should be read in that setting. They have no
c-degree hypothesis because they concern only the matrix `B` and its polytope. They
make no claim about the marginal model at higher c-degree.
-/

namespace MeraConstraints.HiddenGraph

open CompactDistrict EqualityConstraints

variable {n ℓ : ℕ} (G : Graph n ℓ) (d : DistrictId G)
  [DecidableEq (DistrictId G)] (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => CompactDistrict.Row G.observed val (observedDistrict G) d
local notation "C" => CompactDistrict.matrix G.observed val (observedDistrict G) d

/-- A point in the cross-product of probability simplices that is in the affine
hull of the district polytope but not in the polytope. -/
theorem bell_affine_witness_of_two_levels (hstructure : BellStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ t : Rows → ℝ, InSimplexProduct G val d t ∧
      t ∈ affineSpan ℝ (Polytope.mixture C) ∧ t ∉ Polytope.mixture C := by
  obtain ⟨wA, wB, a, b, ⟨P⟩⟩ := hstructure
  obtain ⟨v0, v1, h⟩ := exists_reference_levels G.observed val (observedDistrict G) d hlevels
  exact ⟨P.bellTarget v0 v1, P.bell_affine_witness v0 v1
    (fun i => h i.val (Or.inl i.property))
    (h wA.val (Or.inr wA.property)) (h wB.val (Or.inr wB.property))⟩

theorem bell_nontrivial_H_witness {I E : Type*} (H : Polytope.HRep C I E)
    (hstructure : BellStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ t : Rows → ℝ, InSimplexProduct G val d t ∧ Feasible H.equalities H.target t ∧
      ∃ f : I, H.upper f < score (H.inequalities f) t ∧
        ¬ InequalityTrivial G val d H.equalities H.target (H.inequalities f) (H.upper f) := by
  obtain ⟨t, ht, haff, hnot⟩ := bell_affine_witness_of_two_levels G d val hstructure hlevels
  obtain ⟨f, hv, hn⟩ := H.exists_nontrivial_on (InSimplexProduct G val d) t ht haff hnot
  exact ⟨t, ht, H.equalities_on_affineSpan t haff, f, hv, hn⟩

/-- Remark 3 (`prop:ineqstructure`) (ii): every H-representation of the district
polytope contains a nontrivial inequality. -/
theorem bell_nontrivial_H_row {I E : Type*} (H : Polytope.HRep C I E)
    (hstructure : BellStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ f : I, ¬ InequalityTrivial G val d H.equalities H.target (H.inequalities f) (H.upper f) := by
  obtain ⟨_, _, _, f, _, hf⟩ := bell_nontrivial_H_witness G d val H hstructure hlevels
  exact ⟨f, hf⟩

end MeraConstraints.HiddenGraph
