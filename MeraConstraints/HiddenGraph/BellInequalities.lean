import MeraConstraints.HiddenGraph.BellStructure
import MeraConstraints.CompactDistrict.LevelChoices
import MeraConstraints.CompactDistrict.BellNonmembership
import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.Polytope.HRepAffine

/-!
# Bell structure forces a nontrivial district H-inequality

This assembles manuscript `prop:ineqstructure` (ii) for the actual partition
`observedDistrict G`. The stated cardinality assumptions supply two distinct
levels at every member and at both external sources. Other coordinates need
only be nonempty to extend the reference assignments. The previously checked
lifted PR box is then a normalized affine-hull point outside the actual
district mixture polytope.

Appendix Step 2 applies to any checked exact H-representation: the target
satisfies all H-equalities and violates an H-inequality. It witnesses failure
of the existing `KernelTrivial` predicate on normalized blocks satisfying
those equalities. This row-existence conclusion needs neither separate
affine-hull exactness nor facet geometry nor c-degree one. The positive
global observed-law consequence uses the general facet theorem separately.
-/

namespace MeraConstraints.HiddenGraph

open CompactDistrict EqualityConstraints

variable {n ℓ : ℕ} (G : Graph n ℓ) (d : DistrictId G)
  [DecidableEq (DistrictId G)] (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => CompactDistrict.Row G.observed val (observedDistrict G) d
local notation "C" => CompactDistrict.matrix G.observed val (observedDistrict G) d

/-- The lifted Bell witness with reference levels derived from cardinalities;
no supplied binary encoding or assumed separating inequality is required. -/
theorem bell_affine_witness_of_two_levels (hstructure : BellStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ t : Rows → ℝ, KernelSimplex G val d t ∧
      t ∈ affineSpan ℝ (Polytope.mixture C) ∧ t ∉ Polytope.mixture C := by
  obtain ⟨wA, wB, a, b, ⟨P⟩⟩ := hstructure
  obtain ⟨v0, v1, h⟩ := exists_reference_levels G.observed val (observedDistrict G) d hlevels
  exact ⟨P.bellTarget v0 v1, P.bell_affine_witness v0 v1
    (fun i => h i.val (Or.inl i.property))
    (h wA.val (Or.inr wA.property)) (h wB.val (Or.inr wB.property))⟩

theorem bell_nontrivial_H_witness {I E : Type*} (H : Polytope.HRep C I E)
    (hstructure : BellStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ t : Rows → ℝ, KernelSimplex G val d t ∧ Feasible H.equalities H.target t ∧
      ∃ f : I, H.upper f < score (H.inequalities f) t ∧
        ¬ KernelTrivial G val d H.equalities H.target (H.inequalities f) (H.upper f) := by
  obtain ⟨t, ht, haff, hnot⟩ := bell_affine_witness_of_two_levels G d val hstructure hlevels
  obtain ⟨f, hv, hn⟩ := H.exists_nontrivial_on (KernelSimplex G val d) t ht haff hnot
  exact ⟨t, ht, H.equalities_on_affineSpan t haff, f, hv, hn⟩

/-- Remark `prop:ineqstructure` (ii): a nontrivial inequality of any checked
exact H-system for the actual hidden-graph district. -/
theorem bell_nontrivial_H_row {I E : Type*} (H : Polytope.HRep C I E)
    (hstructure : BellStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ f : I, ¬ KernelTrivial G val d H.equalities H.target (H.inequalities f) (H.upper f) := by
  obtain ⟨_, _, _, f, _, hf⟩ := bell_nontrivial_H_witness G d val H hstructure hlevels
  exact ⟨f, hf⟩

end MeraConstraints.HiddenGraph
