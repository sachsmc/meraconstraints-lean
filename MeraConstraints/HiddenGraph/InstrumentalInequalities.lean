import MeraConstraints.HiddenGraph.InequalityStructures
import MeraConstraints.CompactDistrict.LevelChoices
import MeraConstraints.CompactDistrict.InstrumentalNonmembership
import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.Polytope.HRepAffine

/-!
# Instrumental structure forces a nontrivial district H-inequality

This assembles the instrumental branch of manuscript `prop:ineqstructure`
for the actual partition `observedDistrict G`. Chosen binary values are
derived from the at-least-two-level assumptions, and all other coordinates
need only be nonempty. The lifted target is a normalized affine-hull point
outside the actual response-profile polytope.

For any checked exact H-representation, the target satisfies every equality
and violates an inequality. It witnesses failure of `KernelTrivial`, the
existing definition on the cross-product of probability simplices satisfying
those equalities. No separate affine-hull exactness or facet geometry is
needed for this row-existence step. C-degree one is used separately for the
manuscript's positive global observed-law realization.
-/

namespace MeraConstraints.HiddenGraph

open CompactDistrict EqualityConstraints

variable {n ℓ : ℕ} (G : Graph n ℓ) (d : DistrictId G)
  [DecidableEq (DistrictId G)] (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => CompactDistrict.Row G.observed val (observedDistrict G) d
local notation "C" => CompactDistrict.matrix G.observed val (observedDistrict G) d

/-- The complete lifted witness, with level choices derived from the actual
district/external-parent cardinalities rather than supplied as encodings. -/
theorem instrumental_affine_witness_of_two_levels (hstructure : InstrumentalStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ t : Rows → ℝ, KernelSimplex G val d t ∧
      t ∈ affineSpan ℝ (Polytope.mixture C) ∧ t ∉ Polytope.mixture C := by
  obtain ⟨w, a, b, ⟨P⟩⟩ := hstructure
  obtain ⟨v0, v1, hm, hw⟩ := exists_instrumental_levels G.observed val (observedDistrict G) d hlevels w
  exact ⟨P.instrumentalTarget v0 v1, P.instrumental_affine_witness v0 v1 hm hw⟩

theorem instrumental_nontrivial_H_witness {I E : Type*} (H : Polytope.HRep C I E)
    (hstructure : InstrumentalStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ t : Rows → ℝ, KernelSimplex G val d t ∧ Feasible H.equalities H.target t ∧
      ∃ f : I, H.upper f < score (H.inequalities f) t ∧
        ¬ KernelTrivial G val d H.equalities H.target (H.inequalities f) (H.upper f) := by
  obtain ⟨t, ht, haff, hnot⟩ := instrumental_affine_witness_of_two_levels G d val hstructure hlevels
  obtain ⟨f, hv, hn⟩ := H.exists_nontrivial_on (KernelSimplex G val d) t ht haff hnot
  exact ⟨t, ht, H.equalities_on_affineSpan t haff, f, hv, hn⟩

/-- Remark `prop:ineqstructure` (i), the nontrivial-inequality conclusion
on an actual hidden-graph district and any checked exact H-system. -/
theorem instrumental_nontrivial_H_row {I E : Type*} (H : Polytope.HRep C I E)
    (hstructure : InstrumentalStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ f : I, ¬ KernelTrivial G val d H.equalities H.target (H.inequalities f) (H.upper f) := by
  obtain ⟨_, _, _, f, _, hf⟩ := instrumental_nontrivial_H_witness G d val H hstructure hlevels
  exact ⟨f, hf⟩

end MeraConstraints.HiddenGraph
