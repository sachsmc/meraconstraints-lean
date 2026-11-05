import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.FacetCriterion.Incidence

/-!
# The incidence test for nontrivial inequalities

This chapter proves the test stated after Proposition 4 (`prop:nontrivial`). Let `I`
be the 0/1 matrix with `I_{rβ} = 1` when column `β` of the matrix `B` lies on the
facet defined by row `r` of `H_i`. Then row `r` is nontrivial if and only if every
entry of row `r` of `I Bᵀ` is positive.

The test follows from Proposition 4 (ii), first claim: entry `k` of row `r` of
`I Bᵀ` counts the columns on the facet of `r` at which `p_k` is nonzero. The hypotheses
are those of Proposition 4: the rows of `H_e` define the affine hull and each row of
`H_i` defines a different facet.
-/

namespace MeraConstraints.CompactDistrict

open EqualityConstraints Geometry

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)] (d : HiddenGraph.DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (HiddenGraph.observedDistrict G) d
local notation "C" => matrix G.observed val (HiddenGraph.observedDistrict G) d

/-- The inequality of row `f` is nontrivial if and only if every entry of row `f`
of `I Bᵀ` is positive. -/
theorem inequality_nontrivial_iff_incidence_product_pos {E I : Type*} [Fintype E] [Fintype I]
    (A : Matrix E Rows ℝ) (b : E → ℝ) (h : I → Rows → ℝ) (c : I → ℝ) (f : I)
    (hhull : ∀ p, p ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b p)
    (hvalid : ∀ g r, 0 ≤ slack (h g) (c g) (fun x => C x r))
    (hproper : ∀ g, ∃ r, 0 < slack (h g) (c g) (fun x => C x r))
    (hincident : ∀ g, (MeraConstraints.FacetCriterion.incidentColumns C (h g) (c g)).Nonempty)
    (hdim : ∀ g, Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull C).direction =
      Module.finrank ℝ (MeraConstraints.FacetCriterion.incidentHull C (h g) (c g)).direction + 1)
    (hdistinct : ∀ g, g ≠ f →
      MeraConstraints.FacetCriterion.incidentHull C (h f) (c f) ≠
        MeraConstraints.FacetCriterion.incidentHull C (h g) (c g)) :
    (¬ InequalityTrivial G val d A b (h f) (c f)) ↔
      ∀ x : Rows, 0 < (MeraConstraints.FacetCriterion.incidence C h c * Matrix.transpose C) f x := by
  rw [inequalityTrivial_iff_incident_zero G val d A b h c f
    hhull hvalid hproper hincident hdim hdistinct]
  exact (MeraConstraints.FacetCriterion.incidence_product_pos_iff C h c
    (compatibility_nonneg G val d) f).symm

end MeraConstraints.CompactDistrict
