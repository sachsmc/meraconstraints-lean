import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.FacetCriterion.Incidence

/-!
# Exact matrix test for nontrivial district inequalities

This is the `I Bᵀ` formulation following Proposition `prop:nontrivial`.
It applies to the actual compact district compatibility matrix, and uses
the paper's definition of inequality triviality on the cross-product of
probability simplices satisfying the affine-hull equations.

Facet validity, properness, distinctness and codimension-one incidence
ranks are explicit checked inputs. A numerical H-conversion output must
still provide these certificates before this theorem applies to its rows.
-/

namespace MeraConstraints.CompactDistrict

open EqualityConstraints Geometry

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)] (d : HiddenGraph.DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (HiddenGraph.observedDistrict G) d
local notation "C" => matrix G.observed val (HiddenGraph.observedDistrict G) d

/-- A row defines a nontrivial district inequality exactly when every entry
of its row in the exact incidence product is strictly positive. -/
theorem kernel_nontrivial_iff_incidence_product_pos {E I : Type*} [Fintype E] [Fintype I]
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
    (¬ KernelTrivial G val d A b (h f) (c f)) ↔
      ∀ x : Rows, 0 < (MeraConstraints.FacetCriterion.incidence C h c * C.transpose) f x := by
  rw [kernel_trivial_iff_incident_zero G val d A b h c f
    hhull hvalid hproper hincident hdim hdistinct]
  exact (MeraConstraints.FacetCriterion.incidence_product_pos_iff C h c
    (compatibility_nonneg G val d) f).symm

end MeraConstraints.CompactDistrict
