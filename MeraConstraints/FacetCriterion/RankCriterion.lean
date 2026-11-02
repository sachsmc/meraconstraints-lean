import MeraConstraints.FacetCriterion.Span

/-!
# Facet incidence criterion from direction ranks

This assembles the geometric part of Proposition `prop:nontrivial` (ii).
The hypotheses describe the columns, their affine hull and a finite list of
distinct proper facets through codimension-one direction ranks. Neither the
coordinate certificate nor the separation of the other facet planes is an
input: both are derived from these geometric data.

The conclusion concerns the nonnegative part of the affine hull. Its
interpretation as graph-triviality still needs the manuscript's separate
positive-kernel realization and ordering argument.
-/

namespace MeraConstraints.FacetCriterion

open EqualityConstraints Geometry

variable {Row Col E I : Type*}
  [Fintype Row] [Fintype Col] [Nonempty Col] [Fintype E] [Fintype I]

/-- A proper facet is implied by coordinate nonnegativity and the affine
hull precisely when its incident columns share a zero coordinate. All
facet-span and other-facet separation hypotheses are derived from ranks. -/
theorem coordinate_trivial_iff_incident_zero_of_ranks
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : I → Row → ℝ) (c : I → ℝ) (f : I)
    (hhull : ∀ p, p ∈ columnHull B ↔ Feasible A b p)
    (hnonneg : ∀ i j, 0 ≤ B i j) (hcover : ∀ i, ∃ j, 0 < B i j)
    (hvalid : ∀ g j, 0 ≤ slack (h g) (c g) (fun i => B i j))
    (hproper : ∀ g, ∃ j, 0 < slack (h g) (c g) (fun i => B i j))
    (hincident : ∀ g, (incidentColumns B (h g) (c g)).Nonempty)
    (hdim : ∀ g, Module.finrank ℝ (columnHull B).direction =
      Module.finrank ℝ (incidentHull B (h g) (c g)).direction + 1)
    (hdistinct : ∀ g, g ≠ f →
      incidentHull B (h f) (c f) ≠ incidentHull B (h g) (c g)) :
    CoordinateTrivial A b (h f) (c f) ↔
      ∃ k, ∀ j, slack (h f) (c f) (fun i => B i j) = 0 → B k j = 0 := by
  classical
  have hspan := facetSpan_of_codimension_one B A b (h f) (c f)
    hhull (hincident f) (hproper f) (hdim f)
  have he : ∀ j, Feasible A b (fun i => B i j) := fun j =>
    (hhull _).mp (mem_affineSpan ℝ ⟨j, rfl⟩)
  have htight : (incidentIndices B (h f) (c f)).Nonempty := by
    obtain ⟨_, j, hj, rfl⟩ := hincident f
    exact ⟨j, (mem_incidentIndices _ _ _ _).mpr hj⟩
  have hsep : ∀ g, g ≠ f → ∃ p, Feasible A b p ∧
      slack (h f) (c f) p = 0 ∧ slack (h g) (c g) p ≠ 0 := by
    intro g hg
    obtain ⟨j, hjf, hjg⟩ := strict_incident_column_of_distinct_facets B A b
      (h f) (h g) (c f) (c g) hhull (hincident f) (hincident g)
      (hproper g) (hvalid g) (hdim f) (hdim g) (hdistinct g hg)
    exact ⟨_, he j, hjf, ne_of_gt hjg⟩
  exact coordinate_trivial_iff_incident_zero B A b h c f hspan hnonneg hcover he
    hvalid (hproper f) htight hsep

end MeraConstraints.FacetCriterion
