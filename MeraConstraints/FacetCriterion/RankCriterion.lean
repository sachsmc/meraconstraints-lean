import MeraConstraints.FacetCriterion.Span

/-!
# The facet criterion from dimensions

This is the geometric part of Step 4 of the proof of Proposition 4
(`prop:nontrivial`), the proof of part (ii). The hypotheses are those of the
manuscript: the rows of `H_e` define the affine hull of the district polytope
(`hhull`), and each inequality defines a different facet, whose affine span has
dimension one less than the affine hull (`hdim`, `hdistinct`). From these, the
span property of `FacetSpan` and the strictness of the other inequalities at a
facet are derived.

The conclusion concerns the nonnegative points of the affine hull.
`CompactDistrict.FacetCriterion` identifies them with the cross-product of
probability simplices in the affine hull. `CompactDistrict.FacetWitness` produces
the observed distribution that violates a nontrivial inequality.
-/

namespace MeraConstraints.FacetCriterion

open EqualityConstraints Geometry

variable {Row Col E I : Type*}
  [Fintype Row] [Fintype Col] [Nonempty Col] [Fintype E] [Fintype I]

/-- The inequality of `f` holds at every nonnegative point of the affine hull
exactly when some entry `p_k` is zero at every column of `B` on its facet. The
facet span and the strictness of the other inequalities are derived from the
dimension hypotheses. -/
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
