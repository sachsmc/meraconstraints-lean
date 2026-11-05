import MeraConstraints.Examples.InstrumentalFacetData

/-!
# The twelve printed inequalities define distinct facets

Each row of `H_i` defines a face of the district polytope, the columns of
`printedB` with zero slack. Using the tables of `InstrumentalFacetData` and the
six-dimensional hull of `InstrumentalHull`, this chapter shows, for every row:

- The six selected columns on the face are linearly, hence affinely,
  independent, so the affine hull of the face has dimension at least five.
- A column with positive slack lies off the face, so the hull of the face is a
  proper affine subspace of the six-dimensional hull. Its dimension is at most
  five.

So each face has dimension five, one less than the polytope: it is a facet
(`printed_facets_codimension_one`). For two different rows, a column lies on the
face of the first and off the face of the second, so the facets are different
(`printed_facets_distinct`). Finally `printed_facetSpan` shows that the affine
hull of each face is the set of vectors satisfying the two normalization
equations and the equation of the row.

These are the hypotheses of Proposition 4 (`prop:nontrivial`) that each row of
`H_i` defines a different facet, for the instrumental variable district. The
classification of the rows is in `InstrumentalClassification`.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

open EqualityConstraints Geometry MeraConstraints.FacetCriterion

theorem printed_facet_valid (f : Fin 12) (j : Fin 16) :
    0 ≤ slack (printedHi f) (printedUpper f) (fun i => printedB i j) := by
  have h := printedB_inequalities f j
  change 0 ≤ printedUpper f - ∑ i, printedHi f i * printedB i j
  linarith only [h]

theorem printed_facet_selected_tight (f : Fin 12) (j : Fin 6) :
    slack (printedHi f) (printedUpper f) (fun i => printedB i (facetColumn f j)) = 0 := by
  rw [← facetIntegerSlack_cast]
  exact_mod_cast facet_selected_integer_tight f j

theorem printed_facet_proper (f : Fin 12) :
    0 < slack (printedHi f) (printedUpper f) (fun i => printedB i (facetProperColumn f)) := by
  rw [← facetIntegerSlack_cast]
  exact_mod_cast facet_proper_integer_positive f

theorem printed_facet_incident_nonempty (f : Fin 12) :
    (incidentColumns printedB (printedHi f) (printedUpper f)).Nonempty :=
  ⟨_, facetColumn f 0, printed_facet_selected_tight f 0, rfl⟩

theorem printed_facet_separation (f g : Fin 12) (hfg : f ≠ g) :
    slack (printedHi f) (printedUpper f) (fun i => printedB i (facetSeparatingColumn f g)) = 0 ∧
      0 < slack (printedHi g) (printedUpper g) (fun i => printedB i (facetSeparatingColumn f g)) := by
  rw [← facetIntegerSlack_cast, ← facetIntegerSlack_cast]
  exact_mod_cast facet_separation_integer f g hfg

theorem facetColumn_linearIndependent (f : Fin 12) :
    LinearIndependent ℝ (fun j : Fin 6 => fun i : Fin 8 => printedB i (facetColumn f j)) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  have hlin (w : Fin 6 → ℝ) :
      Fintype.linearCombination ℝ (fun j : Fin 6 => fun i : Fin 8 => printedB i (facetColumn f j)) w =
        (facetColumnMatrix f).mulVec w := by
    funext i
    simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, facetColumnMatrix]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  intro w v h
  rw [hlin w, hlin v] at h
  have hh := congrArg (facetReaderMatrix f).mulVec h
  simpa only [Matrix.mulVec_mulVec, facet_reader_mul_columns, Matrix.one_mulVec] using hh

/-- The affine span of the six selected columns on the face has dimension five. -/
theorem printed_facet_selected_finrank (f : Fin 12) :
    Module.finrank ℝ (vectorSpan ℝ
      (Set.range fun j : Fin 6 => fun i : Fin 8 => printedB i (facetColumn f j))) = 5 :=
  (facetColumn_linearIndependent f).affineIndependent.finrank_vectorSpan (by decide)

theorem printed_facetHull_lt (f : Fin 12) :
    incidentHull printedB (printedHi f) (printedUpper f) < columnHull printedB := by
  apply lt_of_le_of_ne (incidentHull_le_columnHull printedB (printedHi f) (printedUpper f))
  intro heq
  have hcol : (fun i => printedB i (facetProperColumn f)) ∈ columnHull printedB :=
    mem_affineSpan ℝ ⟨facetProperColumn f, rfl⟩
  rw [← heq] at hcol
  have hplane := incidentHull_le_equationPlane printedB (printedHi f) (printedUpper f) hcol
  change score (printedHi f) (fun i => printedB i (facetProperColumn f)) = printedUpper f at hplane
  have hpos := printed_facet_proper f
  change 0 < printedUpper f - score (printedHi f) (fun i => printedB i (facetProperColumn f)) at hpos
  linarith

/-- The affine hull of the columns on the face of each row of `H_i` has
dimension five. -/
theorem printed_facetHull_finrank (f : Fin 12) :
    Module.finrank ℝ (incidentHull printedB (printedHi f) (printedUpper f)).direction = 5 := by
  have hle :
      affineSpan ℝ (Set.range fun j : Fin 6 => fun i : Fin 8 => printedB i (facetColumn f j)) ≤
        incidentHull printedB (printedHi f) (printedUpper f) := by
    apply affineSpan_le.mpr
    rintro _ ⟨j, rfl⟩
    exact mem_affineSpan ℝ ⟨facetColumn f j, printed_facet_selected_tight f j, rfl⟩
  have hlower := Submodule.finrank_mono (AffineSubspace.direction_le hle)
  rw [direction_affineSpan, printed_facet_selected_finrank] at hlower
  have hne : (incidentHull printedB (printedHi f) (printedUpper f) : Set (Fin 8 → ℝ)).Nonempty := by
    obtain ⟨x, hx⟩ := printed_facet_incident_nonempty f
    exact ⟨x, mem_affineSpan ℝ hx⟩
  have hupper := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty (printed_facetHull_lt f) hne)
  rw [printed_columnHull_finrank] at hupper
  omega

theorem printed_facets_codimension_one (f : Fin 12) :
    Module.finrank ℝ (columnHull printedB).direction =
      Module.finrank ℝ (incidentHull printedB (printedHi f) (printedUpper f)).direction + 1 := by
  rw [printed_columnHull_finrank, printed_facetHull_finrank]

theorem printed_facets_distinct (f g : Fin 12) (hfg : f ≠ g) :
    incidentHull printedB (printedHi f) (printedUpper f) ≠
      incidentHull printedB (printedHi g) (printedUpper g) := by
  intro heq
  obtain ⟨hzero, hpos⟩ := printed_facet_separation f g hfg
  have hcol : (fun i => printedB i (facetSeparatingColumn f g)) ∈
      incidentHull printedB (printedHi f) (printedUpper f) :=
    mem_affineSpan ℝ ⟨facetSeparatingColumn f g, hzero, rfl⟩
  rw [heq] at hcol
  have hplane := incidentHull_le_equationPlane printedB (printedHi g) (printedUpper g) hcol
  change score (printedHi g) (fun i => printedB i (facetSeparatingColumn f g)) = printedUpper g at hplane
  change 0 < printedUpper g - score (printedHi g) (fun i => printedB i (facetSeparatingColumn f g)) at hpos
  linarith

/-- For each row of `H_i`, the affine hull of the columns on its face is the set
of vectors with `H_e p = b_e` and zero slack in the row. -/
theorem printed_facetSpan (f : Fin 12) : FacetSpan printedB printedHe printedTarget (printedHi f) (printedUpper f) :=
  facetSpan_of_codimension_one printedB printedHe printedTarget (printedHi f) (printedUpper f)
    printed_columnHull_iff (printed_facet_incident_nonempty f)
    ⟨facetProperColumn f, printed_facet_proper f⟩ (printed_facets_codimension_one f)

end MeraConstraints.Examples.Instrumental.Appendix
