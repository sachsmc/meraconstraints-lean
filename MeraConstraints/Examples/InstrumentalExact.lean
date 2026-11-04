import MeraConstraints.Examples.InstrumentalHRep

/-!
# Exact Appendix B H constraints for the semantic IV profiles

The constructive certificate in `InstrumentalHRep` uses the manuscript's
literal matrix coordinates. Here the previously checked row and profile
equivalences transport its reverse inclusion to the original semantic
matrix, whose rows are (Z,X,Y) and whose columns are all pairs (X(Z),Y(X)).
Both exact H-systems use precisely the twelve printed inequalities and two
normalizations; only the semantic system reindexes the probability columns.
No positive-coordinate or full-support assumption is required.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

theorem instrumental_mixture_iff_printed_feasible (p : Instrumental.Row → ℝ) :
    p ∈ Polytope.mixture Instrumental.matrix ↔ PrintedFeasible (fun i => p (rowEquiv i)) := by
  classical
  constructor
  · exact instrumental_mixture_printed_feasible
  · intro hp
    obtain ⟨q, hq, hqp⟩ := printed_feasible_mixture hp
    let r : Instrumental.Profile → ℝ := fun s => q (profileEquiv.symm s)
    have hr : (fun j => r (profileEquiv j)) = q := by
      funext j
      simp only [r, profileEquiv.symm_apply_apply]
    have hs : r ∈ stdSimplex ℝ Instrumental.Profile := by
      constructor
      · intro s
        exact hq.1 (profileEquiv.symm s)
      · have hsum := profileEquiv.sum_comp r
        rw [hr] at hsum
        exact hsum.symm.trans hq.2
    refine ⟨r, hs, ?_⟩
    funext row
    obtain ⟨i, rfl⟩ := rowEquiv.surjective row
    rw [← reindex_mulVec r i, hr, hqp]

/-- The exact manuscript H-system on the semantic (Z,X,Y) row type. -/
noncomputable def semanticHRep : Polytope.HRep Instrumental.matrix (Fin 12) (Fin 2) where
  inequalities f row := printedHi f (rowEquiv.symm row)
  upper := printedUpper
  equalities e row := printedHe e (rowEquiv.symm row)
  target := printedTarget
  exact_representation p := by
    rw [instrumental_mixture_iff_printed_feasible]
    have hsum (h : Fin 8 → ℝ) :
        (∑ row : Instrumental.Row, h (rowEquiv.symm row) * p row) =
          ∑ i : Fin 8, h i * p (rowEquiv i) := by
      simpa only [rowEquiv.symm_apply_apply] using
        (rowEquiv.sum_comp (fun row => h (rowEquiv.symm row) * p row)).symm
    simp only [PrintedFeasible, hsum]

end MeraConstraints.Examples.Instrumental.Appendix
