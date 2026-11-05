import MeraConstraints.Examples.InstrumentalHRep

/-!
# The printed H-representation in the `(Z, X, Y)` row order

`InstrumentalHRep` shows that the printed H-representation describes the polytope
of `printedB`, whose rows are in the printed order `(X, Y, Z)`. This chapter
carries the result over to `Instrumental.matrix`, whose rows are `(Z, X, Y)` and
whose columns are all sixteen pairs of response functions `(X(Z), Y(X))`, using
`rowEquiv` and `profileEquiv`.

A vector `p` indexed by `(Z, X, Y)` lies in the district polytope of
`Instrumental.matrix` if and only if its reindexed copy satisfies the twelve
printed inequalities and two normalizations
(`instrumental_mixture_iff_printed_feasible`). `semanticHRep` is this
H-representation as a `Polytope.HRep`; it differs from `printedHRep` only in the
order of the coordinates of `p`. Vectors with zero entries are included.
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

/-- The printed H-representation with its coordinates reordered to the row type
`(Z, X, Y)` of `Instrumental.matrix`. -/
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
