import MeraConstraints.Examples.Instrumental
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# The printed matrix and H-representation for the instrumental variable district

This chapter transcribes the matrix `B` and the H-representation `H_i`, `b_i`,
`H_e`, `b_e` printed in the instrumental variable details in the Supplementary
Materials (`appendix:iv`). Its eight probability coordinates are in the printed
order `(X, Y, Z)`, with `X` changing fastest, then `Y`, then `Z`. The row type of
`Instrumental.matrix` is `(Z, X, Y)`, and `rowEquiv` is the change of
coordinates. `profileEquiv` lists all sixteen profiles in the printed column
order, including profiles whose columns repeat. `printedB_eq_matrix` shows that
each entry of the printed matrix equals the corresponding entry of
`Instrumental.matrix`.

The chapter shows that every column of `printedB` satisfies every printed
inequality and equality. Hence so does every mixture of the columns, and, after
the change of coordinates, every point of the district polytope of
`Instrumental.matrix` (`instrumental_mixture_printed_feasible`). This is one
direction of the statement that the printed H-representation describes the
polytope. The other direction is in `InstrumentalHRep`, and `InstrumentalExact`
combines the two.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

def rowIndex : Fin 8 → Instrumental.Row :=
  ![(false, false, false), (false, true, false), (false, false, true), (false, true, true),
    (true, false, false), (true, true, false), (true, false, true), (true, true, true)]

noncomputable def rowEquiv : Fin 8 ≃ Instrumental.Row := Equiv.ofBijective rowIndex (by decide)

def response (b0 b1 : Bool) : Bool → Bool := fun b => if b then b1 else b0

/-- Each entry gives the response functions of one printed column, listed as
`(X(0), X(1))` and `(Y(0), Y(1))`. -/
def profileIndex : Fin 16 → Instrumental.Profile :=
  ![(response false false, response false false),
    (response false true,  response false false),
    (response false false, response false true),
    (response false true,  response false true),
    (response true false,  response false false),
    (response true true,   response false false),
    (response true false,  response true false),
    (response true true,   response true false),
    (response false false, response true false),
    (response false true,  response true false),
    (response false false, response true true),
    (response false true,  response true true),
    (response true false,  response false true),
    (response true true,   response false true),
    (response true false,  response true true),
    (response true true,   response true true)]

noncomputable def profileEquiv : Fin 16 ≃ Instrumental.Profile := Equiv.ofBijective profileIndex (by decide)

def printedB : Matrix (Fin 8) (Fin 16) ℝ :=
  !![1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0;
     0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0;
     0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1;
     1,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0;
     0,1,0,0,0,1,0,1,0,1,0,0,0,0,0,0;
     0,0,0,0,0,0,1,0,1,0,1,0,0,0,1,0;
     0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,1]

theorem printedB_eq_matrix (i : Fin 8) (j : Fin 16) :
    printedB i j = Instrumental.matrix (rowEquiv i) (profileEquiv j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [printedB, Instrumental.matrix, Instrumental.column, rowEquiv, rowIndex,
      profileEquiv, profileIndex, response]

def printedHi : Matrix (Fin 12) (Fin 8) ℝ :=
  !![0,0,0,0,-1,0,0,0;
     -1,-1,-1,0,0,1,0,0;
     0,1,0,0,-1,-1,-1,0;
     -1,0,0,0,0,0,0,0;
     0,0,1,0,1,0,0,0;
     1,0,0,0,0,0,1,0;
     0,0,0,0,0,-1,0,0;
     0,0,0,0,1,1,1,0;
     0,-1,0,0,0,0,0,0;
     1,1,1,0,0,0,0,0;
     0,0,0,0,0,0,-1,0;
     0,0,-1,0,0,0,0,0]

def printedUpper : Fin 12 → ℝ := ![0,0,0,0,1,1,0,1,0,1,0,0]

def printedHe : Matrix (Fin 2) (Fin 8) ℝ :=
  !![-1,-1,-1,-1,0,0,0,0; 0,0,0,0,-1,-1,-1,-1]

def printedTarget : Fin 2 → ℝ := ![-1,-1]

def PrintedFeasible (p : Fin 8 → ℝ) : Prop :=
  (∀ f, ∑ i, printedHi f i * p i ≤ printedUpper f) ∧
    (∀ e, ∑ i, printedHe e i * p i = printedTarget e)

set_option maxHeartbeats 2000000 in
/-- Every column of `printedB` satisfies each of the twelve inequalities. -/
theorem printedB_inequalities (f : Fin 12) (j : Fin 16) :
    (∑ i, printedHi f i * printedB i j) ≤ printedUpper f := by
  fin_cases f <;> fin_cases j <;>
    norm_num [printedHi, printedUpper, printedB, Fin.sum_univ_succ]

/-- Every column of `printedB` satisfies the two equalities: its entries for
`Z = 0` sum to one, and so do its entries for `Z = 1`. -/
theorem printedB_equalities (e : Fin 2) (j : Fin 16) :
    (∑ i, printedHe e i * printedB i j) = printedTarget e := by
  fin_cases e <;> fin_cases j <;>
    norm_num [printedHe, printedTarget, printedB, Fin.sum_univ_succ]

theorem printed_mixture_feasible {p : Fin 8 → ℝ}
    (hp : p ∈ Polytope.mixture printedB) : PrintedFeasible p := by
  constructor
  · intro f
    exact Polytope.inequality_of_columns printedB (printedHi f) (printedUpper f)
      (printedB_inequalities f) hp
  · obtain ⟨q, hq, rfl⟩ := hp
    intro e
    rw [Polytope.score_mulVec]
    simp_rw [printedB_equalities e]
    rw [← Finset.sum_mul, hq.2, one_mul]

/-- Reindexing a probability vector over the profiles by `profileEquiv` gives a
probability vector over the sixteen printed columns. -/
theorem reindex_simplex {q : Instrumental.Profile → ℝ} (hq : q ∈ stdSimplex ℝ Instrumental.Profile) :
    (fun j => q (profileEquiv j)) ∈ stdSimplex ℝ (Fin 16) :=
  ⟨fun j => hq.1 (profileEquiv j), (profileEquiv.sum_comp q).trans hq.2⟩

theorem reindex_mulVec (q : Instrumental.Profile → ℝ) (i : Fin 8) :
    printedB.mulVec (fun j => q (profileEquiv j)) i = Instrumental.matrix.mulVec q (rowEquiv i) := by
  simp only [Matrix.mulVec, dotProduct, printedB_eq_matrix]
  exact profileEquiv.sum_comp (fun r => Instrumental.matrix (rowEquiv i) r * q r)

/-- Every point of the district polytope of `Instrumental.matrix` satisfies the
printed H-representation, after the change of coordinates `rowEquiv`. The
converse is in `InstrumentalExact`. -/
theorem instrumental_mixture_printed_feasible {p : Instrumental.Row → ℝ}
    (hp : p ∈ Polytope.mixture Instrumental.matrix) :
    PrintedFeasible (fun i => p (rowEquiv i)) := by
  obtain ⟨q, hq, rfl⟩ := hp
  apply printed_mixture_feasible
  refine ⟨fun j => q (profileEquiv j), reindex_simplex hq, ?_⟩
  funext i
  exact reindex_mulVec q i

end MeraConstraints.Examples.Instrumental.Appendix
