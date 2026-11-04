import MeraConstraints.Examples.Instrumental
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Appendix B: literal IV matrix and necessary H constraints

This chapter transcribes `appendix.tex:104--158` and the stored output of
`sources/rscripts/01-iv.R`. The eight probability coordinates are ordered by
(X,Y,Z), with X changing fastest, then Y, then Z. The earlier binary example
instead uses the semantic row type (Z,X,Y). `rowEquiv` checks this coordinate
change. `profileEquiv` enumerates all sixteen actual response profiles in
the printed column order, including the profiles with repeated columns.
`printedB_eq_matrix` verifies every printed entry against structural evaluation.

The H coefficients and right-hand sides below are exactly the manuscript's
ones. The stored rcdd representation uses [equality flag, b, -A], so its
coefficient signs are opposite to the printed H_i and H_e. We check every
inequality and equality on every printed column, then transport these
certificates to arbitrary simplex mixtures and the semantic IV matrix.

This chapter proves the necessity direction of H exactness. The subsequent
`InstrumentalHRep` reconstructs mixtures from feasible H vectors, and
`InstrumentalExact` transports that exact H-system to semantic coordinates.
R and cdd are not trusted proof steps.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

def rowIndex : Fin 8 → Instrumental.Row :=
  ![(false, false, false), (false, true, false), (false, false, true), (false, true, true),
    (true, false, false), (true, true, false), (true, false, true), (true, true, true)]

noncomputable def rowEquiv : Fin 8 ≃ Instrumental.Row := Equiv.ofBijective rowIndex (by decide)

def response (b0 b1 : Bool) : Bool → Bool := fun b => if b then b1 else b0

/-- Each entry lists (X(0),X(1)) and (Y(0),Y(1)) for the printed column. -/
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
/-- All 192 column/inequality incidences are checked in Lean. -/
theorem printedB_inequalities (f : Fin 12) (j : Fin 16) :
    (∑ i, printedHi f i * printedB i j) ≤ printedUpper f := by
  fin_cases f <;> fin_cases j <;>
    norm_num [printedHi, printedUpper, printedB, Fin.sum_univ_succ]

/-- The two printed equalities normalize the separate Z input blocks. -/
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

/-- Reordering all sixteen weights retains every response profile. -/
theorem reindex_simplex {q : Instrumental.Profile → ℝ} (hq : q ∈ stdSimplex ℝ Instrumental.Profile) :
    (fun j => q (profileEquiv j)) ∈ stdSimplex ℝ (Fin 16) :=
  ⟨fun j => hq.1 (profileEquiv j), (profileEquiv.sum_comp q).trans hq.2⟩

theorem reindex_mulVec (q : Instrumental.Profile → ℝ) (i : Fin 8) :
    printedB.mulVec (fun j => q (profileEquiv j)) i = Instrumental.matrix.mulVec q (rowEquiv i) := by
  simp only [Matrix.mulVec, dotProduct, printedB_eq_matrix]
  exact profileEquiv.sum_comp (fun r => Instrumental.matrix (rowEquiv i) r * q r)

/-- The literal printed H rows hold for every semantic binary IV mixture,
after the documented row-coordinate change. This does not assert sufficiency. -/
theorem instrumental_mixture_printed_feasible {p : Instrumental.Row → ℝ}
    (hp : p ∈ Polytope.mixture Instrumental.matrix) :
    PrintedFeasible (fun i => p (rowEquiv i)) := by
  obtain ⟨q, hq, rfl⟩ := hp
  apply printed_mixture_feasible
  refine ⟨fun j => q (profileEquiv j), reindex_simplex hq, ?_⟩
  funext i
  exact reindex_mulVec q i

end MeraConstraints.Examples.Instrumental.Appendix
