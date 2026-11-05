import MeraConstraints.Polytope
import Mathlib.Tactic.NormNum

/-!
# Binary instrumental variable district

This chapter and the `Instrumental*` chapters after it treat the district
`{X, Y}` of the binary instrumental variable example, with the instrument `Z`
as its external parent. They correspond to the instrumental variable details in
the Supplementary Materials (`appendix:iv`).

A profile is a pair of binary response functions `X(Z)` and `Y(X)`, so there are
sixteen profiles. The eight rows of the matrix are indexed by `(Z, X, Y)`, the
type `Row` below, whereas the manuscript prints them in the order `(X, Y, Z)`.
The order of the columns does not matter.

For each treatment value `x`, the events `(X(0) = x, Y(x) = 0)` and
`(X(1) = x, Y(x) = 1)` cannot both occur. This gives an instrumental
inequality, proved below for every distribution of the response function
variables. The later chapters show that the twelve printed inequalities
describe the whole district polytope.

The matrix is written out by hand and defined by evaluating the response
functions. It is not obtained from a `HiddenGraph.Graph` for the instrumental
variable DAG, so these chapters are not an instance of the general theorems in
`MainResults`.
-/

namespace MeraConstraints.Examples.Instrumental

abbrev Profile := (Bool → Bool) × (Bool → Bool)
abbrev Row := Bool × Bool × Bool

def column (r : Profile) (z x y : Bool) : ℝ :=
  if r.1 z = x ∧ r.2 x = y then 1 else 0

def matrix : Matrix Row Profile ℝ :=
  fun row r => column r row.1 row.2.1 row.2.2

theorem card_profiles : Fintype.card Profile = 16 := by decide
theorem card_rows : Fintype.card Row = 8 := by decide

/-- Each profile satisfies the instrumental inequality: its two entries sum to at
most one. -/
theorem column_instrumental (r : Profile) (x : Bool) :
    column r false x false + column r true x true ≤ 1 := by
  cases hy : r.2 x <;> by_cases h0 : r.1 false = x <;>
    by_cases h1 : r.1 true = x <;> norm_num [column, hy, h0, h1]

/-- The instrumental inequality
`Pdo(X = x, Y = 0 ∣ Z = 0) + Pdo(X = x, Y = 1 ∣ Z = 1) ≤ 1` holds for every
distribution `q` of the profiles. -/
theorem instrumental (q : Profile → ℝ) (hq : q ∈ stdSimplex ℝ Profile) (x : Bool) :
    matrix.mulVec q (false, x, false) + matrix.mulVec q (true, x, true) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct, matrix]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ r, (column r false x false + column r true x true) * q r := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ ∑ r, 1 * q r := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_right (column_instrumental r x) (hq.1 r)
    _ = 1 := by simpa using hq.2

end MeraConstraints.Examples.Instrumental
