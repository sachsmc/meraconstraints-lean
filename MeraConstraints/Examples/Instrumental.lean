import MeraConstraints.Polytope
import Mathlib.Tactic.NormNum

/-!
# Binary instrumental-variable district

Profiles are the sixteen pairs of binary response functions `X(Z)` and
`Y(X)`. The eight matrix rows are indexed by `(Z, X, Y)` rather than the
printed order in Appendix B; column ordering is immaterial.

For each fixed treatment value `x`, the incompatible events
`(X(0)=x,Y(x)=0)` and `(X(1)=x,Y(x)=1)` give an instrumental inequality.
This supplies a proof certificate for a nontrivial restriction, without
trusting the R computation or claiming that these rows are complete.
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

/-- Every deterministic response profile satisfies the instrumental row. -/
theorem column_instrumental (r : Profile) (x : Bool) :
    column r false x false + column r true x true ≤ 1 := by
  cases hy : r.2 x <;> by_cases h0 : r.1 false = x <;>
    by_cases h1 : r.1 true = x <;> norm_num [column, hy, h0, h1]

/-- The corresponding observable-kernel inequality for every latent mixture. -/
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
