import MeraConstraints.Polytope
import Mathlib.Tactic.NormNum

/-!
# Bell profiles and the CHSH obstruction

For two binary members with separate external inputs, each deterministic
profile assigns `A=f(X)` and `B=g(Y)`. The four parity tests can be met at
most three times. Averaging proves the CHSH inequality for every shared-latent
mixture. A PR box meets all four tests, and so is incompatible.

This is the binary core of Remark `prop:ineqstructure` (ii), not yet its
lifting to arbitrary paths in a larger hidden-variable graph.
-/

namespace MeraConstraints.Examples.Bell

abbrev Profile := (Bool → Bool) × (Bool → Bool)
abbrev Input := Bool × Bool
abbrev Output := Bool × Bool

/-- Indicator of winning the parity game at one input pair. -/
def win (a b x y : Bool) : ℝ := if Bool.xor a b = (x && y) then 1 else 0

def score (r : Profile) : ℝ :=
  win (r.1 false) (r.2 false) false false +
  win (r.1 false) (r.2 true) false true +
  win (r.1 true) (r.2 false) true false +
  win (r.1 true) (r.2 true) true true

theorem score_le_three (r : Profile) : score r ≤ 3 := by
  cases ha : r.1 false <;> cases hb : r.1 true <;>
    cases hc : r.2 false <;> cases hd : r.2 true <;>
    norm_num [score, win, ha, hb, hc, hd]

/-- CHSH in its probability-of-winning form. -/
theorem chsh (q : Profile → ℝ) (hq : q ∈ stdSimplex ℝ Profile) :
    (∑ r, q r * score r) ≤ 3 := by
  calc
    _ ≤ ∑ r, q r * 3 := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left (score_le_three r) (hq.1 r)
    _ = 3 := by rw [← Finset.sum_mul, hq.2, one_mul]

/-- PR-box kernel, normalized separately at each input. -/
noncomputable def prBox (e : Input) (o : Output) : ℝ :=
  if Bool.xor o.1 o.2 = (e.1 && e.2) then 1 / 2 else 0

theorem prBox_mem_stdSimplex (e : Input) : prBox e ∈ stdSimplex ℝ Output := by
  constructor
  · intro o
    unfold prBox
    split <;> norm_num
  · rcases e with ⟨x, y⟩
    cases x <;> cases y <;>
      norm_num [prBox, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The PR-box winning score is four, strictly above the shared-latent bound. -/
theorem prBox_wins (e : Input) :
    (∑ o : Output, prBox e o * win o.1 o.2 e.1 e.2) = 1 := by
  rcases e with ⟨x, y⟩
  cases x <;> cases y <;>
    norm_num [prBox, win, Fintype.sum_prod_type, Fintype.sum_bool]

abbrev Row := Input × Output

def matrix : Matrix Row Profile ℝ :=
  fun row r => if (r.1 row.1.1, r.2 row.1.2) = row.2 then 1 else 0

def gameWeight (row : Row) : ℝ := win row.2.1 row.2.2 row.1.1 row.1.2

theorem columns_chsh (r : Profile) :
    (∑ row, gameWeight row * matrix row r) ≤ 3 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases ha : r.1 false <;> cases hb : r.1 true <;>
    cases hc : r.2 false <;> cases hd : r.2 true <;>
    norm_num [matrix, gameWeight, win, Fintype.sum_prod_type,
      Fintype.sum_bool, ha, hb, hc, hd]

theorem prBox_score :
    (∑ row : Row, gameWeight row * prBox row.1 row.2) = 4 := by
  norm_num [gameWeight, prBox, win, Fintype.sum_prod_type, Fintype.sum_bool]

/-- A normalized kernel outside the Bell district polytope. -/
theorem prBox_not_mem_mixture :
    (fun row : Row => prBox row.1 row.2) ∉ Polytope.mixture matrix := by
  intro hp
  have h := Polytope.inequality_of_columns matrix gameWeight 3 columns_chsh hp
  rw [prBox_score] at h
  norm_num at h

end MeraConstraints.Examples.Bell
