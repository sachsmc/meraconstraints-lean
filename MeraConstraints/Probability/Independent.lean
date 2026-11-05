import MeraConstraints.Probability.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Mutually independent families of finite random variables

In the proof of Proposition 3 (`prop:complete`), the response function variables
of each district have an unrestricted joint distribution, and those of different
districts are mutually independent. The coordinates here play the role of the
districts. Mutual independence, not only pairwise independence, is needed for the
product formula used there.

`joint q` is the distribution of a family in which the joint mass of a tuple is
the product of its coordinate masses. This chapter shows that `joint q` is a
probability vector when each `q d` is (`joint_mem_stdSimplex`), and that the
probability of a rectangle is the product of the coordinate probabilities
(`rectangular_mass`). Both hold for an empty family.
-/

namespace MeraConstraints.Independent

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {R : D → Type*} [∀ d, Fintype (R d)]

/-- The joint mass of a mutually independent family: the product of the
coordinate masses `q d (r d)`. -/
def joint (q : ∀ d, R d → ℝ) (r : ∀ d, R d) : ℝ := ∏ d, q d (r d)

theorem sum_joint (q : ∀ d, R d → ℝ) :
    (∑ r, joint q r) = ∏ d, ∑ a, q d a := by
  exact (Fintype.prod_sum q).symm

theorem joint_mem_stdSimplex (q : ∀ d, R d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (R d)) :
    joint q ∈ stdSimplex ℝ (∀ d, R d) := by
  constructor
  · intro r
    exact Finset.prod_nonneg fun d _ => (hq d).1 (r d)
  · rw [sum_joint]
    simp only [fun d => (hq d).2, Finset.prod_const_one]

omit [DecidableEq D] [∀ d, Fintype (R d)] in
/-- The joint mass restricted to a rectangle is the product of the coordinate
masses, each restricted to its own coordinate set. -/
theorem rectangular_indicator (q : ∀ d, R d → ℝ)
    (A : ∀ d, R d → Prop) [∀ d, DecidablePred (A d)] (r : ∀ d, R d) :
    (if ∀ d, A d (r d) then joint q r else 0) =
      ∏ d, if A d (r d) then q d (r d) else 0 := by
  classical
  by_cases h : ∀ d, A d (r d)
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro d _
    rw [if_pos (h d)]
  · rw [if_neg h]
    obtain ⟨d, hd⟩ := not_forall.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ d) (if_neg hd)).symm

/-- The probability of a rectangle is the product of its coordinate
probabilities. -/
theorem rectangular_mass (q : ∀ d, R d → ℝ)
    (A : ∀ d, R d → Prop) [∀ d, DecidablePred (A d)] :
    (∑ r, if ∀ d, A d (r d) then joint q r else 0) =
      ∏ d, ∑ a, if A d a then q d a else 0 := by
  simp_rw [rectangular_indicator]
  exact (Fintype.prod_sum (fun d a => if A d a then q d a else 0)).symm

end MeraConstraints.Independent
