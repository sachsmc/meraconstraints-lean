import MeraConstraints.Probability.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Independent families of finite latent variables

In the proof of Proposition `prop:complete`, each district receives an
unrestricted joint response-profile law, and the laws of different districts
are taken **mutually independent**. Pairwise independence of individual
selectors would not suffice for the product event identity used there.

Here independence is a construction: the joint mass of a tuple is the product
of its coordinate masses. We prove normalization and the rectangular-event
formula, including empty index families. Later the coordinates will be whole
district response profiles, rather than individual observed variables.
-/

namespace MeraConstraints.Independent

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {R : D → Type*} [∀ d, Fintype (R d)]

/-- Joint mass of a mutually independent family of finite random variables. -/
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
/-- The indicator of an intersection separates coordinate by coordinate. -/
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

/-- Probability of a rectangle is the product of its coordinate probabilities.
No support or positivity assumption is needed for this identity. -/
theorem rectangular_mass (q : ∀ d, R d → ℝ)
    (A : ∀ d, R d → Prop) [∀ d, DecidablePred (A d)] :
    (∑ r, if ∀ d, A d (r d) then joint q r else 0) =
      ∏ d, ∑ a, if A d a then q d a else 0 := by
  simp_rw [rectangular_indicator]
  exact (Fintype.prod_sum (fun d a => if A d a then q d a else 0)).symm

end MeraConstraints.Independent
