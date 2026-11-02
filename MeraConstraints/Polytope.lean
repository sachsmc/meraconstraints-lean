import MeraConstraints.Probability.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite mixture polytopes and constraint certificates

The V-representation is the image of the probability simplex under `B`.
Linear inequalities can be checked on its generating columns, including
when columns repeat. An H-representation carries a proof of equivalence;
the double-description implementation in R is not trusted by Lean.

Partial observations are represented by an arbitrary set of known rows.
Completing the other rows is exactly simplex feasibility with the known
matrix equations, the linear-algebra part of Remark `rmk:positivity`.
-/

namespace MeraConstraints
namespace Polytope

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- V-representation, without requiring distinct or extreme columns. -/
def mixture (B : Matrix Row Col ℝ) : Set (Row → ℝ) :=
  {p | ∃ q ∈ stdSimplex ℝ Col, B.mulVec q = p}

omit [Fintype Row] in
/-- The algorithm's V-representation is exactly the convex hull of columns,
including when the matrix contains duplicate columns. -/
theorem mixture_eq_convexHull (B : Matrix Row Col ℝ) :
    mixture B = convexHull ℝ (Set.range fun j => fun i => B i j) := by
  classical
  change (B.mulVecLin : (Col → ℝ) → (Row → ℝ)) '' stdSimplex ℝ Col = _
  rw [← convexHull_basis_eq_stdSimplex ℝ Col, LinearMap.image_convexHull,
    ← Set.range_comp]
  congr 1
  ext p
  simp only [Set.mem_range, Function.comp_apply, Matrix.mulVecLin_apply]
  constructor <;> rintro ⟨j, rfl⟩ <;> refine ⟨j, ?_⟩ <;>
    funext i <;> simp [Matrix.mulVec, dotProduct, mul_ite]

/-- A linear functional of a mixture is the mixture of its column values. -/
theorem score_mulVec (B : Matrix Row Col ℝ) (h : Row → ℝ) (q : Col → ℝ) :
    (∑ i, h i * B.mulVec q i) = ∑ j, q j * ∑ i, h i * B i j := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A certificate verified at each column bounds every compatible kernel. -/
theorem inequality_of_columns (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ)
    (hc : ∀ j, ∑ i, h i * B i j ≤ c) {p : Row → ℝ}
    (hp : p ∈ mixture B) : ∑ i, h i * p i ≤ c := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [score_mulVec]
  calc
    _ ≤ ∑ j, q j * c := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc j) (hq.1 j)
    _ = c := by rw [← Finset.sum_mul, hq.2, one_mul]

/-- A checked H-representation. Constructing this value requires proving
the conversion correct for the given matrix. -/
structure HRep (B : Matrix Row Col ℝ) (I E : Type*) where
  inequalities : Matrix I Row ℝ
  upper : I → ℝ
  equalities : Matrix E Row ℝ
  target : E → ℝ
  exact_representation : ∀ p, p ∈ mixture B ↔
    (∀ i, ∑ k, inequalities i k * p k ≤ upper i) ∧
    (∀ e, ∑ k, equalities e k * p k = target e)

omit [Fintype Row] in
/-- Completing unspecified entries and solving the reduced LP are equivalent. -/
theorem partial_completion_iff (B : Matrix Row Col ℝ) (known : Set Row)
    (observed : Row → ℝ) :
    (∃ p ∈ mixture B, ∀ i ∈ known, p i = observed i) ↔
      ∃ q ∈ stdSimplex ℝ Col, ∀ i ∈ known, B.mulVec q i = observed i := by
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hp⟩
    exact ⟨q, hq, hp⟩
  · rintro ⟨q, hq, hp⟩
    exact ⟨B.mulVec q, ⟨q, hq, rfl⟩, hp⟩

/-- The certificate direction of Proposition `prop:nontrivial` (ii).
On the equality set, a positive coordinate plus equality rows is nonnegative.
The converse requires facet geometry and is not asserted here. -/
theorem nonnegativity_certificate {E : Type*} [Fintype E]
    (A : Matrix E Row ℝ) (b weights : E → ℝ) (h : Row → ℝ) (c α : ℝ)
    (k : Row) (p : Row → ℝ) (hα : 0 < α) (hp : 0 ≤ p k)
    (he : ∀ e, ∑ i, A e i * p i = b e)
    (cert : c - ∑ i, h i * p i =
      α * p k + ∑ e, weights e * ((∑ i, A e i * p i) - b e)) :
    ∑ i, h i * p i ≤ c := by
  simp only [he, sub_self, mul_zero, Finset.sum_const_zero, add_zero] at cert
  have := mul_nonneg hα.le hp
  linarith

end Polytope
end MeraConstraints
