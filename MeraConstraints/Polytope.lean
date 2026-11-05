import MeraConstraints.Probability.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# District polytopes and their representations

`Polytope.mixture B` is the district polytope `{B r}` of the manuscript, the
image of the probability simplex under the matrix `B` (the V-representation). It
is the convex hull of the columns of `B`, and a linear inequality holds on it if
it holds at every column. `Polytope.HRep B I E` is an H-representation
`H_i p ≤ b_i`, `H_e p = b_e` together with a proof that it describes the same set.
No output of R or `cdd` is trusted, because an H-representation is only used with
such a proof.

If only some entries of `p` are specified, the others can be completed to a point
of the polytope exactly when some `r` in the simplex has `B r` equal to `p` at the
specified entries. This is the linear algebra in Remark 2 (`rmk:positivity`).
-/

namespace MeraConstraints
namespace Polytope

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- The district polytope `{B r}`, where `r` ranges over the probability simplex
(V-representation). Columns may repeat. -/
def mixture (B : Matrix Row Col ℝ) : Set (Row → ℝ) :=
  {p | ∃ q ∈ stdSimplex ℝ Col, B.mulVec q = p}

omit [Fintype Row] in
/-- The district polytope is the convex hull of the columns of `B`. -/
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

/-- A linear function of `B r` is the `r`-weighted average of its values at the
columns of `B`. -/
theorem score_mulVec (B : Matrix Row Col ℝ) (h : Row → ℝ) (q : Col → ℝ) :
    (∑ i, h i * B.mulVec q i) = ∑ j, q j * ∑ i, h i * B i j := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An inequality that holds at every column of `B` holds on the district
polytope. -/
theorem inequality_of_columns (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ)
    (hc : ∀ j, ∑ i, h i * B i j ≤ c) {p : Row → ℝ}
    (hp : p ∈ mixture B) : ∑ i, h i * p i ≤ c := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [score_mulVec]
  calc
    _ ≤ ∑ j, q j * c := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc j) (hq.1 j)
    _ = c := by rw [← Finset.sum_mul, hq.2, one_mul]

/-- An H-representation of the district polytope of `B`: the inequalities
`inequalities p ≤ upper` (`H_i`, `b_i`) and the equations `equalities p = target`
(`H_e`, `b_e`). The field `exact_representation` is a proof that they hold
exactly on the polytope. -/
structure HRep (B : Matrix Row Col ℝ) (I E : Type*) where
  inequalities : Matrix I Row ℝ
  upper : I → ℝ
  equalities : Matrix E Row ℝ
  target : E → ℝ
  exact_representation : ∀ p, p ∈ mixture B ↔
    (∀ i, ∑ k, inequalities i k * p k ≤ upper i) ∧
    (∀ e, ∑ k, equalities e k * p k = target e)

omit [Fintype Row] in
/-- Some point of the polytope agrees with `observed` on the specified entries
`known` exactly when some `q` in the simplex has `B q` equal to `observed` there. -/
theorem partial_completion_iff (B : Matrix Row Col ℝ) (known : Set Row)
    (observed : Row → ℝ) :
    (∃ p ∈ mixture B, ∀ i ∈ known, p i = observed i) ↔
      ∃ q ∈ stdSimplex ℝ Col, ∀ i ∈ known, B.mulVec q i = observed i := by
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hp⟩
    exact ⟨q, hq, hp⟩
  · rintro ⟨q, hq, hp⟩
    exact ⟨B.mulVec q, ⟨q, hq, rfl⟩, hp⟩

/-- If `c - hᵀp = α p_k + λᵀ(H_e p - b_e)` with `α > 0`, then `hᵀp ≤ c` holds at
every `p` with `p_k ≥ 0` that satisfies the equations. This is the easy direction
of Proposition 4 (`prop:nontrivial`) (ii); the converse is in
`FacetCriterion`. -/
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
