/-
Copyright (c) 2026 Michael C. Sachs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael C. Sachs, Claude
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite probability preliminaries

The observed variables are categorical, and the response function variables
take finitely many values. A probability distribution on a finite type `α` is
therefore a vector `q : α → ℝ` of nonnegative entries summing to one, an element
of `stdSimplex ℝ α` in Mathlib. This chapter uses only finite sums. The unobserved
variables of the structural model may take values in any measurable space; the
step from an arbitrary probability measure to a finite vector is in
`Probability.MeasureFinite`.

It defines three constructions:

* `pushforward f q` is the distribution of `f(X)` when `X ∼ q`, that is
  `b ↦ ∑_{a : f a = b} q a`. The observed distribution of a model is the
  pushforward of the distribution of the response function variables along the
  recursive evaluation map.
* `prodDist μ ν` is the joint distribution of independent `X ∼ μ` and `Y ∼ ν`.
  `Probability.Independent` extends this to a mutually independent family, such
  as the response function variables of the districts.
* `uniformDist α` is the uniform distribution, used as a strictly positive
  example.

Each construction maps the simplex to the simplex: it preserves nonnegativity and
total mass.
-/

namespace MeraConstraints

variable {α β : Type*} [Fintype α] [Fintype β]

/-!
## Pushforward distributions

If `X ∼ q` and only `f(X)` is observed, the distribution of the observation
assigns to each `b` the total mass of the fiber `f⁻¹(b)`. When `f` is the
evaluation map of a structural model, sending a joint value of the response
functions to the values of the observed variables, `pushforward f q` is the
observed distribution.
-/

section Pushforward

variable [DecidableEq β] (f : α → β) (q : α → ℝ)

/-- The pushforward of a vector `q : α → ℝ` along `f : α → β`:
`b ↦ ∑_{a : f a = b} q a`.  If `q` is the distribution of `X` then
`pushforward f q` is the distribution of `f X`. -/
def pushforward : β → ℝ :=
  fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), q a

omit [Fintype β] in
theorem pushforward_apply (b : β) :
    pushforward f q b = ∑ a ∈ Finset.univ.filter (fun a => f a = b), q a :=
  rfl

omit [Fintype β] in
theorem pushforward_nonneg (hq : ∀ a, 0 ≤ q a) (b : β) :
    0 ≤ pushforward f q b :=
  Finset.sum_nonneg fun a _ => hq a

theorem sum_pushforward :
    ∑ b, pushforward f q b = ∑ a, q a :=
  Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a)) q

theorem pushforward_mem_stdSimplex (hq : q ∈ stdSimplex ℝ α) :
    pushforward f q ∈ stdSimplex ℝ β :=
  ⟨pushforward_nonneg f q hq.1, by rw [sum_pushforward]; exact hq.2⟩

end Pushforward

/-!
## Product distributions

Two finite random objects are independent when their joint mass is the product of
their marginal masses. This is the two-factor case of the family construction in
`Probability.Independent`.
-/

section ProdDist

variable (μ : α → ℝ) (ν : β → ℝ)

/-- The product (independent joint) distribution of `μ` and `ν`. -/
def prodDist : α × β → ℝ :=
  fun x => μ x.1 * ν x.2

omit [Fintype α] [Fintype β] in
@[simp] theorem prodDist_apply (a : α) (b : β) :
    prodDist μ ν (a, b) = μ a * ν b :=
  rfl

theorem sum_prodDist :
    ∑ x : α × β, prodDist μ ν x = (∑ a, μ a) * ∑ b, ν b := by
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_mul_sum _ _ _ _).symm

theorem prodDist_mem_stdSimplex (hμ : μ ∈ stdSimplex ℝ α) (hν : ν ∈ stdSimplex ℝ β) :
    prodDist μ ν ∈ stdSimplex ℝ (α × β) :=
  ⟨fun x => mul_nonneg (hμ.1 x.1) (hν.1 x.2),
    by rw [sum_prodDist, hμ.2, hν.2, one_mul]⟩

end ProdDist

/-!
## The uniform distribution

The uniform distribution is a strictly positive element of the simplex on any
nonempty finite type.
-/

section Uniform

variable (α) [Nonempty α]

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDist : α → ℝ :=
  fun _ => (Fintype.card α : ℝ)⁻¹

theorem uniformDist_pos (a : α) : 0 < uniformDist α a :=
  inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)

theorem uniformDist_mem_stdSimplex : uniformDist α ∈ stdSimplex ℝ α := by
  refine ⟨fun a => (uniformDist_pos α a).le, ?_⟩
  simp only [uniformDist]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

end Uniform

end MeraConstraints

