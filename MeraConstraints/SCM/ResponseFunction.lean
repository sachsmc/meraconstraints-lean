/-
Copyright (c) 2026 Michael C. Sachs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael C. Sachs, Claude
-/
import MeraConstraints.SCM.Basic

/-!
# Response functions and canonical partitioning

This chapter is the background for the canonical partitioning subsection of the
manuscript (`sec:respvar`). The input of an observed variable `V_i` may be
continuous or high-dimensional, but it only selects which function of the
parents of `V_i` the structural equation uses, and there are finitely many such
functions. Grouping the values of the input by the function they select gives a
finite partition. The response function variable `R_{V_i}` records the class.

* `RespFun G val i` is the type of response functions of `V_i`, the functions from
  the joint values of its parents to its values. Its size is
  `|V_i|^{k_i}`, where `k_i` is the number of joint values of the parents
  (`RespFun.card`). `RespAssign` is a joint value of the response functions of all
  the variables.
* `SCM.respMap M i` sends an input value `u` to the response function
  `F_i(·, u)`. The partition is `Setoid.ker (M.respMap i)`, and its quotient is
  finite (`SCM.finite_canonicalPartition`). `SCM.proposition1` says that each `u`
  determines a unique response function. The name does not refer to
  Proposition 1 (`prop:ident`) of the manuscript.
* `evalR` evaluates a joint value of the response functions recursively along the
  order. `SCM.eval_eq_evalR` shows that evaluating the structural equations at
  `u` gives the same values as evaluating the response functions `M.respOf u`
  induced by `u`.

These facts are the basis of the response function variable transformation, and
`SCM/Intervention.lean` shows that it preserves interventions (Remark 1, `rmk1`).
-/

namespace MeraConstraints

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)

/-!
## Response functions and how many there are

A response function of `V_i` is a function from the joint values of its parents to
its values. There are `|V_i|^{k_i}` of them, where `k_i` is the number of joint
values of the parents. A joint value of the response functions of all the
variables has the product of these numbers of possibilities.
-/

/-- The type of response functions of `V_i`: functions from the joint values of
its observed parents to its values. The response function variable `R_{V_i}` takes
values in this finite type. -/
abbrev RespFun (i : Fin n) : Type _ :=
  PaAssign G val i → val i

/-- A joint value of the response functions of all the observed variables. -/
abbrev RespAssign : Type _ :=
  ∀ i : Fin n, RespFun G val i

namespace RespFun

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The number of levels of the response function variable `R_{V_i}` is
`|V_i|^{k_i}`, where `k_i` is the number of joint values of the observed parents
of `V_i`, as in the response function variable transformation. -/
theorem card (i : Fin n) :
    Fintype.card (RespFun G val i)
      = Fintype.card (val i) ^ ∏ j ∈ G.parents i, Fintype.card (val j) := by
  rw [Fintype.card_fun, PaAssign.card]

/-- The number of joint values of the response functions of all the variables is
the product of the numbers for each variable. -/
theorem card_respAssign :
    Fintype.card (RespAssign G val)
      = ∏ i, Fintype.card (val i) ^ ∏ j ∈ G.parents i, Fintype.card (val j) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => card G val i

end RespFun

variable {G val}

/-!
## Evaluating a response-function assignment

A response function for every variable determines the values of all observed
variables by the same recursion as `SCM.eval`. The existence and uniqueness
statements are the same as for `SCM.eval`.
-/

/-- The values of the observed variables determined by the response functions
`r`: each `V_i` is `r i` applied to the values of its parents. The recursion
terminates because parents have smaller indices. -/
def evalR (r : RespAssign G val) (i : Fin n) : val i :=
  r i (fun j => evalR r j)
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- `evalR r` solves the equations `v_i = r i (pa_i)`. -/
theorem evalR_eq (r : RespAssign G val) (i : Fin n) :
    evalR r i = r i (PaAssign.restrict (evalR r) i) := by
  rw [evalR]; rfl

/-- Any joint value satisfying the equations `v_i = r i (pa_i)` agrees with
`evalR r` at every variable. -/
theorem evalR_unique_apply (r : RespAssign G val) (w : FullAssign val)
    (hw : ∀ i, w i = r i (PaAssign.restrict w i)) (i : Fin n) :
    w i = evalR r i := by
  rw [hw i, evalR]
  congr 1
  funext j
  exact evalR_unique_apply r w hw j
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- The solution of the equations `v_i = r i (pa_i)` is unique: it is `evalR r`. -/
theorem evalR_unique (r : RespAssign G val) (w : FullAssign val)
    (hw : ∀ i, w i = r i (PaAssign.restrict w i)) :
    w = evalR r :=
  funext fun i => evalR_unique_apply r w hw i

namespace SCM

variable (M : SCM G val)

/-!
## The canonical partition

The map `respMap` sends each input value `u` of `V_i` to the response function
`F_i(·, u)` that it induces. Each `u` induces exactly one response function, and
the fibers of this map partition the input type into finitely many classes,
however large the input type is. `eval_eq_evalR` shows that evaluating the
structural equations at `u` gives the same values as evaluating the response
functions induced by `u`.
-/

/-- Sends a value `u` of the input of `V_i` to the response function it induces,
`pa ↦ F_i(pa, u)`. The canonical partition is the partition of `M.exo i` into the
fibers of this map, `Setoid.ker (M.respMap i)`. -/
def respMap (i : Fin n) (u : M.exo i) : RespFun G val i :=
  fun pa => M.F i pa u

/-- Each value `u` of the input of `V_i`, whatever the input type, induces a unique
response function `r` with `F_i(pa, u) = r pa` for all `pa`. The set of response
functions is finite (`RespFun.card`). -/
theorem proposition1 (i : Fin n) (u : M.exo i) :
    ∃! r : RespFun G val i, ∀ pa : PaAssign G val i, M.F i pa u = r pa :=
  ⟨M.respMap i u, fun _ => rfl, fun _ hr => (funext fun pa => (hr pa).symm)⟩

/-- The canonical partition of the input type of `V_i`, the quotient by
`u₁ ∼ u₂ ↔ respMap u₁ = respMap u₂`, has finitely many classes. -/
theorem finite_canonicalPartition [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
    (i : Fin n) :
    Finite (Quotient (Setoid.ker (M.respMap i))) :=
  have : Finite (Set.range (M.respMap i)) := (Set.toFinite _).to_subtype
  Finite.of_equiv _ (Setoid.quotientKerEquivRange (M.respMap i)).symm

/-- The joint value of the response functions induced by the inputs `u`. -/
def respOf (u : ∀ i, M.exo i) : RespAssign G val :=
  fun i => M.respMap i (u i)

/-- Evaluating the structural equations at the inputs `u` gives the same values as
evaluating the response functions induced by `u`. -/
theorem eval_eq_evalR (u : ∀ i, M.exo i) :
    M.eval u = evalR (M.respOf u) :=
  evalR_unique (M.respOf u) (M.eval u) fun i => M.eval_eq u i

end SCM

end MeraConstraints

