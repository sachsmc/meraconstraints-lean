/-
Copyright (c) 2026 Michael C. Sachs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael C. Sachs, Claude
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Directed acyclic graphs of observed variables and structural equations

A nonparametric structural equation model on observed variables `V_1, …, V_n`
determines each variable from its observed parents and an unobserved input:
`v_i = F_i(pa_i, u_i)`. The inputs may take values in any type, so no assumption
is made on the unobserved variables. This chapter defines the graph and the
model, and shows that the structural equations have a unique solution: fixing the
inputs fixes the values of the observed variables.

* `CausalDAG n` is a DAG on the observed variables `Fin n`, in topological order:
  every parent has a smaller index. Any DAG can be relabeled this way. Districts
  need not be contiguous in this order.
* `PaAssign G val i` is a joint value of the observed parents of `V_i`. The
  values `val i` of each variable are a parameter, so that the response functions
  (`SCM/ResponseFunction.lean`) can be shared by every model on the same graph.
* `SCM` gives each variable `i` an input type `exo i` and a structural equation
  `F i : PaAssign G val i → exo i → val i`.
* `SCM.eval` solves the equations recursively along the order and gives the
  values of all observed variables from the inputs. `eval_eq` says that this is a
  solution and `eval_unique` that it is the only one.

Here each variable has its own input and the inputs have no distribution. The
hidden variables DAG of the manuscript, with unobserved variables shared by
several observed variables and independent inputs, is `HiddenGraph.SCM` in the
`HiddenGraph` chapters. It uses `CausalDAG` for the observed variables.
-/

namespace MeraConstraints

/-!
## The graph

The order is part of the definition: `parents i` contains only indices smaller
than `i`. This implies acyclicity, and recursions along the graph become
recursions on `Fin n`.
-/

/-- A directed acyclic graph on the observed variables `Fin n`, in topological
order: every parent of a variable has a strictly smaller index. The observed
parents of `V_i` are the `V_j` with `j ∈ parents i`. -/
structure CausalDAG (n : ℕ) where
  /-- The observed parents of each variable. -/
  parents : Fin n → Finset (Fin n)
  /-- Parents have smaller indices, which implies acyclicity. -/
  parents_lt : ∀ ⦃i j : Fin n⦄, j ∈ parents i → j < i

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)

/-- A joint value of the observed parents of `V_i`. -/
abbrev PaAssign (i : Fin n) : Type _ :=
  ∀ j : {j : Fin n // j ∈ G.parents i}, val j

/-- A joint value of all the observed variables. -/
abbrev FullAssign : Type _ :=
  ∀ i : Fin n, val i

namespace PaAssign

variable {G} {val}

/-- Restrict a full assignment to the parents of `i`. -/
def restrict (w : FullAssign val) (i : Fin n) : PaAssign G val i :=
  fun j => w j

@[simp] theorem restrict_apply (w : FullAssign val) (i : Fin n)
    (j : {j : Fin n // j ∈ G.parents i}) :
    restrict w i j = w j := rfl

/-- The number of joint values of the parents of `V_i` is the product of the
numbers of values of the parents. -/
theorem card [∀ i, Fintype (val i)] (i : Fin n) :
    Fintype.card (PaAssign G val i) = ∏ j ∈ G.parents i, Fintype.card (val j) := by
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort (G.parents i) fun j => Fintype.card (val j)

end PaAssign

/-!
## The model

Each variable has an input type, which may be infinite, and a structural
equation. The model carries no distribution on the inputs.
-/

/-- A structural model on the DAG `G` with observed value types `val`: for each
variable an input type and a structural equation that determines the variable
from its observed parents and its input. -/
structure SCM where
  /-- The input type of `V_i`; it may be infinite. -/
  exo : Fin n → Type*
  /-- Each input type is nonempty. -/
  exoNonempty : ∀ i, Nonempty (exo i)
  /-- The structural equation `F_i` of `V_i`. -/
  F : ∀ i : Fin n, PaAssign G val i → exo i → val i

namespace SCM

variable {G} {val} (M : SCM G val)

/-!
## Solving the structural equations

Because parents precede children in the order, the equations are solved by
recursion: the value of `V_i` is `F_i` applied to the computed values of
its parents and its input. `eval` performs this recursion, `eval_eq` says that
the result solves the equations, and `eval_unique` says that nothing else does.
-/

/-- The values of the observed variables determined by the inputs `u`, found by
solving `v_i = F_i(pa_i, u_i)` recursively along the order. -/
def eval (u : ∀ i, M.exo i) (i : Fin n) : val i :=
  M.F i (fun j => eval u j) (u i)
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- `eval u` solves the structural equations. -/
theorem eval_eq (u : ∀ i, M.exo i) (i : Fin n) :
    M.eval u i = M.F i (PaAssign.restrict (M.eval u) i) (u i) := by
  rw [eval]; rfl

/-- Any joint value satisfying the structural equations agrees with `eval u` at
every variable. The proof is by induction along the order. -/
theorem eval_unique_apply (u : ∀ i, M.exo i) (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (u i)) (i : Fin n) :
    w i = M.eval u i := by
  rw [hw i, eval]
  congr 1
  funext j
  exact eval_unique_apply u w hw j
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- The solution of the structural equations is unique: any joint value satisfying
them is `eval u`. -/
theorem eval_unique (u : ∀ i, M.exo i) (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (u i)) :
    w = M.eval u :=
  funext fun i => M.eval_unique_apply u w hw i

end SCM

end MeraConstraints

