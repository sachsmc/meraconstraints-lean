/-
Copyright (c) 2026 Michael C. Sachs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael C. Sachs, Claude
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Causal DAGs and structural causal models

The paper's starting point is a *nonparametric structural equation model*
(NPSEM): a directed acyclic graph whose vertices are categorical observed
variables `W_1, …, W_n`, where each variable is determined by its parents
in the graph together with an unmeasured influence,

  `w_i = F_{W_i}(pa_{W_i}, u_{W_i})`.

Nothing is assumed about the unmeasured `U_{W_i}` — they may be continuous,
multivariate, correlated with each other in arbitrary ways.  All the
confounding one might fear lives in their joint distribution.  This chapter
formalizes the graph, the model, and the fact that the structural equations
have a unique solution: fixing the unmeasured inputs determines the
observed world.

This chapter defines:

* `MeraConstraints.CausalDAG`: a DAG on `Fin n` presented in topological order
  (every parent has a smaller index).  Since the observed variables of any
  finite DAG can be relabeled along a topological order, this loses no
  generality. Districts need not be contiguous in this global order.
* `MeraConstraints.PaAssign G val i`: an assignment of values to the parents of
  variable `i` (the paper's `ν(Pa_{W_i})`).
* `MeraConstraints.SCM`: a structural causal model: each observed variable `i`
  carries an arbitrary type `exo i` of unmeasured influences (the paper's
  `ν(U_{W_i})`, allowed to be "continuous or multivariate") and a structural
  function `F i : PaAssign G val i → exo i → val i` (the paper's
  `F_{W_i}(pa_{W_i}, u_{W_i})`).
* `MeraConstraints.SCM.eval`: the deterministic evaluation `u ↦ w` obtained by
  recursively solving the structural equations (the paper's `g^*_{W_i}(r)`
  specialised to exogenous input), together with its characterising
  equations (`eval_eq`) and uniqueness (`eval_unique`).

This is a general structural foundation adapted from `causaloptim-lean`.
It does not yet constrain which variables share latent inputs or specify
independence of latent roots. The new `HiddenGraph` chapters impose the
present manuscript's common-cause graph and retain private disturbances.

The type of values `val i` of each observed variable is a parameter kept
outside the structures so that the response-function machinery
(`MeraConstraints/SCM/ResponseFunction.lean`), which does not depend on the
unmeasured influences, can be shared by every SCM over the same DAG.
-/

namespace MeraConstraints

/-!
## The graph

A causal DAG on vertices `0, …, n-1`.  Rather than assuming acyclicity and
then choosing a topological order, we build the order into the definition:
`parents i` may only contain indices smaller than `i`.  Every finite DAG
can be presented this way by relabeling, so no generality is lost, and
every recursion along the graph below becomes a recursion on `Fin n`.
-/

/-- A directed acyclic graph on the vertex set `Fin n`, presented in
topological order: every parent of a vertex has strictly smaller index.
The paper's `W_j ∈ Pa_{W_i}` corresponds to `j ∈ parents i`. -/
structure CausalDAG (n : ℕ) where
  /-- The parent set of each vertex. -/
  parents : Fin n → Finset (Fin n)
  /-- Topological ordering: parents have smaller indices.  This encodes
  acyclicity. -/
  parents_lt : ∀ ⦃i j : Fin n⦄, j ∈ parents i → j < i

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)

/-- An assignment of values to the parents of variable `i`; the paper's
`pa_{W_i} ∈ ν(Pa_{W_i})`.  An `abbrev` so that finiteness, decidability and
nonemptiness instances of the underlying Pi type apply directly. -/
abbrev PaAssign (i : Fin n) : Type _ :=
  ∀ j : {j : Fin n // j ∈ G.parents i}, val j

/-- A full assignment of values to all observed variables; the paper's
`w ∈ ν(W)`. -/
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

/-- The number of parent assignments is the product of the cardinalities of
the parents' value sets: `|ν(Pa_{W_i})| = ∏_{V ∈ Pa_{W_i}} c_V`. -/
theorem card [∀ i, Fintype (val i)] (i : Fin n) :
    Fintype.card (PaAssign G val i) = ∏ j ∈ G.parents i, Fintype.card (val j) := by
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort (G.parents i) fun j => Fintype.card (val j)

end PaAssign

/-!
## The model

An SCM equips each variable with an arbitrary (possibly infinite) type of
unmeasured influences and a structural function.  Note what is *not* here:
no distribution on the unmeasured influences yet, and no independence
assumptions.  A "causal model compatible with the DAG" in later chapters
will be an `SCM` together with a distribution on its exogenous inputs; the
worst case over all such distributions is what the bounds quantify over.
-/

/-- A structural causal model (nonparametric structural equation model) over
the DAG `G` with observed value types `val`: for each variable an arbitrary
type of unmeasured influences and a structural function determining the
variable from its parents and its unmeasured influence.

Taking `PaAssign` as the domain of `F i` builds the paper's requirement that
`W_i` is a function of `(Pa_{W_i}, U_{W_i})` directly into the type. -/
structure SCM where
  /-- The value type of the unmeasured influences `U_{W_i}`; arbitrary
  (possibly infinite). -/
  exo : Fin n → Type*
  /-- Every variable has unmeasured influences to draw from. -/
  exoNonempty : ∀ i, Nonempty (exo i)
  /-- The structural function `F_{W_i}`. -/
  F : ∀ i : Fin n, PaAssign G val i → exo i → val i

namespace SCM

variable {G} {val} (M : SCM G val)

/-!
## Solving the structural equations

Because parents precede children in the ordering, the structural equations
can be solved by strong recursion: the value of `W_i` is `F_i` applied to
the (recursively computed) values of its parents and its own unmeasured
input.  `eval` performs this recursion, `eval_eq` says the result solves
the equations, and `eval_unique` says nothing else does.  Together they are
the formal content of the informal phrase "the model determines the data."
-/

/-- Deterministic evaluation of the structural equations: given a full
exogenous assignment `u`, produce the (unique) full observed assignment
solving `w_i = F_i(pa_i, u_i)`.  This is the paper's recursive evaluation
`w_i = g^*_{W_i}(r)` with exogenous input in place of response functions. -/
def eval (u : ∀ i, M.exo i) (i : Fin n) : val i :=
  M.F i (fun j => eval u j) (u i)
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- The defining equation of `eval`: it solves the structural equations. -/
theorem eval_eq (u : ∀ i, M.exo i) (i : Fin n) :
    M.eval u i = M.F i (PaAssign.restrict (M.eval u) i) (u i) := by
  rw [eval]; rfl

/-- Uniqueness of the solution of the structural equations, pointwise form:
any full assignment satisfying all structural equations agrees with `eval u`
everywhere.  Proved by strong induction along the topological order. -/
theorem eval_unique_apply (u : ∀ i, M.exo i) (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (u i)) (i : Fin n) :
    w i = M.eval u i := by
  rw [hw i, eval]
  congr 1
  funext j
  exact eval_unique_apply u w hw j
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- Uniqueness of the solution of the structural equations: any full
assignment satisfying all structural equations is `eval u`. -/
theorem eval_unique (u : ∀ i, M.exo i) (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (u i)) :
    w = M.eval u :=
  funext fun i => M.eval_unique_apply u w hw i

end SCM

end MeraConstraints

