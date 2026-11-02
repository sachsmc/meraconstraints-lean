/-
Copyright (c) 2026 Michael C. Sachs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael C. Sachs, Claude
-/
import MeraConstraints.SCM.Basic

/-!
# Response functions and canonical partitioning

This chapter is adapted from Proposition 1 of the different manuscript
formalized in `causaloptim-lean`. In the present manuscript these results
are background for Section `sec:respvar`. The historical declaration name
`SCM.proposition1` is retained; it does not denote `prop:hlp` here.

The unmeasured influence `U_W` of a variable `W` may be a continuous,
high-dimensional object — but only finitely much of it can ever matter.
All `U_W` does in the model is select which function of the parents the
structural equation implements, and there are only finitely many functions
`ν(Pa_W) → ν(W)`.  Partitioning `ν(U_W)` according to *which* function is
selected yields the **canonical partition**: finitely many
classes, one per *response function*.  Replacing `U_W` by the discrete
random variable `R_W` recording its class loses nothing observable — and
the mechanisms can be represented by a finite joint response-profile type.

This move (due to Balke and Pearl in the binary-instrument setting, made
generalized in the source development) is the linchpin of the method: it converts "optimize
over all possible unmeasured confounding" from an infinite-dimensional
problem into a finite-dimensional one, over distributions of the response
function variables.

This chapter formalises canonical partitioning and pointwise faithfulness:

* `MeraConstraints.RespFun G val i`: the type of *response functions* of variable
  `i`, i.e. functions `ν(Pa_{W_i}) → ν(W_i)`.  It is a finite type; its
  cardinality is the paper's `|ν(R_{W_i})| = c_{W_i} ^ |ν(Pa_{W_i})|`
  (`RespFun.card`).
* `MeraConstraints.SCM.respMap M i : M.exo i → RespFun G val i`: the paper's
  `φ_W : ν(U_W) → {h : ν(Pa_W) → ν(W)}`, `u_W ↦ F_W(·, u_W)`.
* `MeraConstraints.SCM.proposition1`: for every value `u` of the unmeasured
  influences of `i` there is a *unique* response function `r` with
  `F_W(·, u) = f_W(·, r)`; together with the finiteness of `RespFun` this is
  the reused canonical-partition theorem. The partition itself is exhibited as
  `Setoid.ker (M.respMap i)`, whose quotient is finite
  (`SCM.finite_canonicalPartition`).
* `MeraConstraints.evalR`: recursive evaluation `g^*_{W_i}(r)` of a joint
  response-function assignment, and `SCM.eval_eq_evalR`: the discretised
  model reproduces the original structural model observation by observation.
-/

namespace MeraConstraints

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)

/-!
## Response functions and how many there are

A response function for variable `i` is simply a function from parent
assignments to values.  Counting them gives the paper's cardinality
formula: `c_W^{|ν(Pa_W)|}` for one variable, and the product `ℵ` over all
variables for a joint assignment.  These counts are what make the linear
programs of later chapters finite (if occasionally large).
-/

/-- The type of *response functions* of variable `i`: functions from parent
assignments to values, `ν(Pa_{W_i}) → ν(W_i)`.  The response function
variable `R_{W_i}` of the paper is a random element of this (finite) type. -/
abbrev RespFun (i : Fin n) : Type _ :=
  PaAssign G val i → val i

/-- A joint assignment of response functions to all variables; the paper's
`r ∈ ν(R)`. -/
abbrev RespAssign : Type _ :=
  ∀ i : Fin n, RespFun G val i

namespace RespFun

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- `|ν(R_{W_i})| = c_{W_i} ^ |ν(Pa_{W_i})|`: the cardinality of the response
function variable displayed in Section `sec:respvar` of the manuscript. -/
theorem card (i : Fin n) :
    Fintype.card (RespFun G val i)
      = Fintype.card (val i) ^ ∏ j ∈ G.parents i, Fintype.card (val j) := by
  rw [Fintype.card_fun, PaAssign.card]

/-- `ℵ = |ν(R)| = ∏ᵢ |ν(R_{W_i})|`: the total number of joint response
function assignments. -/
theorem card_respAssign :
    Fintype.card (RespAssign G val)
      = ∏ i, Fintype.card (val i) ^ ∏ j ∈ G.parents i, Fintype.card (val j) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => card G val i

end RespFun

variable {G val}

/-!
## Evaluating a response-function assignment

Fixing a response function for every variable determines the entire
observed world, by the same parent-first recursion as for an SCM: this is
the paper's evaluation map `g*`.  Existence and uniqueness mirror
`SCM.eval` exactly — the discretised model is a structural causal model in
its own right, just one whose "latent" inputs are finite.
-/

/-- Recursive evaluation of a joint response-function assignment: the paper's
`w_i = g^*_{W_i}(r) = f_{W_i}(g^*_{W_{i1}}(r), …, g^*_{W_{ik}}(r), r_{W_i})`.
Well-founded because parents have smaller indices. -/
def evalR (r : RespAssign G val) (i : Fin n) : val i :=
  r i (fun j => evalR r j)
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- The defining equation of `evalR`. -/
theorem evalR_eq (r : RespAssign G val) (i : Fin n) :
    evalR r i = r i (PaAssign.restrict (evalR r) i) := by
  rw [evalR]; rfl

/-- Uniqueness, pointwise form: any solution of the response-function
structural equations agrees with `evalR r` everywhere. -/
theorem evalR_unique_apply (r : RespAssign G val) (w : FullAssign val)
    (hw : ∀ i, w i = r i (PaAssign.restrict w i)) (i : Fin n) :
    w i = evalR r i := by
  rw [hw i, evalR]
  congr 1
  funext j
  exact evalR_unique_apply r w hw j
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- Uniqueness: any solution of the response-function structural equations
is `evalR r`. -/
theorem evalR_unique (r : RespAssign G val) (w : FullAssign val)
    (hw : ∀ i, w i = r i (PaAssign.restrict w i)) :
    w = evalR r :=
  funext fun i => evalR_unique_apply r w hw i

namespace SCM

variable (M : SCM G val)

/-!
## The canonical partition (source paper's Proposition 1)

Given an actual SCM, the map `φ_W` sends each latent value `u` to the
response function `F_W(·, u)` it induces. The reused theorem states
that this map is well-defined and exhaustive: every `u` induces exactly one
response function (existence and uniqueness), and the fibers of `φ_W`
partition the latent space into finitely many classes however wild `ν(U_W)`
may be.  Finally, `eval_eq_evalR` shows the discretisation is *faithful*:
evaluating the original structural equations at `u` produces the same
observed world as evaluating the response functions induced by `u`.
-/

/-- The paper's `φ_W : ν(U_W) → {h : ν(Pa_W) → ν(W)}`, sending a value of
the unmeasured influences of `i` to the response function it induces.  The
*canonical partition* is the partition of `M.exo i` into
the fibers of this map, `Setoid.ker (M.respMap i)`. -/
def respMap (i : Fin n) (u : M.exo i) : RespFun G val i :=
  fun pa => M.F i pa u

/-- Source paper's **Proposition 1** (canonical partitions), existence-and-uniqueness form:
for each variable `W` and each value `u_W ∈ ν(U_W)` of its unmeasured
influences — `ν(U_W)` being an arbitrary type, e.g. continuous or
multivariate — there exists a unique response function
`r_W ∈ ν(R_W)` with `F_W(·, u_W) = f_W(·, r_W)`.  Finiteness of `ν(R_W)`
is the `Fintype (RespFun G val i)` instance together with `RespFun.card`. -/
theorem proposition1 (i : Fin n) (u : M.exo i) :
    ∃! r : RespFun G val i, ∀ pa : PaAssign G val i, M.F i pa u = r pa :=
  ⟨M.respMap i u, fun _ => rfl, fun _ hr => (funext fun pa => (hr pa).symm)⟩

/-- Source paper's **Proposition 1**, partition form: the canonical partition of `ν(U_W)` —
the quotient of `ν(U_W)` by the equivalence `u₁ ∼ u₂ ↔ φ_W u₁ = φ_W u₂` —
has finitely many classes, regardless of the characteristics of `U_W`. -/
theorem finite_canonicalPartition [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
    (i : Fin n) :
    Finite (Quotient (Setoid.ker (M.respMap i))) :=
  have : Finite (Set.range (M.respMap i)) := (Set.toFinite _).to_subtype
  Finite.of_equiv _ (Setoid.quotientKerEquivRange (M.respMap i)).symm

/-- The joint response-function assignment induced by a full exogenous
assignment. -/
def respOf (u : ∀ i, M.exo i) : RespAssign G val :=
  fun i => M.respMap i (u i)

/-- The discretised model is observationally equivalent to the original SCM:
evaluating the structural equations at `u` agrees with evaluating the
response functions induced by `u`.  This is the sense in which the response
function variables "fully characterize the probabilistic causal model". -/
theorem eval_eq_evalR (u : ∀ i, M.exo i) :
    M.eval u = evalR (M.respOf u) :=
  evalR_unique (M.respOf u) (M.eval u) fun i => M.eval_eq u i

end SCM

end MeraConstraints

