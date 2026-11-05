import MeraConstraints.SCM.ResponseFunction
import MeraConstraints.Probability.Finite
import Mathlib.Data.Matrix.Mul

/-!
# Districts, profiles and the matrix `B`

This chapter gives the construction behind Proposition 1 (`prop:ident`) for one
district, with the members indexed by `Fin n` and the external parents by
`Fin m`. Each member has internal parents among the members (`G.internal`) and
external parents (`G.external`). A profile gives each member a response function
of its parents. `eval` solves the members' equations recursively with the
external parents fixed to `e`. The external parents may be descendants of earlier
members in the full graph; they are intervened on, so their values are given.

`responseMap` sends a value of an input `U` shared by the members to a profile, and
a solution of the equations with that input is the evaluation of the profile
(`responseMap_faithful`). The type `U` may be infinite, but there are finitely
many profiles (`card_profile`). `compatibility` is the matrix `B`, with a `1`
where the profile gives the members the values of the row, which has the external
values first. For a distribution `q` of the profiles,
`kernel q e` is the distribution of the members' values with the external
parents fixed to `e`, and `kernel_eq_mulVec` shows `p = B r`. That this equals the
product of observed conditional probabilities defining the district factor `Pdo`
uses the conditional independencies implied by the graph, and is not part of this
chapter.

`marginal_eq_of_closedInDistrict` shows that the margin of a set closed in the
district depends on `e` only through the external parents of that set. For sets
closed in the graph these are equations (O) of the subsection on nontrivial
constraints (`sec:nontriv`).

This chapter is self-contained. The main results use the `CompactDistrict`
chapter, which develops the matrix `B` with the members and external parents as
subtypes of the observed variables.
-/

namespace MeraConstraints
namespace District

variable {n m : ℕ}

/-- A district: the DAG on its `n` members, and for each member its set of
external parents, among `m` external variables. -/
structure Graph (n m : ℕ) where
  internal : CausalDAG n
  external : Fin n → Finset (Fin m)

variable (G : Graph n m) (val : Fin n → Type*) (extVal : Fin m → Type*)

abbrev ExternalAssign (i : Fin n) :=
  ∀ j : {j : Fin m // j ∈ G.external i}, extVal j

/-- A profile: for each member, a response function of its internal and external
parents. -/
abbrev Profile :=
  ∀ i, PaAssign G.internal val i → ExternalAssign G extVal i → val i

/-- The values of the members given by the profile `r`, with the external parents
fixed to `e`. -/
def eval (r : Profile G val extVal) (e : FullAssign extVal) (i : Fin n) : val i :=
  r i (fun j => eval r e j) (fun j => e j)
termination_by i.val
decreasing_by exact G.internal.parents_lt j.2

theorem eval_eq (r : Profile G val extVal) (e : FullAssign extVal) (i : Fin n) :
    eval G val extVal r e i =
      r i (PaAssign.restrict (eval G val extVal r e) i) (fun j => e j) := by
  rw [eval]
  rfl

/-- Any joint value of the members satisfying the equations of the profile `r`,
with external parents `e`, agrees with `eval r e` at every member. -/
theorem eval_unique_apply (r : Profile G val extVal) (e : FullAssign extVal)
    (w : FullAssign val)
    (hw : ∀ i, w i = r i (PaAssign.restrict w i) (fun j => e j)) (i : Fin n) :
    w i = eval G val extVal r e i := by
  rw [hw i, eval]
  congr 1
  funext j
  exact eval_unique_apply r e w hw j
termination_by i.val
decreasing_by exact G.internal.parents_lt j.2

theorem eval_unique (r : Profile G val extVal) (e : FullAssign extVal)
    (w : FullAssign val)
    (hw : ∀ i, w i = r i (PaAssign.restrict w i) (fun j => e j)) :
    w = eval G val extVal r e :=
  funext (eval_unique_apply G val extVal r e w hw)

/-- A set `S` of members is closed in the district: it contains the internal
parents of each of its members, hence every ancestor reached by a path inside
the district. -/
def ClosedInDistrict (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ G.internal.parents i, j ∈ S

/-- For a set closed in the district, the values of its members depend on `e` only
through the external parents of the set. -/
theorem eval_eq_on_closedInDistrict (S : Finset (Fin n)) (hS : ClosedInDistrict G S)
    (r : Profile G val extVal) (e e' : FullAssign extVal)
    (he : ∀ i ∈ S, ∀ j : {j : Fin m // j ∈ G.external i}, e j = e' j)
    (i : Fin n) (hi : i ∈ S) :
    eval G val extVal r e i = eval G val extVal r e' i := by
  rw [eval, eval]
  congr 1
  · funext j
    exact eval_eq_on_closedInDistrict S hS r e e' he j (hS i hi j j.2)
  · funext j
    exact he i hi j
termination_by i.val
decreasing_by exact G.internal.parents_lt j.2

/-- A value `u` of a shared input induces a profile, with `U` any type. Its fibers
are the canonical partition of `U`. -/
def responseMap {U : Type*}
    (F : ∀ i, PaAssign G.internal val i → ExternalAssign G extVal i → U → val i)
    (u : U) : Profile G val extVal :=
  fun i pa ea => F i pa ea u

/-- A joint value that solves the structural equations with input `u` is the
evaluation of the profile induced by `u`. -/
theorem responseMap_faithful {U : Type*}
    (F : ∀ i, PaAssign G.internal val i → ExternalAssign G extVal i → U → val i)
    (u : U) (e : FullAssign extVal) (w : FullAssign val)
    (hw : ∀ i, w i = F i (PaAssign.restrict w i) (fun j => e j) u) :
    w = eval G val extVal (responseMap G val extVal F u) e :=
  eval_unique G val extVal _ e w hw

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ j, Fintype (extVal j)] [∀ j, DecidableEq (extVal j)]

/-- The set of profiles is finite, with the number of elements given here. -/
theorem card_profile :
    Fintype.card (Profile G val extVal) =
      ∏ i, (Fintype.card (val i) ^ Fintype.card (ExternalAssign G extVal i)) ^
        Fintype.card (PaAssign G.internal val i) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_fun, Fintype.card_fun]

/-- The compatibility matrix `B` of the district. The entry at row `(e, v)` and
profile `r` is `1` when `eval r e = v`, and `0` otherwise. The row lists the
external values `e` first. -/
def compatibility : Matrix (FullAssign extVal × FullAssign val)
    (Profile G val extVal) ℝ :=
  fun x r => if eval G val extVal r x.1 = x.2 then 1 else 0

omit [∀ i, Fintype (val i)] [∀ j, Fintype (extVal j)]
  [∀ j, DecidableEq (extVal j)] in
theorem compatibility_binary (x : FullAssign extVal × FullAssign val)
    (r : Profile G val extVal) :
    compatibility G val extVal x r = 0 ∨ compatibility G val extVal x r = 1 := by
  unfold compatibility
  split <;> simp

/-- The distribution of the members' values when the external parents are set to
`e`, for a distribution `q` of the profiles: the probability of `V₁ = v₁` under
`Do(V₂ = e)`. -/
def kernel (q : Profile G val extVal → ℝ) (e : FullAssign extVal) :
    FullAssign val → ℝ :=
  pushforward (fun r => eval G val extVal r e) q

/-- The identity `p = B r` of Proposition 1 (`prop:ident`): the entry of `kernel`
at `(e, w)` is the entry of `B q` at row `(e, w)`. -/
theorem kernel_eq_mulVec (q : Profile G val extVal → ℝ)
    (e : FullAssign extVal) (w : FullAssign val) :
    kernel G val extVal q e w = (compatibility G val extVal).mulVec q (e, w) := by
  classical
  simp [kernel, pushforward, compatibility, Matrix.mulVec, dotProduct,
    Finset.sum_filter, ite_mul]

theorem kernel_mem_stdSimplex (q : Profile G val extVal → ℝ)
    (hq : q ∈ stdSimplex ℝ (Profile G val extVal)) (e : FullAssign extVal) :
    kernel G val extVal q e ∈ stdSimplex ℝ (FullAssign val) :=
  pushforward_mem_stdSimplex _ q hq

/-- The distribution of the values of the members in `S`, when the external
parents are set to `e`. -/
def marginal (S : Finset (Fin n)) (q : Profile G val extVal → ℝ)
    (e : FullAssign extVal) : (∀ i : {i // i ∈ S}, val i) → ℝ :=
  pushforward (fun r => fun i => eval G val extVal r e i) q

/-- For a set closed in the district, the margin over `S` is the same at any two
values `e`, `e'` of the external parents that agree on the external parents of `S`.
For sets closed in the graph these are equations (O). For sets closed only in the
district they can be nontrivial, Verma-type constraints. -/
theorem marginal_eq_of_closedInDistrict (S : Finset (Fin n)) (hS : ClosedInDistrict G S)
    (q : Profile G val extVal → ℝ) (e e' : FullAssign extVal)
    (he : ∀ i ∈ S, ∀ j : {j : Fin m // j ∈ G.external i}, e j = e' j) :
    marginal G val extVal S q e = marginal G val extVal S q e' := by
  unfold marginal
  apply congrArg (fun f => pushforward f q)
  funext r i
  exact eval_eq_on_closedInDistrict G val extVal S hS r e e' he i i.2

end District
end MeraConstraints

