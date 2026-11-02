import MeraConstraints.SCM.ResponseFunction
import MeraConstraints.Probability.Finite
import Mathlib.Data.Matrix.Mul

/-!
# District response functions and compatibility matrices

A district has internal observed parents and fixed external observed parents.
Its members share one unrestricted latent input. A response profile assigns
each member a function of precisely its parents. Recursion follows the
topological ordering, including when external parents are also descendants
of earlier district members in the full graph: here they are intervened on.

The finite latent reduction is pointwise, so it does not require the original
latent state space to be finite. Probability vectors enter only afterwards.
The observable identification of these kernels requires a separate Markov
argument; it is not part of the definition of a district kernel.
-/

namespace MeraConstraints
namespace District

variable {n m : ℕ}

/-- Internal DAG and external parent sets of a district. -/
structure Graph (n m : ℕ) where
  internal : CausalDAG n
  external : Fin n → Finset (Fin m)

variable (G : Graph n m) (val : Fin n → Type*) (extVal : Fin m → Type*)

abbrev ExternalAssign (i : Fin n) :=
  ∀ j : {j : Fin m // j ∈ G.external i}, extVal j

/-- All deterministic mechanisms allowed by the district parent sets. -/
abbrev Profile :=
  ∀ i, PaAssign G.internal val i → ExternalAssign G extVal i → val i

/-- Solve the district equations with its external parents fixed to `e`. -/
def eval (r : Profile G val extVal) (e : FullAssign extVal) (i : Fin n) : val i :=
  r i (fun j => eval r e j) (fun j => e j)
termination_by i.val
decreasing_by exact G.internal.parents_lt j.2

theorem eval_eq (r : Profile G val extVal) (e : FullAssign extVal) (i : Fin n) :
    eval G val extVal r e i =
      r i (PaAssign.restrict (eval G val extVal r e) i) (fun j => e j) := by
  rw [eval]
  rfl

/-- No second solution of the same structural equations exists. -/
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

/-- A district subset contains the internal parents of each of its members.
Iterating this condition also includes every internal ancestor. -/
def ClosedInDistrict (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ G.internal.parents i, j ∈ S

/-- A closed subset's outputs depend only on the external parents of that
subset. This is the deterministic step behind the margin equalities of sets closed in the district. -/
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

/-- An arbitrary shared latent input induces a profile. No finiteness of `U`
is assumed. Its fibers are the canonical finite partition of the latent space. -/
def responseMap {U : Type*}
    (F : ∀ i, PaAssign G.internal val i → ExternalAssign G extVal i → U → val i)
    (u : U) : Profile G val extVal :=
  fun i pa ea => F i pa ea u

/-- Replacing the latent input by its profile preserves every solution. -/
theorem responseMap_faithful {U : Type*}
    (F : ∀ i, PaAssign G.internal val i → ExternalAssign G extVal i → U → val i)
    (u : U) (e : FullAssign extVal) (w : FullAssign val)
    (hw : ∀ i, w i = F i (PaAssign.restrict w i) (fun j => e j) u) :
    w = eval G val extVal (responseMap G val extVal F u) e :=
  eval_unique G val extVal _ e w hw

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ j, Fintype (extVal j)] [∀ j, DecidableEq (extVal j)]

/-- The response-profile space is finite, even for arbitrary original latents. -/
theorem card_profile :
    Fintype.card (Profile G val extVal) =
      ∏ i, (Fintype.card (val i) ^ Fintype.card (ExternalAssign G extVal i)) ^
        Fintype.card (PaAssign G.internal val i) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_fun, Fintype.card_fun]

/-- Algorithm's binary matrix, indexed by `(external input, district output)`. -/
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

/-- Interventional district kernel induced by a profile distribution. -/
def kernel (q : Profile G val extVal → ℝ) (e : FullAssign extVal) :
    FullAssign val → ℝ :=
  pushforward (fun r => eval G val extVal r e) q

/-- Algebraic part of Proposition `prop:ident`: `p = B r`.
This does not yet identify `p` with a product of observational conditionals. -/
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

/-- Distribution of the outputs in a district subset under fixed inputs. -/
def marginal (S : Finset (Fin n)) (q : Profile G val extVal → ℝ)
    (e : FullAssign extVal) : (∀ i : {i // i ∈ S}, val i) → ℝ :=
  pushforward (fun r => fun i => eval G val extVal r e i) q

/-- Parent-closed margin equalities hold for every finite response-profile mixture.
For globally ancestor-closed sets these are equations (O); for sets closed only
in the district they can instead be nontrivial Verma constraints (Section 3.3). -/
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

