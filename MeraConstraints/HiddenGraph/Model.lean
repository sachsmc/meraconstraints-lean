import MeraConstraints.HiddenGraph

/-!
# Structural models with explicit latent parent restrictions

A hidden-variable graph alone does not assign a probability law. Its
structural mechanisms may inspect only their observed parents, the latent
roots that have them as children, and a private disturbance. The private
disturbance is essential after Condition `A2` removes single-child hidden
vertices: an observed singleton district still has an arbitrary stochastic
mechanism. It is represented by a response variable even when it has no
listed latent parent, as in the definition in `sec:respvar`.

The input types here are arbitrary, possibly infinite. A probability law
on these inputs must impose the intended independence: latent roots and
private disturbances are mutually independent. That probabilistic assertion
is deliberately not replaced by a graph-theoretic claim about exogeneity.

The response reduction is pointwise and works for any c-degree. It does
**not** permit an unrestricted joint law of all response variables: at
higher c-degree, the latent parent restrictions still constrain that law.
The final construction explains why a degree-one district is different:
every member can read one common root, whose value may be its entire joint
response profile. This is the realization direction used by `prop:complete`.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type*)

/-- Parent-restricted structural mechanisms on the full hidden graph.
Latent input types remain arbitrary. Private inputs represent the implicit
node-specific randomness retained when one-child latent vertices are removed. -/
structure SCM where
  latentValue : Fin ℓ → Type*
  latentNonempty : ∀ u, Nonempty (latentValue u)
  privateNoise : Fin n → Type*
  privateNonempty : ∀ i, Nonempty (privateNoise i)
  F : ∀ i, PaAssign G.observed val i →
    (∀ u : {u : Fin ℓ // i ∈ G.children u}, latentValue u) → privateNoise i → val i

namespace SCM

variable {G val} (M : SCM G val)

/-- Recursive solution of the full structural model. -/
def eval (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) (i : Fin n) : val i :=
  M.F i (fun j => eval u ε j) (fun j => u j) (ε i)
termination_by i.val
decreasing_by exact G.observed.parents_lt j.2

theorem eval_eq (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) (i : Fin n) :
    M.eval u ε i = M.F i (PaAssign.restrict (M.eval u ε) i) (fun j => u j) (ε i) := by
  rw [eval]
  rfl

/-- The profile obtained from one complete input assignment; its coordinates
are functions of observed parents, not of arbitrary observed variables. -/
def responseProfile (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    RespAssign G.observed val :=
  fun i pa => M.F i pa (fun j => u j) (ε i)

/-- Faithfulness of the response-variable transformation in the absence of
interventions. It does not assert independence of profile coordinates. -/
theorem eval_eq_evalR (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    M.eval u ε = evalR (M.responseProfile u ε) :=
  evalR_unique (M.responseProfile u ε) (M.eval u ε) (fun i => M.eval_eq u ε i)

/-- A node can inspect only the listed latent parents. Thus if these inputs
and its private input agree, its response function is unchanged. -/
theorem responseProfile_eq_at_of_inputs_eq
    (u u' : ∀ j, M.latentValue j) (ε ε' : ∀ i, M.privateNoise i) (i : Fin n)
    (hu : ∀ j : {j : Fin ℓ // i ∈ G.children j}, u j = u' j)
    (hε : ε i = ε' i) :
    M.responseProfile u ε i = M.responseProfile u' ε' i := by
  funext pa
  unfold responseProfile
  congr 1
  · funext j
    exact hu j

end SCM

/-!
## Realizing every joint profile of a one-latent district

Choose the value of the common latent root to be a full response profile.
Its children use the appropriate coordinate of that profile. Other observed
vertices use their own private response functions. Unused latent inputs are
allowed: graph compatibility restricts which arguments a mechanism may use,
but never requires dependence on every permitted argument.

The child/component equivalence proved in `HiddenGraph.lean` is what allows
the following construction to cover every member of a degree-one district.
No distribution is fixed in this construction, so any joint profile law
can subsequently be chosen for the common root. The other root inputs and
private disturbances may be degenerate independent variables.
-/

variable [∀ i, Nonempty (val i)]

noncomputable def sharedProfileModel (u : Fin ℓ) : SCM G val where
  latentValue := fun _ => RespAssign G.observed val
  latentNonempty := fun _ => inferInstance
  privateNoise := fun i => RespFun G.observed val i
  privateNonempty := fun _ => inferInstance
  F := fun i pa lat ε => if h : i ∈ G.children u then lat ⟨u, h⟩ i pa else ε pa

/-- Every observed member of the degree-one district reads its coordinate
from the common latent profile, with no restriction on the joint profile. -/
theorem sharedProfileModel_on_district (u : Fin ℓ) (i : Fin n)
    (hdegree : cDegree G (.inr u) ≤ 1)
    (hui : Connected G (.inr u) (.inl i))
    (pa : PaAssign G.observed val i)
    (lat : ∀ _j : {j : Fin ℓ // i ∈ G.children j}, RespAssign G.observed val)
    (ε : RespFun G.observed val i) :
    (sharedProfileModel G val u).F i pa lat ε =
      lat ⟨u, child_of_cDegree_le_one G u i hdegree hui⟩ i pa := by
  simp [sharedProfileModel, child_of_cDegree_le_one G u i hdegree hui]

end MeraConstraints.HiddenGraph
