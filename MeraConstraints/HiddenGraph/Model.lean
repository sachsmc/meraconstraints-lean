import MeraConstraints.HiddenGraph

/-!
# Structural models on a hidden variables DAG

`HiddenGraph.SCM` is a structural model on a `HiddenGraph.Graph`. The value of
each observed variable is a function of its observed parents, of the
unobserved variables that are its parents, and of its private noise. The private
noise of an observed variable is its own independent input, which the graph does
not draw. It corresponds to the response function variable of that variable in
Section "Canonical partitioning" (`sec:respvar`), and it is what gives a
variable in a singleton district a random structural equation once Condition 2
has removed unobserved variables with a single child.

The input types are arbitrary and may be infinite. A structural model alone has
no distribution; independence of the unobserved variables and the private noise
is imposed when a probability law is chosen, in `ProbabilityModel.lean`.

For any c-degree, the model determines the response functions of the observed
variables (`responseProfile`) and evaluating the model is the same as
evaluating those response functions (`eval_eq_evalR`). In a district of
c-degree at most one, all members have the same unobserved parent, so its value
can be a whole profile of response functions. This is the construction used for
`sharedProfileModel` and for the realization direction of Proposition 3
(`prop:complete`).
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type*)

/-- A structural model on the hidden variables DAG `G`: an input type for each
unobserved variable and each observed variable's private noise, and a structural
equation `F` for each observed variable. -/
structure SCM where
  latentValue : Fin ℓ → Type*
  latentNonempty : ∀ u, Nonempty (latentValue u)
  privateNoise : Fin n → Type*
  privateNonempty : ∀ i, Nonempty (privateNoise i)
  F : ∀ i, PaAssign G.observed val i →
    (∀ u : {u : Fin ℓ // i ∈ G.children u}, latentValue u) → privateNoise i → val i

namespace SCM

variable {G val} (M : SCM G val)

/-- The values of the observed variables, computed in the topological order. -/
def eval (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) (i : Fin n) : val i :=
  M.F i (fun j => eval u ε j) (fun j => u j) (ε i)
termination_by i.val
decreasing_by exact G.observed.parents_lt j.2

theorem eval_eq (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) (i : Fin n) :
    M.eval u ε i = M.F i (PaAssign.restrict (M.eval u ε) i) (fun j => u j) (ε i) := by
  rw [eval]
  rfl

/-- The response function of each observed variable for one value of the
unobserved variables and the private noise. -/
def responseProfile (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    RespAssign G.observed val :=
  fun i pa => M.F i pa (fun j => u j) (ε i)

/-- The observed values equal those obtained by evaluating the response
functions. -/
theorem eval_eq_evalR (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    M.eval u ε = evalR (M.responseProfile u ε) :=
  evalR_unique (M.responseProfile u ε) (M.eval u ε) (fun i => M.eval_eq u ε i)

/-- The response function of an observed variable depends only on its
unobserved parents and its private noise. -/
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
## A district with one unobserved variable can have any joint profile

Let the value of the unobserved variable `u` be a complete profile of response
functions. Each child of `u` uses its own coordinate of that profile. Every
other observed variable uses its private noise, which is a response function.
A structural equation may ignore an input that the graph allows it to read.

By `child_of_cDegree_le_one`, every member of a district of c-degree at most one
is a child of `u`. The construction does not fix a distribution, so any
distribution of the profile can be given to `u` later.
-/

variable [∀ i, Nonempty (val i)]

noncomputable def sharedProfileModel (u : Fin ℓ) : SCM G val where
  latentValue := fun _ => RespAssign G.observed val
  latentNonempty := fun _ => inferInstance
  privateNoise := fun i => RespFun G.observed val i
  privateNonempty := fun _ => inferInstance
  F := fun i pa lat ε => if h : i ∈ G.children u then lat ⟨u, h⟩ i pa else ε pa

/-- Every member of the district of `u`, if it has c-degree at most one, uses
its coordinate of the profile that is the value of `u`. -/
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
