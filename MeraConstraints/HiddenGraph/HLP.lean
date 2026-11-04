import MeraConstraints.HiddenGraph.Model
import Mathlib.Logic.Function.Basic

/-!
# The HLP edge transformation: structural constructions

Proposition `prop:hlp` adds an observed edge `a → b` when every parent of `a`
is a parent of `b` and the two vertices share a latent parent. The observed
parent condition and the latent parent condition are recorded separately.

Adding the edge first permits every original mechanism simply to ignore the
extra argument. In the reverse construction, the private disturbance of `a`
is included in the shared latent input. Vertex `b` can reconstruct the value
of `a` from its own available observed/latent parents and that disturbance,
so its mechanism no longer needs a direct argument from `a`.

This chapter concerns actual structural mechanisms and pointwise recursive
evaluation, with arbitrary latent/private input types. It does not define
model equivalence as a premise. The probability-law equivalence additionally
requires the moved private input to be grouped with the chosen latent root,
and the now-unused private input to be constant, preserving full original
input independence. `HiddenGraph.HLPMeasure`, `HiddenGraph.HLPInputs` and
`Completeness.HLP` establish that probability transport for arbitrary
original measurable exogenous spaces and finite observed state spaces.
The ignore-edge evaluation theorem is proved below. `HiddenGraph.HLPEvaluation`
proves that the explicit reverse absorption preserves the complete observed
evaluation at every original input realization. The probability-model
equivalence is proved separately from that pointwise identity.
-/

namespace MeraConstraints.HiddenGraph.SCM

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type*}

/-- Uniqueness of the original hidden-graph structural equations. -/
theorem eval_unique (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (fun j => u j) (ε i)) :
    w = M.eval u ε := by
  rw [eval_eq_evalR]
  exact evalR_unique (M.responseProfile u ε) w hw

end MeraConstraints.HiddenGraph.SCM

namespace MeraConstraints.HiddenGraph.HLP

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (a b : Fin n) (hab : a < b)

/-- Add the specified observed arrow, leaving all latent child sets unchanged.
When the arrow was already present this is harmless; the paper applies it to
an absent edge. `hab` ensures the added arrow respects the global order. -/
def addEdge : HiddenGraph.Graph n ℓ where
  observed := {
    parents := fun i => if i = b then insert a (G.observed.parents i) else G.observed.parents i
    parents_lt := by
      intro i j hj
      by_cases hi : i = b
      · subst i
        have hj' : j = a ∨ j ∈ G.observed.parents b := by
          simpa using hj
        rcases hj' with hja | hjold
        · subst j
          exact hab
        · exact G.observed.parents_lt hjold
      · have hj' : j ∈ G.observed.parents i := by simpa only [if_neg hi] using hj
        exact G.observed.parents_lt hj' }
  children := G.children
  two_le_card := G.two_le_card
  child_antichain := G.child_antichain

@[simp] theorem addEdge_children (j : Fin ℓ) : (addEdge G a b hab).children j = G.children j := rfl

theorem parent_mem_addEdge {i j : Fin n} (h : j ∈ G.observed.parents i) :
    j ∈ (addEdge G a b hab).observed.parents i := by
  by_cases hi : i = b
  · subst i
    simpa [addEdge] using (Finset.mem_insert_of_mem h : j ∈ insert a (G.observed.parents b))
  · simpa [addEdge, hi] using h

theorem parent_addEdge_of_ne {i j : Fin n} (hi : i ≠ b)
    (h : j ∈ (addEdge G a b hab).observed.parents i) : j ∈ G.observed.parents i := by
  simpa only [addEdge, if_neg hi] using h

theorem parent_addEdge_at_b {j : Fin n}
    (h : j ∈ (addEdge G a b hab).observed.parents b) :
    j = a ∨ j ∈ G.observed.parents b := by
  simpa [addEdge] using h

variable {G a b hab} {val : Fin n → Type*}

/-- Forget the added argument when embedding an original mechanism. -/
def forgetParent (i : Fin n) (pa : PaAssign (addEdge G a b hab).observed val i) :
    PaAssign G.observed val i :=
  fun j => pa ⟨j, parent_mem_addEdge G a b hab j.property⟩

/-- Forward structural inclusion: every original mechanism can ignore the
additional observed parent. The original input types are retained exactly. -/
def ignoreEdge (M : HiddenGraph.SCM G val) (a b : Fin n) (hab : a < b) :
    HiddenGraph.SCM (addEdge G a b hab) val where
  latentValue := M.latentValue
  latentNonempty := M.latentNonempty
  privateNoise := M.privateNoise
  privateNonempty := M.privateNonempty
  F := fun i pa u ε => M.F i (forgetParent i pa) u ε

theorem eval_ignoreEdge (M : HiddenGraph.SCM G val) (a b : Fin n) (hab : a < b)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    (ignoreEdge M a b hab).eval u ε = M.eval u ε := by
  symm
  apply HiddenGraph.SCM.eval_unique
  intro i
  exact M.eval_eq u ε i

section Absorption

variable (M : HiddenGraph.SCM (addEdge G a b hab) val)

/-- A fixed full assignment exists because the model's root/private inputs
are nonempty. It fills irrelevant coordinates of a partial parent assignment. -/
noncomputable def baseline : FullAssign val :=
  M.eval (fun j => Classical.choice (M.latentNonempty j))
    (fun i => Classical.choice (M.privateNonempty i))

/-- Extend only the permitted observed parent arguments by fixed constants.
The extension cannot introduce dependence on any additional observed input. -/
noncomputable def parentWitness (i : Fin n) (pa : PaAssign G.observed val i) : FullAssign val :=
  fun j => if hj : j ∈ G.observed.parents i then pa ⟨j, hj⟩ else baseline M j

theorem parentWitness_on_parent (i : Fin n) (pa : PaAssign G.observed val i)
    (j : {j : Fin n // j ∈ G.observed.parents i}) : parentWitness M i pa j = pa j := by
  simp [parentWitness, j.property]

theorem parentWitness_restrict_of_ne (w : FullAssign val) (i : Fin n) (hi : i ≠ b) :
    PaAssign.restrict (G := (addEdge G a b hab).observed)
      (parentWitness M i (PaAssign.restrict (G := G.observed) w i)) i =
      PaAssign.restrict (G := (addEdge G a b hab).observed) w i := by
  funext j
  have hj := parent_addEdge_of_ne G a b hab hi j.property
  simp [PaAssign.restrict, parentWitness, hj]

theorem parentWitness_b_restrict_a (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (w : FullAssign val) :
    PaAssign.restrict (G := (addEdge G a b hab).observed)
      (parentWitness M b (PaAssign.restrict (G := G.observed) w b)) a =
      PaAssign.restrict (G := (addEdge G a b hab).observed) w a := by
  funext j
  have hj := hpa (parent_addEdge_of_ne G a b hab (ne_of_lt hab) j.property)
  simp [PaAssign.restrict, parentWitness, hj]

theorem updatedWitness_restrict_b (w : FullAssign val) (x : val a) (hx : x = w a) :
    PaAssign.restrict (G := (addEdge G a b hab).observed)
      (Function.update (parentWitness M b (PaAssign.restrict (G := G.observed) w b)) a x) b =
      PaAssign.restrict (G := (addEdge G a b hab).observed) w b := by
  subst x
  funext j
  by_cases hja : j.val = a
  · change Function.update _ a (w a) j.val = w j.val
    rw [hja]
    simp
  · have hj := (parent_addEdge_at_b G a b hab j.property).resolve_left hja
    simp [PaAssign.restrict, Function.update_of_ne hja, parentWitness, hj]

/-- Move `a`'s private disturbance into a chosen common latent input. Every
root carries the same product type for simplicity; only the chosen root's
extra coordinate will vary in the input embedding below. -/
noncomputable def absorb
    (hLat : ∀ j : Fin ℓ, a ∈ G.children j → b ∈ G.children j)
    (s : Fin ℓ) (hsa : a ∈ G.children s) (hsb : b ∈ G.children s) : HiddenGraph.SCM G val where
  latentValue := fun j => M.latentValue j × M.privateNoise a
  latentNonempty := fun j => ⟨Classical.choice (M.latentNonempty j),
    Classical.choice (M.privateNonempty a)⟩
  privateNoise := M.privateNoise
  privateNonempty := M.privateNonempty
  F := fun i pa u ε =>
    if hia : i = a then by
      subst i
      exact M.F a (PaAssign.restrict (parentWitness M a pa) a)
        (fun j => (u j).1) (u ⟨s, hsa⟩).2
    else if hib : i = b then by
      subst i
      let z := parentWitness M b pa
      let va := M.F a (PaAssign.restrict z a)
        (fun j => (u ⟨j, hLat j j.property⟩).1) (u ⟨s, hsb⟩).2
      exact M.F b (PaAssign.restrict (Function.update z a va) b) (fun j => (u j).1) ε
    else M.F i (PaAssign.restrict (parentWitness M i pa) i) (fun j => (u j).1) ε

/-- The new latent inputs. Only the shared root receives the actual moved
private disturbance; the extra coordinates at all other roots are constants. -/
noncomputable def absorbLatents (s : Fin ℓ) (u : ∀ j, M.latentValue j)
    (ε : ∀ i, M.privateNoise i) : ∀ j, M.latentValue j × M.privateNoise a :=
  fun j => (u j, if j = s then ε a else Classical.choice (M.privateNonempty a))

/-- `a`'s original private input is no longer used and is fixed to a constant. -/
noncomputable def absorbPrivate (ε : ∀ i, M.privateNoise i) : ∀ i, M.privateNoise i :=
  fun i => if i = a then Classical.choice (M.privateNonempty i) else ε i

end Absorption
end MeraConstraints.HiddenGraph.HLP
