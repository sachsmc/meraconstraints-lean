import MeraConstraints.HiddenGraph.Model
import Mathlib.Logic.Function.Basic

/-!
# Adding an edge: constructions on structural models

Proposition 5 (`prop:hlp`) says that the edge `a → b` between observed variables
can be added to a hidden variables DAG without changing the constraints, when
the parents of `a` are parents of `b` and `a` and `b` have a common unobserved
parent. `addEdge G a b hab` is the graph with the edge added, where `a < b` in
the topological order.

This file gives the two constructions on structural models. Forward direction
(`ignoreEdge`): a structural model on `G` is a structural model on the graph with
the edge, whose equation for `b` ignores `a`; it has the same values
(`eval_ignoreEdge`). Reverse direction (`absorb`): a model on the graph with the
edge becomes a model on `G` by moving the private noise of `a` into the common
unobserved parent `s`. Then `b` recomputes the value of `a` from the parents of
`a`, which it also sees, the unobserved parents of `a`, and the moved noise, so it
no longer needs `a` itself. The values are the same (`eval_absorb`, in
`HLPEvaluation.lean`).

These are statements about values for each value of the inputs. That the
distributions generated are the same, with independent inputs, is shown in
`HLPInputs.lean`, `HLPMeasure.lean` and `Completeness/HLP.lean`.
-/

namespace MeraConstraints.HiddenGraph.SCM

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type*}

/-- The values of the observed variables are the unique solution of the
structural equations. -/
theorem eval_unique (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (fun j => u j) (ε i)) :
    w = M.eval u ε := by
  rw [eval_eq_evalR]
  exact evalR_unique (M.responseProfile u ε) w hw

end MeraConstraints.HiddenGraph.SCM

namespace MeraConstraints.HiddenGraph.HLP

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (a b : Fin n) (hab : a < b)

/-- The graph `G` with the edge `a → b` added. The unobserved variables and
their children are unchanged. The hypothesis `hab : a < b` keeps the topological
order. -/
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

/-- A value of the parents in the graph with the edge, restricted to the parents
in `G`. -/
def forgetParent (i : Fin n) (pa : PaAssign (addEdge G a b hab).observed val i) :
    PaAssign G.observed val i :=
  fun j => pa ⟨j, parent_mem_addEdge G a b hab j.property⟩

/-- The structural model on the graph with the edge in which every structural
equation ignores the added parent. It has the same inputs as `M`. -/
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

/-- A fixed joint value of the observed variables, namely the values of `M` at
some fixed value of its inputs, which exist because the input types are
nonempty. -/
noncomputable def baseline : FullAssign val :=
  M.eval (fun j => Classical.choice (M.latentNonempty j))
    (fun i => Classical.choice (M.privateNonempty i))

/-- A joint value of the observed variables that agrees with `pa` on the parents
of `i` in `G` and with `baseline` elsewhere. -/
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

/-- The structural model on `G` obtained by moving the private noise of `a` into
the common unobserved parent `s`, so that `b` recomputes the value of `a`. Each
unobserved variable gets an extra coordinate of the type of the private noise of
`a`; only that of `s` is used (`absorbLatents`). -/
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

/-- The inputs of `absorb`: the extra coordinate of `s` is the private noise of
`a`, and the extra coordinates of the other unobserved variables are constant. -/
noncomputable def absorbLatents (s : Fin ℓ) (u : ∀ j, M.latentValue j)
    (ε : ∀ i, M.privateNoise i) : ∀ j, M.latentValue j × M.privateNoise a :=
  fun j => (u j, if j = s then ε a else Classical.choice (M.privateNonempty a))

/-- The private noise of `absorb`: that of `a` is replaced by a constant, since
it has been moved. -/
noncomputable def absorbPrivate (ε : ∀ i, M.privateNoise i) : ∀ i, M.privateNoise i :=
  fun i => if i = a then Classical.choice (M.privateNonempty i) else ε i

end Absorption
end MeraConstraints.HiddenGraph.HLP
