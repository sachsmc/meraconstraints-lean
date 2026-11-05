import MeraConstraints.HiddenGraph.Model

/-!
# Strong face splitting: the graphs, and every split model is an original model

This chapter belongs to Proposition 6 (`prop:strong`, Strong Face Splitting). The
proposition assumes Condition 1 (`A1`) only, and splitting can break Condition 2
(`A2`): a new unobserved variable may have a single child, or children contained
in those of another. The manuscript deletes such variables afterwards.
`HiddenGraph.Graph` includes `A2`, so the proposition is formalized on
`RootGraph` instead: the observed DAG together with the observed children of each
unobserved variable, with no further requirement. `RootSCM` is a structural model
on a `RootGraph`.

The original graph (`originalGraph`) has selected unobserved variables with
children `C_i ∪ D` and other unobserved variables with children `other j`. The
split graph (`splitGraph`) replaces each selected variable by one with children
`C_i`, and adds one variable with children `D`. The observed DAG and the other
unobserved variables are unchanged. `Conditions` and `ManuscriptConditions` give
the hypotheses on `C_i`, `D` and `other j`.

The direction "every split model is an original model" is shown by adding a bundled
input. One selected variable is chosen as the anchor. The anchor's input is the pair
(its own `C_i`-input, the `D`-input of the split model). Every other selected
variable carries its `C_i`-input and an unused constant. Each vertex in `D` is a
child of the anchor, so it can read the `D`-input from there, and the original model
computes exactly what the split model computes (`bundledModel_eval`). Only an element
of `K` is needed for this, not the hypotheses of `Conditions`. The reverse direction
is in `StrongFaceReplay` and the chapters after it.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

/-- A hidden variables DAG satisfying Condition 1 (`A1`) but not necessarily
Condition 2 (`A2`): a DAG on the observed variables, and for each unobserved
variable (indexed by `R`) a set of observed children. Unobserved variables have no
parents. -/
structure RootGraph (n : ℕ) (R : Type*) where
  observed : CausalDAG n
  children : R → Finset (Fin n)

/-- A `HiddenGraph.Graph` is a `RootGraph`. -/
def RootGraph.ofGraph {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) : RootGraph n (Fin ℓ) :=
  ⟨G.observed, G.children⟩

variable {n : ℕ} {R : Type*}

/-- A structural model on a `RootGraph`. Each observed variable is computed from
its observed parents, from the unobserved variables that have it as a child, and
from its private noise. The model does not require `A2`. -/
structure RootSCM (G : RootGraph n R) (val : Fin n → Type*) where
  rootValue : R → Type*
  rootNonempty : ∀ r, Nonempty (rootValue r)
  privateNoise : Fin n → Type*
  privateNonempty : ∀ i, Nonempty (privateNoise i)
  F : ∀ i, PaAssign G.observed val i →
    (∀ r : {r : R // i ∈ G.children r}, rootValue r) → privateNoise i → val i

namespace RootSCM

variable {G : RootGraph n R} {val : Fin n → Type*} (M : RootSCM G val)

/-- The structural model on the observed DAG whose input at `i` is the pair
(values of its unobserved parents, private noise). -/
def toSCM : MeraConstraints.SCM G.observed val where
  exo i := (∀ r : {r : R // i ∈ G.children r}, M.rootValue r) × M.privateNoise i
  exoNonempty i := by
    letI : ∀ r : {r : R // i ∈ G.children r}, Nonempty (M.rootValue r) := fun r => M.rootNonempty r
    letI := M.privateNonempty i
    exact inferInstance
  F i pa a := M.F i pa a.1 a.2

def eval (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) : FullAssign val :=
  M.toSCM.eval (fun i => ((fun r => u r), ε i))

theorem eval_eq (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) (i : Fin n) :
    M.eval u ε i = M.F i (PaAssign.restrict (M.eval u ε) i) (fun r => u r) (ε i) :=
  M.toSCM.eval_eq _ i

theorem eval_unique (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i)
    (w : FullAssign val)
    (hw : ∀ i, w i = M.F i (PaAssign.restrict w i) (fun r => u r) (ε i)) :
    w = M.eval u ε := M.toSCM.eval_unique _ w hw

end RootSCM

variable {K J : Type*} (A : CausalDAG n) (C : K → Finset (Fin n))
  (D : Finset (Fin n)) (other : J → Finset (Fin n))

/-- The graph of Proposition 6 before splitting: the selected unobserved variable
`k` has children `C k ∪ D`, and the unobserved variable `j` of the other kind has
children `other j`. -/
def originalGraph : RootGraph n (K ⊕ J) where
  observed := A
  children r := match r with
    | .inl k => C k ∪ D
    | .inr j => other j

/-- The split graph `𝒢*` of Proposition 6: the variable `some k` has children
`C k`, and the new variable `none` has children `D`. It need not satisfy `A2`; the
manuscript removes variables with a single child afterwards. -/
def splitGraph : RootGraph n (Option K ⊕ J) where
  observed := A
  children r := match r with
    | .inl none => D
    | .inl (some k) => C k
    | .inr j => other j

/-- The graphical conditions under which the proofs below run. The sets `C k`
may overlap.

These are slightly **weaker** than the conditions printed in Proposition
`prop:strong`, so the results proved from them are slightly stronger. The
difference is in `crossing_coverage`: the manuscript requires `D ⊆ Chobs(U_j)`
whenever `Chobs(U_j)` meets `⋃ C_i` and is not contained in *any single* `C_i`,
while here it is required only when `Chobs(U_j)` is not contained in the
*union* `⋃ C_i`. An unobserved variable whose children all lie in `⋃ C_i` but
not in one `C_i` is exempt here. `ManuscriptConditions` is the printed version,
and `ManuscriptConditions.toConditions` shows that it implies this one. -/
structure Conditions [Fintype K] : Prop where
  selected_nonempty : Nonempty K
  common_nonempty : D.Nonempty
  disjoint_common : ∀ k, Disjoint (C k) D
  observed_coverage : ∀ k d, d ∈ D → (C k ∪ (C k).biUnion A.parents) ⊆ A.parents d
  crossing_coverage : ∀ j, ((other j) ∩ Finset.univ.biUnion C).Nonempty →
    ¬ other j ⊆ Finset.univ.biUnion C → D ⊆ other j

/-- The conditions of Proposition `prop:strong` as printed in the manuscript.
`k ≥ 1` is implicit there, since `U_1, …, U_k` are chosen to share a child. -/
structure ManuscriptConditions [Fintype K] : Prop where
  selected_nonempty : Nonempty K
  common_nonempty : D.Nonempty
  disjoint_common : ∀ k, Disjoint (C k) D
  /-- Numbered condition 1 of the proposition: `Paobs(C_i) ∪ C_i ⊆ Paobs(d)` for each `d ∈ D` and each `i`. -/
  observed_coverage : ∀ k d, d ∈ D → (C k ∪ (C k).biUnion A.parents) ⊆ A.parents d
  /-- Numbered condition 2 of the proposition: if `Chobs(U_j)` meets `⋃ C_i` and is contained in no `C_i`,
  then `D ⊆ Chobs(U_j)`. -/
  crossing_coverage : ∀ j, ((other j) ∩ Finset.univ.biUnion C).Nonempty →
    (∀ k, ¬ other j ⊆ C k) → D ⊆ other j

/-- The manuscript's conditions imply the ones used in the proofs, so every
result below applies to the graphs covered by Proposition `prop:strong`. -/
theorem ManuscriptConditions.toConditions [Fintype K]
    (h : ManuscriptConditions A C D other) : Conditions A C D other where
  selected_nonempty := h.selected_nonempty
  common_nonempty := h.common_nonempty
  disjoint_common := h.disjoint_common
  observed_coverage := h.observed_coverage
  crossing_coverage := fun j hmeets hnot => h.crossing_coverage j hmeets fun k hk =>
    hnot (hk.trans (Finset.subset_biUnion_of_mem C (Finset.mem_univ k)))

variable {val : Fin n → Type*}
variable (M : RootSCM (splitGraph A C D other) val)

/-- Value of a selected unobserved variable of the original graph: its `C_i`-input
and a copy of the `D`-input. Only the anchor's copy is read. -/
def bundledRootValue : K ⊕ J → Type _
  | .inl k => M.rootValue (.inl (some k)) × M.rootValue (.inl none)
  | .inr j => M.rootValue (.inr j)

def recoverSplitInputs (anchor : K) (u : ∀ r, bundledRootValue A C D other M r) :
    ∀ r, M.rootValue r
  | .inl none => (u (.inl anchor)).2
  | .inl (some k) => (u (.inl k)).1
  | .inr j => u (.inr j)

/-- The split inputs that observed variable `i` reads, recovered from the original
inputs it reads. The `D`-input comes from the anchor. -/
def recoverLocalInputs (anchor : K) (i : Fin n)
    (u : ∀ r : {r : K ⊕ J // i ∈ (originalGraph A C D other).children r},
      bundledRootValue A C D other M r) :
    ∀ r : {r : Option K ⊕ J // i ∈ (splitGraph A C D other).children r}, M.rootValue r
  | ⟨.inl none, hi⟩ => (u ⟨.inl anchor, Finset.mem_union.mpr (Or.inr hi)⟩).2
  | ⟨.inl (some k), hi⟩ => (u ⟨.inl k, Finset.mem_union.mpr (Or.inl hi)⟩).1
  | ⟨.inr j, hi⟩ => u ⟨.inr j, hi⟩

theorem recoverLocalInputs_restrict (anchor : K) (u : ∀ r, bundledRootValue A C D other M r)
    (i : Fin n) :
    recoverLocalInputs A C D other M anchor i (fun r => u r) =
      (fun r : {r : Option K ⊕ J // i ∈ (splitGraph A C D other).children r} =>
        recoverSplitInputs A C D other M anchor u r.val) := by
  funext r
  rcases r with ⟨r, hr⟩
  cases r with
  | inl r => cases r <;> rfl
  | inr r => rfl

/-- The model on the original graph that simulates the split model `M`. -/
def bundledModel (anchor : K) : RootSCM (originalGraph A C D other) val where
  rootValue := bundledRootValue A C D other M
  rootNonempty r := by
    cases r with
    | inl k =>
        change Nonempty (M.rootValue (.inl (some k)) × M.rootValue (.inl none))
        letI := M.rootNonempty (.inl (some k))
        letI := M.rootNonempty (.inl none)
        exact inferInstance
    | inr j => exact M.rootNonempty (.inr j)
  privateNoise := M.privateNoise
  privateNonempty := M.privateNonempty
  F i pa u ε := M.F i pa (recoverLocalInputs A C D other M anchor i u) ε

/-- The bundled model, evaluated at original inputs `u`, gives the observed values
of the split model at the recovered inputs. -/
theorem bundledModel_eval (anchor : K)
    (u : ∀ r, bundledRootValue A C D other M r) (ε : ∀ i, M.privateNoise i) :
    (bundledModel A C D other M anchor).eval u ε =
      M.eval (recoverSplitInputs A C D other M anchor u) ε := by
  symm
  apply RootSCM.eval_unique
  intro i
  rw [M.eval_eq]
  change M.F i _ (fun r => recoverSplitInputs A C D other M anchor u r.val) (ε i) =
    M.F i _ (recoverLocalInputs A C D other M anchor i (fun r => u r)) (ε i)
  rw [recoverLocalInputs_restrict]
  rfl

variable [DecidableEq K]

/-- Turn split inputs into original inputs. The `D`-input goes only to the anchor;
every other selected variable gets the fixed `constant` in that slot, so no random
input is duplicated. -/
def encodeSplitInputs (anchor : K) (constant : M.rootValue (.inl none))
    (u : ∀ r, M.rootValue r) : ∀ r, bundledRootValue A C D other M r
  | .inl k => (u (.inl (some k)), if k = anchor then u (.inl none) else constant)
  | .inr j => u (.inr j)

theorem recover_encode (anchor : K) (constant : M.rootValue (.inl none))
    (u : ∀ r, M.rootValue r) :
    recoverSplitInputs A C D other M anchor (encodeSplitInputs A C D other M anchor constant u) = u := by
  funext r
  cases r with
  | inl r => cases r <;> simp [recoverSplitInputs, encodeSplitInputs]
  | inr r => rfl

/-- For every value `u` of the split inputs, the bundled model at the encoded
inputs gives the same observed values as the split model. -/
theorem split_eval_reproduced (anchor : K) (constant : M.rootValue (.inl none))
    (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    (bundledModel A C D other M anchor).eval (encodeSplitInputs A C D other M anchor constant u) ε =
      M.eval u ε := by
  rw [bundledModel_eval, recover_encode]

end MeraConstraints.HiddenGraph.StrongFaceSplitting
