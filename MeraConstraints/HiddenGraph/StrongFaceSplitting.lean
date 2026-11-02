import MeraConstraints.HiddenGraph.Model

/-!
# Strong face splitting: the original/split mechanism embedding

Proposition `prop:strong` is stated for graphs satisfying `A1` only. Its raw
split graph can contain one-child, empty-child, or dominated latent vertices;
the manuscript removes these afterwards to restore `A2`. Accordingly this
chapter first provides an `A1`-only root graph rather than incorrectly forcing
the intermediate split graph into `HiddenGraph.Graph`, which includes `A2`.

The original selected roots have child sets `C_i ∪ D`; the split roots have
child sets `C_i` and one additional common child set `D`. Unselected root
child sets and all observed arrows are identical. The manuscript's two
strong splitting hypotheses are recorded literally in `Conditions`.

We prove the **easy embedding direction** constructively: every structural
mechanism on the split graph can be simulated on the original graph. Choose
one selected root as anchor, bundle the common-D input into that original
root, and let every other selected root carry only its own C-input plus an
ignored constant component. All new mechanisms read only permitted parents.
Recursive evaluation agrees pointwise after this input encoding.

This direction does not use the strong splitting hypotheses; they are needed
for the difficult reverse simulation. No marginal-model equivalence or
probability transport is claimed by these pointwise theorems. In particular,
an arbitrary coupling of encoded inputs must not be called independent.
The anchor makes the intended nonempty selected family explicit (`k ≥ 1`).
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

/-- An `A1` graph, with arbitrary root child sets before the `A2` reductions. -/
structure RootGraph (n : ℕ) (R : Type*) where
  observed : CausalDAG n
  children : R → Finset (Fin n)

/-- Every graph in the existing development is an `A1` root graph. -/
def RootGraph.ofGraph {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) : RootGraph n (Fin ℓ) :=
  ⟨G.observed, G.children⟩

variable {n : ℕ} {R : Type*}

/-- Parent-restricted structural mechanisms on an `A1` graph, without imposing
the child-antichain or two-child restrictions that splitting can destroy. -/
structure RootSCM (G : RootGraph n R) (val : Fin n → Type*) where
  rootValue : R → Type*
  rootNonempty : ∀ r, Nonempty (rootValue r)
  privateNoise : Fin n → Type*
  privateNonempty : ∀ i, Nonempty (privateNoise i)
  F : ∀ i, PaAssign G.observed val i →
    (∀ r : {r : R // i ∈ G.children r}, rootValue r) → privateNoise i → val i

namespace RootSCM

variable {G : RootGraph n R} {val : Fin n → Type*} (M : RootSCM G val)

/-- Reuse the checked observed-DAG recursion, retaining the latent parent mask. -/
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

/-- Original selected roots have the common children `D` in addition to `C_i`. -/
def originalGraph : RootGraph n (K ⊕ J) where
  observed := A
  children r := match r with
    | .inl k => C k ∪ D
    | .inr j => other j

/-- Raw split graph, prior to removal of one-child or redundant latent roots. -/
def splitGraph : RootGraph n (Option K ⊕ J) where
  observed := A
  children r := match r with
    | .inl none => D
    | .inl (some k) => C k
    | .inr j => other j

/-- Exact graphical conditions of Proposition `prop:strong`. These hypotheses
are not replaced by a claimed model equivalence. Overlaps between C-sets are allowed. -/
structure Conditions [Fintype K] : Prop where
  selected_nonempty : Nonempty K
  common_nonempty : D.Nonempty
  disjoint_common : ∀ k, Disjoint (C k) D
  observed_coverage : ∀ k d, d ∈ D → (C k ∪ (C k).biUnion A.parents) ⊆ A.parents d
  crossing_coverage : ∀ j, ((other j) ∩ Finset.univ.biUnion C).Nonempty →
    ¬ other j ⊆ Finset.univ.biUnion C → D ⊆ other j

variable {val : Fin n → Type*}
variable (M : RootSCM (splitGraph A C D other) val)

/-- Original selected-root state: its split C-input and a common-D component.
Only the anchor's common component will actually be read by a mechanism. -/
def bundledRootValue : K ⊕ J → Type _
  | .inl k => M.rootValue (.inl (some k)) × M.rootValue (.inl none)
  | .inr j => M.rootValue (.inr j)

def recoverSplitInputs (anchor : K) (u : ∀ r, bundledRootValue A C D other M r) :
    ∀ r, M.rootValue r
  | .inl none => (u (.inl anchor)).2
  | .inl (some k) => (u (.inl k)).1
  | .inr j => u (.inr j)

/-- Recover only the split parents of a node from that node's allowed original
parents. The common-D coordinate is available through the anchor root. -/
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

/-- Actual original-graph mechanisms simulating a given split-graph model. -/
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

/-- Pointwise simulation of the split model, using only original allowed parents. -/
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

/-- Encode split inputs without duplicating the random common-D component
across original roots. Nonanchor common components are an ignored constant. -/
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

/-- Every split input realization is reproduced by an explicitly encoded
original input realization. No observational equivalence is assumed. -/
theorem split_eval_reproduced (anchor : K) (constant : M.rootValue (.inl none))
    (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    (bundledModel A C D other M anchor).eval (encodeSplitInputs A C D other M anchor constant u) ε =
      M.eval u ε := by
  rw [bundledModel_eval, recover_encode]

end MeraConstraints.HiddenGraph.StrongFaceSplitting
