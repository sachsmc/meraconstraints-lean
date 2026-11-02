import MeraConstraints.SCM.ResponseFunction
import Mathlib.Logic.Relation

/-!
# Hidden-variable DAGs, districts, and c-degree

Conditions `A1` and `A2` of `main-revised.tex` concern the hidden-variable
graph before the response-variable transformation. Its observed arrows form
a topologically ordered DAG. Its other arrows go from a latent root to an
observed child; there are no arrows entering latent vertices. Each latent
root has at least two children, and its child set is not contained in that
of a distinct latent root.

The manuscript's districts contain **both** observed and latent vertices.
They are the connected components remaining after the observed arrows are
deleted. Accordingly we use the equivalence closure of bipartite incidence
on `Fin n ⊕ Fin ℓ`, rather than identifying a district with just its observed
members. The c-degree counts latent vertices in that component, including
isolated observed components of c-degree zero.

The graph does not itself assert any probabilistic independence. Independence
of root inputs is a property of a probability law, and must be supplied when
using the structural evaluation below. In particular, pairwise independence
of response variables in distinct districts does not suffice for mutual
independence of the district response vectors.
-/

namespace MeraConstraints.HiddenGraph

/-- A finite hidden-variable DAG satisfying Conditions `A1` and `A2`.
Exogeneity is built into the permitted arrows. -/
structure Graph (n ℓ : ℕ) where
  observed : CausalDAG n
  children : Fin ℓ → Finset (Fin n)
  two_le_card : ∀ u, 2 ≤ (children u).card
  child_antichain : ∀ u v, children u ⊆ children v → u = v

variable {n ℓ : ℕ} (G : Graph n ℓ)

abbrev Vertex := Fin n ⊕ Fin ℓ

/-- The undirected graph obtained by deleting all observed-origin arrows. -/
def Incidence : Vertex (n := n) (ℓ := ℓ) → Vertex (n := n) (ℓ := ℓ) → Prop
  | .inl i, .inr u => i ∈ G.children u
  | .inr u, .inl i => i ∈ G.children u
  | _, _ => False

theorem incidence_symm {x y : Vertex (n := n) (ℓ := ℓ)}
    (h : Incidence G x y) : Incidence G y x := by
  cases x <;> cases y <;> exact h

/-- Membership in the same district, Definition `def:districts`. -/
abbrev Connected := Relation.EqvGen (Incidence G)

def districtSetoid : Setoid (Vertex (n := n) (ℓ := ℓ)) :=
  Relation.EqvGen.setoid (Incidence G)

/-- District identifiers form a quotient, so their fibers partition all
vertices, including singleton unconfounded observed vertices. -/
abbrev DistrictId := Quotient (districtSetoid G)

def districtOf (x : Vertex (n := n) (ℓ := ℓ)) : DistrictId G := Quotient.mk _ x

noncomputable instance : Fintype (DistrictId G) := Fintype.ofFinite _

/-- The block map used when assembling independent district profiles. -/
def observedDistrict (i : Fin n) : DistrictId G := districtOf G (.inl i)

theorem districtOf_eq_iff (x y : Vertex (n := n) (ℓ := ℓ)) :
    districtOf G x = districtOf G y ↔ Connected G x y := Quotient.eq

theorem connected_child (u : Fin ℓ) (i : Fin n) (hi : i ∈ G.children u) :
    Connected G (.inr u) (.inl i) := Relation.EqvGen.rel _ _ hi

theorem children_same_district (u : Fin ℓ) (i j : Fin n)
    (hi : i ∈ G.children u) (hj : j ∈ G.children u) :
    Connected G (.inl i) (.inl j) :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (connected_child G u i hi))
    (connected_child G u j hj)

/-- Every district contains an observed member. A latent-only component
would contradict Condition `A2`, because each latent root has children. -/
theorem observedDistrict_surjective : Function.Surjective (observedDistrict G) := by
  intro d
  refine Quotient.inductionOn d ?_
  intro x
  cases x with
  | inl i => exact ⟨i, rfl⟩
  | inr u =>
      have hpos : 0 < (G.children u).card := lt_of_lt_of_le (by decide : 0 < 2)
        (G.two_le_card u)
      obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
      refine ⟨i, (districtOf_eq_iff G _ _).2 ?_⟩
      exact Relation.EqvGen.symm _ _ (connected_child G u i hi)

/-- The latent vertices in the district of `x`. -/
noncomputable def latentMembers (x : Vertex (n := n) (ℓ := ℓ)) : Finset (Fin ℓ) := by
  classical
  exact Finset.univ.filter fun u => Connected G x (.inr u)

@[simp] theorem mem_latentMembers (x : Vertex (n := n) (ℓ := ℓ)) (u : Fin ℓ) :
    u ∈ latentMembers G x ↔ Connected G x (.inr u) := by
  classical
  simp [latentMembers]

/-- Definition `def:cdeg`: count hidden vertices, not observed members,
incident arrows, or pairwise bidirected edges. -/
noncomputable def cDegree (x : Vertex (n := n) (ℓ := ℓ)) : ℕ :=
  (latentMembers G x).card

/-- The graph c-degree is the maximum of its component c-degrees, with
maximum zero for the empty graph. Repeated vertices of a component do not
affect this maximum. -/
noncomputable def graphCDegree : ℕ := by
  classical
  exact Finset.univ.sup (cDegree G)

theorem cDegree_le_graphCDegree (x : Vertex (n := n) (ℓ := ℓ)) :
    cDegree G x ≤ graphCDegree G := by
  classical
  exact Finset.le_sup (Finset.mem_univ x)

theorem graphCDegree_le_iff (k : ℕ) :
    graphCDegree G ≤ k ↔ ∀ x, cDegree G x ≤ k := by
  classical
  simp [graphCDegree, Finset.sup_le_iff]

theorem latentMembers_eq_of_connected {x y : Vertex (n := n) (ℓ := ℓ)}
    (hxy : Connected G x y) : latentMembers G x = latentMembers G y := by
  classical
  ext u
  simp only [mem_latentMembers]
  constructor
  · intro hx
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxy) hx
  · intro hy
    exact Relation.EqvGen.trans _ _ _ hxy hy

theorem cDegree_eq_of_connected {x y : Vertex (n := n) (ℓ := ℓ)}
    (hxy : Connected G x y) : cDegree G x = cDegree G y := by
  unfold cDegree
  rw [latentMembers_eq_of_connected G hxy]

private def HasNeighbor (x : Vertex (n := n) (ℓ := ℓ)) : Prop :=
  ∃ y, Incidence G x y

private theorem connected_eq_or_neighbors {x y : Vertex (n := n) (ℓ := ℓ)}
    (h : Connected G x y) : x = y ∨ (HasNeighbor G x ∧ HasNeighbor G y) := by
  induction h with
  | rel a b hab => exact Or.inr ⟨⟨b, hab⟩, ⟨a, incidence_symm G hab⟩⟩
  | refl a => exact Or.inl rfl
  | symm a b _ ih =>
      rcases ih with h | ⟨ha, hb⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hb, ha⟩
  | trans a b c _ _ hab hbc =>
      rcases hab with h | ⟨ha, hb⟩
      · subst b
        exact hbc
      · rcases hbc with h | ⟨hb', hc⟩
        · subst c
          exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

private theorem observed_has_latent_of_neighbor (i : Fin n)
    (hi : HasNeighbor G (.inl i)) : ∃ u, i ∈ G.children u := by
  rcases hi with ⟨y, hy⟩
  cases y with
  | inl j => exact False.elim hy
  | inr u => exact ⟨u, hy⟩

/-- An observed vertex without a latent parent is isolated after deleting
the observed arrows, irrespective of its observed parent/child sets. -/
theorem connected_observed_eq_of_no_latent_parent (i : Fin n)
    (hi : ¬ ∃ u, i ∈ G.children u) {x : Vertex (n := n) (ℓ := ℓ)}
    (hix : Connected G (.inl i) x) : x = .inl i := by
  rcases connected_eq_or_neighbors G hix with h | ⟨hn, _⟩
  · exact h.symm
  · exact False.elim (hi (observed_has_latent_of_neighbor G i hn))

/-!
## Degree zero and degree one components

These two facts justify the first sentence of `sec:respvar`: degree-zero
components are singleton observed vertices; every observed member of a
degree-one component is a child of its unique latent root. The statements
are consequences of the component definition, not additional assumptions.
-/

theorem connected_observed_eq_of_cDegree_zero (i j : Fin n)
    (hzero : cDegree G (.inl i) = 0)
    (hij : Connected G (.inl i) (.inl j)) : i = j := by
  classical
  rcases connected_eq_or_neighbors G hij with h | ⟨hi, _⟩
  · exact Sum.inl.inj h
  · obtain ⟨u, hu⟩ := observed_has_latent_of_neighbor G i hi
    have hm : u ∈ latentMembers G (.inl i) := (mem_latentMembers G _ _).2
      (Relation.EqvGen.symm _ _ (connected_child G u i hu))
    have hempty : latentMembers G (.inl i) = ∅ := Finset.card_eq_zero.1 hzero
    simp [hempty] at hm

/-- Every observed member of a component with at most one latent root is
a direct child of that root. This rules out a merely indirect latent chain. -/
theorem child_of_cDegree_le_one (u : Fin ℓ) (i : Fin n)
    (hdegree : cDegree G (.inr u) ≤ 1)
    (hui : Connected G (.inr u) (.inl i)) : i ∈ G.children u := by
  classical
  have hn : HasNeighbor G (.inl i) := by
    rcases connected_eq_or_neighbors G hui with h | ⟨_, hi⟩
    · cases h
    · exact hi
  obtain ⟨v, hv⟩ := observed_has_latent_of_neighbor G i hn
  have hu : u ∈ latentMembers G (.inr u) :=
    (mem_latentMembers G _ _).2 (Relation.EqvGen.refl _)
  have hv' : v ∈ latentMembers G (.inr u) := (mem_latentMembers G _ _).2
    (Relation.EqvGen.trans _ _ _ hui
      (Relation.EqvGen.symm _ _ (connected_child G v i hv)))
  have huv : u = v := Finset.card_le_one.1 hdegree u hu v hv'
  simpa [huv] using hv

theorem connected_latent_observed_iff_of_cDegree_le_one (u : Fin ℓ) (i : Fin n)
    (hdegree : cDegree G (.inr u) ≤ 1) :
    Connected G (.inr u) (.inl i) ↔ i ∈ G.children u :=
  ⟨child_of_cDegree_le_one G u i hdegree, connected_child G u i⟩

end MeraConstraints.HiddenGraph
