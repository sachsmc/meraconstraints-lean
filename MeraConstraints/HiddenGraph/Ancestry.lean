import MeraConstraints.HiddenGraph

/-!
# Observed ancestry and the two notions of district closure

The paper uses two different closure notions. In the equality criterion of
Proposition `prop:nontrivial`, a set is **closed** if it contains every member
of its district that is an ancestor of one of its members. These directed
paths may leave the district and subsequently return. Later the manuscript
also uses **closed in the district**, which concerns paths entirely within
the district. These notions need not coincide.

Here all sets consist of vertices in the original global observed order.
`FullClosed` uses reflexive observed ancestry in that full DAG.
`ClosedInDistrict` asks only for the internal parents of every member; by
iteration, this includes all paths entirely within the district. The latter
is the global-vertex counterpart of `District.ClosedInDistrict`, which uses
a separately indexed local district graph.

Full closure implies internal closure. Every topological prefix of a district
is fully closed: an observed ancestor always has a smaller or equal global
index, even when the witnessing path leaves and re-enters the district.
These are graph facts and require no c-degree or probabilistic assumptions.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

def ObservedEdge (i j : Fin n) : Prop := i ∈ G.observed.parents j

/-- Observed ancestry in the full observed DAG, including the vertex itself.
Latents cannot be intermediate vertices of these paths by Condition `A1`. -/
abbrev ObservedAncestor := Relation.ReflTransGen (ObservedEdge G)

theorem observedAncestor_refl (i : Fin n) : ObservedAncestor G i i :=
  Relation.ReflTransGen.refl

theorem observedAncestor_of_parent {i j : Fin n} (h : i ∈ G.observed.parents j) :
    ObservedAncestor G i j := Relation.ReflTransGen.single h

theorem observedAncestor_trans {i j k : Fin n}
    (hij : ObservedAncestor G i j) (hjk : ObservedAncestor G j k) :
    ObservedAncestor G i k := Relation.ReflTransGen.trans hij hjk

/-- Parent precedence is built into the global DAG presentation. -/
theorem observedParent_lt {i j : Fin n} (h : i ∈ G.observed.parents j) : i < j :=
  G.observed.parents_lt h

/-- Every observed ancestor precedes or equals its descendant in the global
order. The proof follows the complete directed path, not a contracted graph. -/
theorem observedAncestor_le {i j : Fin n} (h : ObservedAncestor G i j) : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | tail hij hjk ih => exact le_trans ih (observedParent_lt G hjk).le

theorem observedAncestor_lt_of_ne {i j : Fin n}
    (h : ObservedAncestor G i j) (hne : i ≠ j) : i < j :=
  lt_of_le_of_ne (observedAncestor_le G h) hne

theorem observedAncestor_antisymm {i j : Fin n}
    (hij : ObservedAncestor G i j) (hji : ObservedAncestor G j i) : i = j :=
  le_antisymm (observedAncestor_le G hij) (observedAncestor_le G hji)

/-- The full-ancestry closure used in Proposition `prop:nontrivial`.
The first conjunct records that this is a subset of the selected district. -/
def FullClosed (d : DistrictId G) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, observedDistrict G i = d) ∧
    ∀ i ∈ S, ∀ j, ObservedAncestor G j i → observedDistrict G j = d → j ∈ S

/-- Closure for directed paths that stay inside a district, expressed by
closure under one internal parent step. -/
def ClosedInDistrict (d : DistrictId G) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, observedDistrict G i = d) ∧
    ∀ i ∈ S, ∀ j, j ∈ G.observed.parents i → observedDistrict G j = d → j ∈ S

theorem fullClosed_implies_closedInDistrict (d : DistrictId G) (S : Finset (Fin n))
    (hS : FullClosed G d S) : ClosedInDistrict G d S := by
  refine ⟨hS.1, ?_⟩
  intro i hi j hji hj
  exact hS.2 i hi j (observedAncestor_of_parent G hji) hj

/-- All members of a district that occur before global index `k`. Restricting
a topological ordering to a district gives precisely these prefix sets. -/
noncomputable def districtPrefix (d : DistrictId G) (k : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => observedDistrict G i = d ∧ i.val < k

@[simp] theorem mem_districtPrefix (d : DistrictId G) (k : ℕ) (i : Fin n) :
    i ∈ districtPrefix G d k ↔ observedDistrict G i = d ∧ i.val < k := by
  classical
  simp [districtPrefix]

/-- Prefixes are fully closed, including ancestors reached through observed
vertices outside the district. No quotient graph acyclicity is assumed. -/
theorem districtPrefix_fullClosed (d : DistrictId G) (k : ℕ) :
    FullClosed G d (districtPrefix G d k) := by
  constructor
  · intro i hi
    exact ((mem_districtPrefix G d k i).1 hi).1
  · intro i hi j hji hj
    apply (mem_districtPrefix G d k j).2
    refine ⟨hj, ?_⟩
    exact lt_of_le_of_lt (show j.val ≤ i.val from observedAncestor_le G hji)
      (((mem_districtPrefix G d k i).1 hi).2)

theorem districtPrefix_closedInDistrict (d : DistrictId G) (k : ℕ) :
    ClosedInDistrict G d (districtPrefix G d k) :=
  fullClosed_implies_closedInDistrict G d _ (districtPrefix_fullClosed G d k)

end MeraConstraints.HiddenGraph
