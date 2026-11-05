import MeraConstraints.HiddenGraph

/-!
# Observed ancestry and the two kinds of closed set

The manuscript uses two kinds of closure for a set `S` of members of a district.
In the trivial equality constraints (Proposition 4, `prop:nontrivial`), `S` is
**closed** if it contains every member of the district that is an ancestor of a
member of `S`. The directed path from the ancestor may leave the district and
return. The set `S` is **closed in the district** if the same holds for
directed paths that stay inside the district. A closed set is closed in the
district, but not conversely.

Sets here are subsets of `Fin n`, in the topological order of the whole DAG.
`FullClosed` uses ancestry in the observed DAG, including the vertex itself.
`ClosedInDistrict` asks that the parents of each member that lie in the district
are in the set, which gives the same for all paths inside the district. It
corresponds to `District.ClosedInDistrict`, which indexes members within the
district.

For each `k`, the members of a district with index below `k` form a closed
set, because an ancestor has a smaller or equal index (`districtPrefix_fullClosed`).
These are facts about the graph and use no assumption on the c-degree.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

def ObservedEdge (i j : Fin n) : Prop := i ∈ G.observed.parents j

/-- `i` is an ancestor of `j` in the observed DAG, where `i` is its own ancestor.
Unobserved variables cannot lie on these paths, by Condition 1. -/
abbrev ObservedAncestor := Relation.ReflTransGen (ObservedEdge G)

theorem observedAncestor_refl (i : Fin n) : ObservedAncestor G i i :=
  Relation.ReflTransGen.refl

theorem observedAncestor_of_parent {i j : Fin n} (h : i ∈ G.observed.parents j) :
    ObservedAncestor G i j := Relation.ReflTransGen.single h

theorem observedAncestor_trans {i j k : Fin n}
    (hij : ObservedAncestor G i j) (hjk : ObservedAncestor G j k) :
    ObservedAncestor G i k := Relation.ReflTransGen.trans hij hjk

/-- Parents come before their children in the topological order. -/
theorem observedParent_lt {i j : Fin n} (h : i ∈ G.observed.parents j) : i < j :=
  G.observed.parents_lt h

/-- An ancestor comes before its descendant, or equals it, in the topological
order. -/
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

/-- `S` is a closed set of members of the district `d` (Proposition 4,
`prop:nontrivial`): it contains every member of `d` that is an ancestor of a
member of `S`. -/
def FullClosed (d : DistrictId G) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, observedDistrict G i = d) ∧
    ∀ i ∈ S, ∀ j, ObservedAncestor G j i → observedDistrict G j = d → j ∈ S

/-- `S` is closed in the district `d`: it contains every parent in `d` of a
member of `S`, so it contains the ancestors reached by paths inside `d`. -/
def ClosedInDistrict (d : DistrictId G) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, observedDistrict G i = d) ∧
    ∀ i ∈ S, ∀ j, j ∈ G.observed.parents i → observedDistrict G j = d → j ∈ S

theorem fullClosed_implies_closedInDistrict (d : DistrictId G) (S : Finset (Fin n))
    (hS : FullClosed G d S) : ClosedInDistrict G d S := by
  refine ⟨hS.1, ?_⟩
  intro i hi j hji hj
  exact hS.2 i hi j (observedAncestor_of_parent G hji) hj

/-- The members of the district `d` with index below `k`. -/
noncomputable def districtPrefix (d : DistrictId G) (k : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => observedDistrict G i = d ∧ i.val < k

@[simp] theorem mem_districtPrefix (d : DistrictId G) (k : ℕ) (i : Fin n) :
    i ∈ districtPrefix G d k ↔ observedDistrict G i = d ∧ i.val < k := by
  classical
  simp [districtPrefix]

/-- The first members of a district, in the topological order, form a closed
set, including for ancestors reached through paths that leave the district. -/
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
