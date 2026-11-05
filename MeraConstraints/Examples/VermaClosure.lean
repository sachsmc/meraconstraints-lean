import MeraConstraints.HiddenGraph.Ancestry

/-!
# A set that is closed in the district but not closed

The end of the section "Identifying nontrivial constraints" distinguishes two
kinds of closure for a set of district members (`HiddenGraph.ClosedInDistrict`
and `HiddenGraph.FullClosed`). A set is closed in the district if it contains the
members of the district that are parents of its elements. It is closed if it
contains the members of the district that are ancestors of its elements in the
whole graph. Closed implies closed in the district, but not conversely.

The example is the graph `A → B → C → D` with an unobserved parent of `B` and
`D`. The manuscript writes it `V_1 → V_2 → V_3 → V_4` with `U → V_2` and
`U → V_4`, so `A, B, C, D` are `V_1, …, V_4`. The district is `{B, D}`. The set
`{D}` is closed in the district, since the only parent of `D`, namely `C`, is in
another district. It is not closed, since `B` is an ancestor of `D` through `C`
and lies in the same district. The ancestor relation is taken in the whole graph,
so the path `B → C → D` through `C` counts.
-/

namespace MeraConstraints.Examples.VermaClosure

open HiddenGraph

abbrev A : Fin 4 := 0
abbrev B : Fin 4 := 1
abbrev C : Fin 4 := 2
abbrev D : Fin 4 := 3

def graph : HiddenGraph.Graph 4 1 where
  observed := {
    parents := fun i => Finset.univ.filter fun j => j.val + 1 = i.val
    parents_lt := by
      intro i j h
      have hij := (Finset.mem_filter.1 h).2
      change j.val < i.val
      rw [← hij]
      exact Nat.lt_succ_self j.val }
  children := fun _ => {B, D}
  two_le_card := by decide
  child_antichain := fun u v _ => Subsingleton.elim u v

theorem b_same_district_d : observedDistrict graph B = observedDistrict graph D :=
  (districtOf_eq_iff graph _ _).2
    (children_same_district graph 0 B D (by decide) (by decide))

theorem c_different_district_d : observedDistrict graph C ≠ observedDistrict graph D := by
  intro h
  have heq : Sum.inl D = Sum.inl C :=
    connected_observed_eq_of_no_latent_parent graph C (by decide)
      ((districtOf_eq_iff graph _ _).1 h)
  exact (by decide : D ≠ C) (Sum.inl.inj heq)

theorem b_ancestor_d : ObservedAncestor graph B D :=
  observedAncestor_trans graph
    (observedAncestor_of_parent graph (by decide : B ∈ graph.observed.parents C))
    (observedAncestor_of_parent graph (by decide : C ∈ graph.observed.parents D))

theorem singleton_d_closedInDistrict :
    HiddenGraph.ClosedInDistrict graph (observedDistrict graph D) {D} := by
  constructor
  · intro i hi
    have hi' : i = D := Finset.mem_singleton.1 hi
    subst i
    rfl
  · intro i hi j hp hj
    have hi' : i = D := Finset.mem_singleton.1 hi
    subst i
    have hval : j.val + 1 = D.val := (Finset.mem_filter.1 hp).2
    have hj' : j = C := Fin.ext (Nat.succ.inj hval)
    subst j
    exact False.elim (c_different_district_d hj)

theorem singleton_d_not_fullClosed :
    ¬ FullClosed graph (observedDistrict graph D) {D} := by
  intro h
  have hB : B ∈ ({D} : Finset (Fin 4)) :=
    h.2 D (by simp) B b_ancestor_d b_same_district_d
  exact (by decide : B ≠ D) (Finset.mem_singleton.1 hB)

/-- A set closed in the district need not be closed, even when there is a single
unobserved variable. -/
theorem closure_distinction :
    HiddenGraph.ClosedInDistrict graph (observedDistrict graph D) {D} ∧
      ¬ FullClosed graph (observedDistrict graph D) {D} :=
  ⟨singleton_d_closedInDistrict, singleton_d_not_fullClosed⟩

end MeraConstraints.Examples.VermaClosure
