import MeraConstraints.HiddenGraph.MoralSeparation

/-!
# A collider is opened by conditioning on its child

In the graph `0 → 2 ← 1`, with no unobserved variables, the observed variables
`0` and `1` are separated given the empty set (`roots_separated`). The ancestral
set of `{0, 1}` does not contain `2`, so the moral graph has no edge between them.
Given `{2}`, the ancestral set contains `2`, its parents `0` and `1` are joined
by an edge, and they are no longer separated (`roots_not_separated_given_child`).
This is the behavior of d-separation at a collider, for `MoralSeparated`, which
`MainResults` uses for the conditional independencies implied by the graph.
-/

namespace MeraConstraints.Examples.MoralCollider

open HiddenGraph

def graph : HiddenGraph.Graph 3 0 where
  observed := {
    parents := fun i => if i = 2 then {0, 1} else ∅
    parents_lt := by
      intro i j hj
      by_cases hi : i = 2
      · subst i
        have hj' : j = 0 ∨ j = 1 := by simpa using hj
        rcases hj' with rfl | rfl <;> decide
      · simp [hi] at hj }
  children := Fin.elim0
  two_le_card := fun u => Fin.elim0 u
  child_antichain := fun u => Fin.elim0 u

theorem roots_separated : MoralSeparated graph {0} {1} ∅ := by
  classical
  let side : Vertex (n := 3) (ℓ := 0) → Bool := fun x => match x with
    | .inl i => decide (i = 1)
    | .inr _ => false
  apply moralSeparated_of_cut graph {0} {1} ∅ (by decide) (by simp) (by simp) side
  · intro i hi
    have he : i = 0 := Finset.mem_singleton.mp hi
    subst i
    decide
  · intro i hi
    have he : i = 1 := Finset.mem_singleton.mp hi
    subst i
    decide
  · intro x y _ _ hxy
    have hnone (c : Fin 3) (hc : c ∈ observedAncestors graph ({0} ∪ {1} ∪ ∅))
        (v : Vertex (n := 3) (ℓ := 0)) : ¬ FullParent graph v c := by
      obtain ⟨k, hk, hck⟩ := (mem_observedAncestors graph _ c).mp hc
      have hk' : k = 0 ∨ k = 1 := by simpa using hk
      have hcne : c ≠ 2 := by
        intro he
        subst c
        have hle := observedAncestor_le graph hck
        rcases hk' with rfl | rfl
        · exact (by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hle
        · exact (by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hle
      cases v with
      | inl j => simp [FullParent, graph, hcne]
      | inr u => exact Fin.elim0 u
    rcases hxy with ⟨c, hc, _, hp⟩ | ⟨c, hc, _, hp⟩ | ⟨c, hc, hp, _⟩
    · exact (hnone c hc _ hp).elim
    · exact (hnone c hc _ hp).elim
    · exact (hnone c hc _ hp).elim

theorem roots_not_separated_given_child : ¬ MoralSeparated graph {0} {1} {2} := by
  intro hsep
  let A := observedAncestors graph ({0} ∪ {1} ∪ {2})
  have h0 : (0 : Fin 3) ∈ A := subset_observedAncestors graph _ (by simp)
  have h1 : (1 : Fin 3) ∈ A := subset_observedAncestors graph _ (by simp)
  have h2 : (2 : Fin 3) ∈ A := subset_observedAncestors graph _ (by simp)
  apply hsep.2.2.2 0 (by simp) 1 (by simp)
  apply Relation.ReflTransGen.single
  refine ⟨⟨h0, by simp [ConditionedVertex]⟩, ⟨h1, by simp [ConditionedVertex]⟩, ?_⟩
  exact Or.inr (Or.inr ⟨2, h2, by simp [FullParent, graph], by simp [FullParent, graph]⟩)

end MeraConstraints.Examples.MoralCollider
