import MeraConstraints.CompactDistrict.InstrumentalStructure

/-!
# Permitted parent readers for copying a district path

Every member of an explicit path has an observed parent which is either the
external source or another path member. Select such a parent from the actual
parent set. The DAG order puts that parent strictly before the terminal
member, so it cannot be the terminal treatment whose value is overridden in
the instrumental profiles. This supplies legitimate local mechanisms without
giving any member access to an unlisted external input.
-/

namespace MeraConstraints.CompactDistrict.MemberPath

variable {n : ℕ} {D : Type*} {G : CausalDAG n} {block : Fin n → D} {d : D} {w v : Fin n}

theorem parent_on_path (p : MemberPath G block d w v) {i : Fin n} (hi : i ∈ p.vertices) :
    ∃ j, j ∈ G.parents i ∧ (j = w ∨ j ∈ p.vertices) := by
  induction p with
  | direct _ hwv =>
    have heq := Finset.mem_singleton.mp hi
    subst i
    exact ⟨w, hwv, Or.inl rfl⟩
  | tail initial _ hij ih =>
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact ⟨_, hij, Or.inr (Finset.mem_insert_of_mem initial.endpoint_mem)⟩
    · obtain ⟨j, hji, hjw | hjp⟩ := ih hi
      · exact ⟨j, hji, Or.inl hjw⟩
      · exact ⟨j, hji, Or.inr (Finset.mem_insert_of_mem hjp)⟩

noncomputable def copyParent (p : MemberPath G block d w v) (i : Fin n) (hi : i ∈ p.vertices) : Fin n :=
  Classical.choose (p.parent_on_path hi)

theorem copyParent_mem (p : MemberPath G block d w v) (i : Fin n) (hi : i ∈ p.vertices) :
    p.copyParent i hi ∈ G.parents i := (Classical.choose_spec (p.parent_on_path hi)).1

theorem copyParent_source_or_path (p : MemberPath G block d w v) (i : Fin n) (hi : i ∈ p.vertices) :
    p.copyParent i hi = w ∨ p.copyParent i hi ∈ p.vertices :=
  (Classical.choose_spec (p.parent_on_path hi)).2

theorem copyParent_lt_terminal (p : MemberPath G block d w v) (i : Fin n) (hi : i ∈ p.vertices) :
    p.copyParent i hi < v := lt_of_lt_of_le (G.parents_lt (p.copyParent_mem i hi)) (p.vertices_le hi)

end MeraConstraints.CompactDistrict.MemberPath
