import MeraConstraints.CompactDistrict.Reachability

/-!
# The instrumental type of Remark 3

This chapter states the graph condition of type (i) in Remark 3
(`prop:ineqstructure`) and proves the last step of its proof for type (i). An
`InstrumentalWitness` consists of a directed path `W → Z₁ → ⋯ → Z_r → A` with `W`
an external parent and `Z₁, …, Z_r, A` members (`r ≥ 0`), an edge `A → B`, and the
requirement that no vertex of the path other than `A`, including `W`, is a parent of
`B`. The vertices `Z₁, …, Z_r` are `intermediates`. `InstrumentalType` says that the
district has such a structure.

The vertex `B` is not on the path, since the path ends at `A` and `A → B`
(`outcome_not_on_path`). Take two rows that differ only in `W`, in `Z₁, …, Z_r` and in
`B`. Then `B` has the same parent values in both, so no single profile is compatible
with both rows if `B` takes different values in them (`not_both_compatible`). This
is the argument that the vector `t` is not a column of `B`.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} (G : CausalDAG n) (block : Fin n → D) (d : D)

/-- The path from the external parent `w` to the member `a`, the edge from `a` to
`b`, and the exclusion of `w` and the other path vertices from the parents of `b`. -/
structure InstrumentalWitness (w : ExternalParent G block d) (a b : Member block d) where
  path : MemberPath G block d w.val a.val
  treatment_parent : a.val ∈ G.parents b.val
  exclusion : ∀ i ∈ insert w.val path.vertices, i ≠ a.val → i ∉ G.parents b.val

def InstrumentalType : Prop :=
  ∃ w : ExternalParent G block d, ∃ a b : Member block d, Nonempty (InstrumentalWitness G block d w a b)

namespace InstrumentalWitness

variable {G block d} {w : ExternalParent G block d} {a b : Member block d}
  (P : InstrumentalWitness G block d w a b)

def intermediates : Finset (Fin n) := P.path.vertices.erase a.val

/-- The case of an edge `w → a`, with no intermediate members, where `w` is not a
parent of `b`. -/
def direct (hwa : w.val ∈ G.parents a.val) (hab : a.val ∈ G.parents b.val)
    (hwb : w.val ∉ G.parents b.val) : InstrumentalWitness G block d w a b where
  path := .direct a.property hwa
  treatment_parent := hab
  exclusion := by
    intro i hi hia
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact hwb
    · exact False.elim (hia (Finset.mem_singleton.mp hi))

theorem direct_intermediates (hwa : w.val ∈ G.parents a.val) (hab : a.val ∈ G.parents b.val)
    (hwb : w.val ∉ G.parents b.val) : (direct hwa hab hwb).intermediates = ∅ := by
  simp [direct, intermediates, MemberPath.vertices]

include P in
theorem treatment_lt_outcome : a.val < b.val := G.parents_lt P.treatment_parent

theorem outcome_not_on_path : b.val ∉ P.path.vertices := P.path.next_not_mem P.treatment_parent

theorem instrument_not_on_path : w.val ∉ P.path.vertices := by
  intro hw
  exact w.property.1 (P.path.vertices_member hw)

include P in
theorem instrument_not_parent : w.val ∉ G.parents b.val := by
  apply P.exclusion w.val (Finset.mem_insert_self _ _)
  intro hwa
  apply w.property.1
  exact (congrArg block hwa).trans a.property

theorem intermediate_not_parent {i : Fin n} (hi : i ∈ P.intermediates) : i ∉ G.parents b.val := by
  obtain ⟨hia, hip⟩ := Finset.mem_erase.mp hi
  exact P.exclusion i (Finset.mem_insert_of_mem hip) hia

theorem intermediate_member {i : Fin n} (hi : i ∈ P.intermediates) : block i = d :=
  P.path.vertices_member (Finset.mem_erase.mp hi).2

theorem treatment_not_intermediate : a.val ∉ P.intermediates := Finset.notMem_erase _ _

theorem outcome_not_intermediate : b.val ∉ P.intermediates :=
  fun hb => P.outcome_not_on_path (Finset.mem_erase.mp hb).2

variable [DecidableEq D] (val : Fin n → Type*)

/-- If two rows differ only in `W`, in the intermediate vertices and in `B`, the
parents of `B` have the same values in both. -/
theorem parentAssign_eq (x x' : MemberAssign val block d) (e e' : ExternalAssign G val block d)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j)
    (hx : ∀ i : Member block d, i.val ∉ insert b.val P.intermediates → x i = x' i) :
    CompactDistrict.parentAssign G val block d (x, e) b =
      CompactDistrict.parentAssign G val block d (x', e') b := by
  funext j
  by_cases hj : block j = d
  · simp only [CompactDistrict.parentAssign, dif_pos hj]
    apply hx ⟨j, hj⟩
    intro hm
    obtain hjb | hji := Finset.mem_insert.mp hm
    · exact (ne_of_lt (G.parents_lt j.property)) hjb
    · exact P.intermediate_not_parent hji j.property
  · simp only [CompactDistrict.parentAssign, dif_neg hj]
    apply he ⟨j, hj, ⟨b, b.property, j.property⟩⟩
    intro hje
    apply P.instrument_not_parent
    have hv : j.val = w.val := congrArg Subtype.val hje
    simpa only [hv] using j.property

/-- A profile compatible with both rows gives `B` the same value in both. -/
theorem outcome_eq_of_compatible (r : GlobalModel.Profile G val block d)
    (x x' : MemberAssign val block d) (e e' : ExternalAssign G val block d)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j)
    (hx : ∀ i : Member block d, i.val ∉ insert b.val P.intermediates → x i = x' i)
    (hr : Compatible G val block d (x, e) r) (hr' : Compatible G val block d (x', e') r) :
    x b = x' b := by
  have h := hr b
  rw [P.parentAssign_eq val x x' e e' he hx] at h
  exact h.symm.trans (hr' b)

/-- No profile is compatible with both rows if `B` takes different values in
them. -/
theorem not_both_compatible (x x' : MemberAssign val block d) (e e' : ExternalAssign G val block d)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j)
    (hx : ∀ i : Member block d, i.val ∉ insert b.val P.intermediates → x i = x' i)
    (hb : x b ≠ x' b) :
    ¬ ∃ r : GlobalModel.Profile G val block d,
      Compatible G val block d (x, e) r ∧ Compatible G val block d (x', e') r := by
  rintro ⟨r, hr, hr'⟩
  exact hb (P.outcome_eq_of_compatible val r x x' e e' he hx hr hr')

end InstrumentalWitness
end MeraConstraints.CompactDistrict
