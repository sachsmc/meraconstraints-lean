import MeraConstraints.CompactDistrict

/-!
# External parents reaching a member through its district

Appendix proof of `prop:ineqstructure`, Step 1: a profile's value at a member
depends on external inputs only through external parents that reach it.

A path starts with one observed edge from its source to a district member;
every subsequent vertex is a member of the same district. Thus it cannot
leave the district and return. The source is external when this definition
is applied to an `ExternalParent`. The path includes its terminal member and
permits a direct external-parent edge, with no intermediate members.

The proofs use the actual compact district evaluation and parent restrictions.
No finiteness of the state spaces, probability law or c-degree assumption is
needed for this deterministic dependence statement.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*}

/-- A directed observed path whose vertices after the source stay in the
selected district. The terminal member is included in the path. -/
inductive MemberPath (G : CausalDAG n) (block : Fin n → D) (d : D) (w : Fin n) : Fin n → Type
  | direct {v : Fin n} (member : block v = d) (edge : w ∈ G.parents v) : MemberPath G block d w v
  | tail {i j : Fin n} (initial : MemberPath G block d w i) (member : block j = d)
      (edge : i ∈ G.parents j) : MemberPath G block d w j

namespace MemberPath

variable {G : CausalDAG n} {block : Fin n → D} {d : D} {w : Fin n}

/-- All member vertices on the path, including its endpoint and excluding
the external source. This is not the set of intermediate vertices alone. -/
def vertices {v : Fin n} (p : MemberPath G block d w v) : Finset (Fin n) :=
  match p with
  | .direct _ _ => {v}
  | .tail initial _ _ => insert v initial.vertices

def length {v : Fin n} (p : MemberPath G block d w v) : ℕ :=
  match p with
  | .direct _ _ => 1
  | .tail initial _ _ => initial.length + 1

variable {v : Fin n}

theorem endpoint_member (p : MemberPath G block d w v) : block v = d := by
  cases p with
  | direct hv _ => exact hv
  | tail _ hv _ => exact hv

theorem endpoint_mem (p : MemberPath G block d w v) : v ∈ p.vertices := by
  cases p <;> simp [vertices]

theorem vertices_member (p : MemberPath G block d w v) {i : Fin n} (hi : i ∈ p.vertices) : block i = d := by
  induction p with
  | direct hv _ =>
    have heq := Finset.mem_singleton.mp hi
    exact heq.symm ▸ hv
  | @tail a b initial hb _ ih =>
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact hb
    · exact ih hi

theorem start_lt (p : MemberPath G block d w v) : w < v := by
  induction p with
  | direct _ hwv => exact G.parents_lt hwv
  | tail _ _ hij ih => exact lt_trans ih (G.parents_lt hij)

theorem vertices_le (p : MemberPath G block d w v) {i : Fin n} (hi : i ∈ p.vertices) : i ≤ v := by
  induction p with
  | direct _ _ => exact (Finset.mem_singleton.mp hi).le
  | tail initial _ hij ih =>
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact le_rfl
    · exact le_trans (ih hi) (G.parents_lt hij).le

theorem start_lt_vertex (p : MemberPath G block d w v) {i : Fin n} (hi : i ∈ p.vertices) : w < i := by
  induction p with
  | direct _ hwv =>
    have heq := Finset.mem_singleton.mp hi
    exact heq.symm ▸ G.parents_lt hwv
  | tail initial _ hij ih =>
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact lt_trans initial.start_lt (G.parents_lt hij)
    · exact ih hi

theorem next_not_mem (p : MemberPath G block d w v) {j : Fin n} (hvj : v ∈ G.parents j) :
    j ∉ p.vertices := fun hj => (not_le_of_gt (G.parents_lt hvj)) (p.vertices_le hj)

theorem card_vertices (p : MemberPath G block d w v) : p.vertices.card = p.length := by
  induction p with
  | direct _ _ => simp [vertices, length]
  | tail initial _ hij ih => simp [vertices, length, Finset.card_insert_of_notMem (initial.next_not_mem hij), ih]

theorem first_edge (p : MemberPath G block d w v) : ∃ i, block i = d ∧ w ∈ G.parents i := by
  induction p with
  | direct hv hwv => exact ⟨_, hv, hwv⟩
  | tail _ _ _ ih => exact ih

end MemberPath

variable (G : CausalDAG n) (block : Fin n → D) (d : D)

/-- The manuscript's external-parent reachability relation. When the source
is external, every vertex other than that source is a district member. -/
def Reaches (w v : Fin n) : Prop := Nonempty (MemberPath G block d w v)

theorem reaches_direct {w v : Fin n} (hv : block v = d) (hwv : w ∈ G.parents v) :
    Reaches G block d w v := ⟨.direct hv hwv⟩

theorem reaches_tail {w i j : Fin n} (hw : Reaches G block d w i)
    (hj : block j = d) (hij : i ∈ G.parents j) : Reaches G block d w j := by
  obtain ⟨p⟩ := hw
  exact ⟨.tail p hj hij⟩

theorem reaches_lt {w v : Fin n} (h : Reaches G block d w v) : w < v := by
  obtain ⟨p⟩ := h
  exact p.start_lt

theorem isExternalParent_of_reaches {w v : Fin n} (hw : block w ≠ d) (h : Reaches G block d w v) :
    IsExternalParent G block d w := by
  obtain ⟨p⟩ := h
  exact ⟨hw, p.first_edge⟩

variable [DecidableEq D] (val : Fin n → Type*)

/-- Appendix `prop:ineqstructure`, Step 1: the actual profile evaluation
depends only on the external parents which reach the selected member. -/
theorem eval_eq_of_eq_on_reaching (r : GlobalModel.Profile G val block d)
    (e e' : ExternalAssign G val block d) (i : Member block d)
    (he : ∀ w : ExternalParent G block d, Reaches G block d w.val i.val → e w = e' w) :
    eval G val block d r e i = eval G val block d r e' i := by
  rw [eval, eval]
  congr 1
  funext j
  by_cases hj : block j = d
  · simp only [dif_pos hj]
    apply eval_eq_of_eq_on_reaching r e e' ⟨j, hj⟩
    intro w hw
    exact he w (reaches_tail G block d hw i.property j.property)
  · simp only [dif_neg hj]
    exact he ⟨j, hj, ⟨i, i.property, j.property⟩⟩ (reaches_direct G block d i.property j.property)
termination_by i.val.val
decreasing_by exact G.parents_lt j.property

/-- Changing one external parent cannot change a member that it does not
reach through the district. Other observed paths may leave the district. -/
theorem eval_eq_of_change_unreached (r : GlobalModel.Profile G val block d)
    (e e' : ExternalAssign G val block d) (w : ExternalParent G block d) (i : Member block d)
    (hw : ¬ Reaches G block d w.val i.val)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j) :
    eval G val block d r e i = eval G val block d r e' i := by
  apply eval_eq_of_eq_on_reaching G block d val r e e' i
  intro j hj
  by_cases h : j = w
  · subst j
    exact False.elim (hw hj)
  · exact he j h

end MeraConstraints.CompactDistrict
