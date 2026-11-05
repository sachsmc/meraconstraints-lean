import MeraConstraints.CompactDistrict

/-!
# External parents that reach a member

This is Step 1 of the proof of Remark 3 (`prop:ineqstructure`): in every profile, the
value of a member depends on `v₂` only through the external parents that reach it
(`eval_eq_of_eq_on_reaching`).

As in the manuscript, an external parent `W` reaches a member `V` if there is a
directed path from `W` to `V` all of whose vertices other than `W` are members of the
district. `MemberPath` is such a path: its first edge goes from the source to a
member, and every later vertex is a member. The path may be a single edge. The
statements need no assumption on the value sets, the distribution or the c-degree.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*}

/-- A directed path from `w` to `v` of at least one edge, all of whose vertices
after `w` are members of the district. -/
inductive MemberPath (G : CausalDAG n) (block : Fin n → D) (d : D) (w : Fin n) : Fin n → Type
  | direct {v : Fin n} (member : block v = d) (edge : w ∈ G.parents v) : MemberPath G block d w v
  | tail {i j : Fin n} (initial : MemberPath G block d w i) (member : block j = d)
      (edge : i ∈ G.parents j) : MemberPath G block d w j

namespace MemberPath

variable {G : CausalDAG n} {block : Fin n → D} {d : D} {w : Fin n}

/-- The vertices of the path other than its source, including the endpoint. -/
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

/-- `w` reaches `v`: there is a `MemberPath` from `w` to `v`. For an external
parent `w`, this is the manuscript's "reaches". -/
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

/-- Step 1 of the proof of Remark 3: the value a profile gives a member is
unchanged if `v₂` changes only at external parents that do not reach the member. -/
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

/-- Changing one external parent does not change the value of a member that it
does not reach. Paths that leave the district do not count. -/
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
