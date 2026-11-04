import MeraConstraints.CompactDistrict.BellStructure
import MeraConstraints.CompactDistrict.InstrumentalProfiles

/-!
# Lifted Bell profiles through the permitted observed parents

Appendix `prop:ineqstructure` (ii) constructs d_fg by copying the W_A input
along its path, applying f at A, copying W_B along its disjoint path and
applying g at B. All other members take their chosen zero value. We use
the same binary encoding as the instrumental construction: an external
input is one precisely when it equals its chosen one value. This defines
the profiles on every external input, including additional state levels.

Each copying mechanism reads one actual observed parent selected on its
own path. That parent is strictly before the endpoint, so its value has
not been transformed by f or g. Disjoint paths ensure that the other
path's mechanism cannot overwrite this copied value. Extra observed edges
are permitted and ignored by these particular profiles.

The evaluation theorem checks the entire member assignment, not just A
and B. Distinct zero/one values are needed at members; external source
distinctness is needed only later to select four different input blocks.
No finite-state, c-degree or probability premise is used here.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}

namespace MemberPath

variable {w : ExternalParent G block d} {v : Fin n}
  (p : MemberPath G block d w.val v) (v0 v1 : FullAssign val)

/-- A local mechanism reading a listed parent, applying f only at the
terminal member. Every other member of this path copies the decoded bit. -/
noncomputable def copyValue (f : Bool → Bool) (i : Member block d)
    (hi : i.val ∈ p.vertices) (pa : PaAssign G val i.val) : val i.val :=
  let j := p.copyParent i.val hi
  let z := BinaryValues.decode v1 j (pa ⟨j, p.copyParent_mem i.val hi⟩)
  BinaryValues.encode v0 v1 i.val (if i.val = v then f z else z)

/-- Any member assignment that copies z on the path's intermediate members
lets each selected parent reader recover z. Its endpoint value is irrelevant. -/
theorem read_copyParent_of_values
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (x : MemberAssign val block d) (e : ExternalAssign G val block d) (z : Bool)
    (hw : BinaryValues.decode v1 w.val (e w) = z)
    (hx : ∀ j : Member block d, j.val ∈ p.vertices → j.val ≠ v →
      x j = BinaryValues.encode v0 v1 j.val z)
    (i : Member block d) (hi : i.val ∈ p.vertices) :
    BinaryValues.decode v1 (p.copyParent i.val hi)
      (parentAssign G val block d (x, e) i
        ⟨p.copyParent i.val hi, p.copyParent_mem i.val hi⟩) = z := by
  let j := p.copyParent i.val hi
  have hji : j ∈ G.parents i.val := p.copyParent_mem i.val hi
  obtain hjw | hjp := p.copyParent_source_or_path i.val hi
  · change j = w.val at hjw
    have hjout : block j ≠ d := by
      intro h
      exact w.property.1 (hjw ▸ h)
    change BinaryValues.decode v1 j (parentAssign G val block d (x, e) i ⟨j, hji⟩) = z
    simp only [parentAssign, dif_neg hjout]
    calc
      _ = BinaryValues.decode v1 w.val (e w) :=
        congrArg (fun k : ExternalParent G block d => BinaryValues.decode v1 k.val (e k))
          (show (⟨j, hjout, ⟨i, i.property, hji⟩⟩ : ExternalParent G block d) = w from Subtype.ext hjw)
      _ = z := hw
  · have hjm : block j = d := p.vertices_member hjp
    change BinaryValues.decode v1 j (parentAssign G val block d (x, e) i ⟨j, hji⟩) = z
    simp only [parentAssign, dif_pos hjm]
    rw [hx ⟨j, hjm⟩ hjp (ne_of_lt (p.copyParent_lt_terminal i.val hi))]
    exact BinaryValues.decode_encode v0 v1 j (hlevels ⟨j, hjm⟩) z

end MemberPath

namespace BellWitness

variable {wA wB : ExternalParent G block d} {a b : Member block d}
  (P : BellWitness G block d wA wB a b) (v0 v1 : FullAssign val)

noncomputable def sourceBitA (e : ExternalAssign G val block d) : Bool :=
  BinaryValues.decode v1 wA.val (e wA)

noncomputable def sourceBitB (e : ExternalAssign G val block d) : Bool :=
  BinaryValues.decode v1 wB.val (e wB)

/-- Intermediate members copy their own source bit; endpoints have the
separately specified output bits x and y; all remaining members are zero. -/
def binaryAssignment (zA zB x y : Bool) : MemberAssign val block d := fun i =>
  if i.val ∈ P.pathA.vertices then
    BinaryValues.encode v0 v1 i.val (if i = a then x else zA)
  else if i.val ∈ P.pathB.vertices then
    BinaryValues.encode v0 v1 i.val (if i = b then y else zB)
  else v0 i.val

noncomputable def copyingProfile (f g : Bool → Bool) : GlobalModel.Profile G val block d := by
  classical
  intro i pa
  exact if hi : i.val ∈ P.pathA.vertices then P.pathA.copyValue v0 v1 f i hi pa
    else if hi : i.val ∈ P.pathB.vertices then P.pathB.copyValue v0 v1 g i hi pa
    else v0 i.val

omit [DecidableEq D] in
theorem binaryAssignment_on_pathA (zA zB x y : Bool) (i : Member block d)
    (hi : i.val ∈ P.pathA.vertices) :
    P.binaryAssignment v0 v1 zA zB x y i =
      BinaryValues.encode v0 v1 i.val (if i = a then x else zA) := by
  simp only [binaryAssignment, if_pos hi]

omit [DecidableEq D] in
theorem binaryAssignment_on_pathB (zA zB x y : Bool) (i : Member block d)
    (hi : i.val ∈ P.pathB.vertices) :
    P.binaryAssignment v0 v1 zA zB x y i =
      BinaryValues.encode v0 v1 i.val (if i = b then y else zB) := by
  have hA : i.val ∉ P.pathA.vertices := fun h => Finset.disjoint_left.mp P.paths_disjoint h hi
  simp only [binaryAssignment, if_neg hA, if_pos hi]

omit [DecidableEq D] in
theorem binaryAssignment_at_A (zA zB x y : Bool) :
    P.binaryAssignment v0 v1 zA zB x y a = BinaryValues.encode v0 v1 a.val x := by
  simp only [P.binaryAssignment_on_pathA v0 v1 zA zB x y a P.pathA.endpoint_mem, ite_true]

omit [DecidableEq D] in
theorem binaryAssignment_at_B (zA zB x y : Bool) :
    P.binaryAssignment v0 v1 zA zB x y b = BinaryValues.encode v0 v1 b.val y := by
  simp only [P.binaryAssignment_on_pathB v0 v1 zA zB x y b P.pathB.endpoint_mem, ite_true]

/-- The full compact evaluation of the appendix's d_fg, at every external
assignment and with arbitrary additional observed state levels. -/
theorem eval_copyingProfile (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (f g : Bool → Bool) (e : ExternalAssign G val block d) :
    eval G val block d (P.copyingProfile v0 v1 f g) e =
      P.binaryAssignment v0 v1 (sourceBitA (wA := wA) v1 e) (sourceBitB (wB := wB) v1 e)
        (f (sourceBitA (wA := wA) v1 e)) (g (sourceBitB (wB := wB) v1 e)) := by
  classical
  let zA := sourceBitA (wA := wA) v1 e
  let zB := sourceBitB (wB := wB) v1 e
  let x := P.binaryAssignment v0 v1 zA zB (f zA) (g zB)
  apply (eval_eq_iff_compatible G val block d (x, e) (P.copyingProfile v0 v1 f g)).mpr
  intro i
  by_cases hiA : i.val ∈ P.pathA.vertices
  · simp only [copyingProfile, dif_pos hiA, MemberPath.copyValue]
    have hread := P.pathA.read_copyParent_of_values v0 v1 hlevels x e zA rfl
      (fun j hj hja => by
        have hne : j ≠ a := fun h => hja (congrArg Subtype.val h)
        exact (P.binaryAssignment_on_pathA v0 v1 zA zB (f zA) (g zB) j hj).trans
          (by rw [if_neg hne])) i hiA
    rw [hread]
    change _ = P.binaryAssignment v0 v1 zA zB (f zA) (g zB) i
    rw [P.binaryAssignment_on_pathA v0 v1 zA zB (f zA) (g zB) i hiA]
    have heq : (i.val = a.val) ↔ i = a := ⟨Subtype.ext, congrArg Subtype.val⟩
    simp only [heq]
  · simp only [copyingProfile, dif_neg hiA]
    by_cases hiB : i.val ∈ P.pathB.vertices
    · simp only [dif_pos hiB, MemberPath.copyValue]
      have hread := P.pathB.read_copyParent_of_values v0 v1 hlevels x e zB rfl
        (fun j hj hjb => by
          have hne : j ≠ b := fun h => hjb (congrArg Subtype.val h)
          exact (P.binaryAssignment_on_pathB v0 v1 zA zB (f zA) (g zB) j hj).trans
            (by rw [if_neg hne])) i hiB
      rw [hread]
      change _ = P.binaryAssignment v0 v1 zA zB (f zA) (g zB) i
      rw [P.binaryAssignment_on_pathB v0 v1 zA zB (f zA) (g zB) i hiB]
      have heq : (i.val = b.val) ↔ i = b := ⟨Subtype.ext, congrArg Subtype.val⟩
      simp only [heq]
    · simp only [dif_neg hiB]
      exact (show x i = v0 i.val by simp only [x, binaryAssignment, if_neg hiA, if_neg hiB]).symm

theorem eval_copyingProfile_at_A (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (f g : Bool → Bool) (e : ExternalAssign G val block d) :
    eval G val block d (P.copyingProfile v0 v1 f g) e a =
      BinaryValues.encode v0 v1 a.val (f (sourceBitA (wA := wA) v1 e)) := by
  rw [P.eval_copyingProfile v0 v1 hlevels, P.binaryAssignment_at_A]

theorem eval_copyingProfile_at_B (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (f g : Bool → Bool) (e : ExternalAssign G val block d) :
    eval G val block d (P.copyingProfile v0 v1 f g) e b =
      BinaryValues.encode v0 v1 b.val (g (sourceBitB (wB := wB) v1 e)) := by
  rw [P.eval_copyingProfile v0 v1 hlevels, P.binaryAssignment_at_B]

/-- The actual compatibility column, retaining all surrounding member values. -/
theorem matrix_copyingProfile [∀ i, DecidableEq (val i)]
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (f g : Bool → Bool) (row : Row G val block d) :
    matrix G val block d row (P.copyingProfile v0 v1 f g) =
      if P.binaryAssignment v0 v1 (sourceBitA (wA := wA) v1 row.2) (sourceBitB (wB := wB) v1 row.2)
          (f (sourceBitA (wA := wA) v1 row.2)) (g (sourceBitB (wB := wB) v1 row.2)) = row.1
        then 1 else 0 := by
  rw [matrix_eq_eval, P.eval_copyingProfile v0 v1 hlevels]

end BellWitness
end MeraConstraints.CompactDistrict
