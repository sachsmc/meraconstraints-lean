import MeraConstraints.CompactDistrict.BellStructure
import MeraConstraints.CompactDistrict.InstrumentalProfiles

/-!
# The profiles for type (ii)

This is the construction of the columns `d_{fg}` in Step 3 of the proof of Remark 3
(`prop:ineqstructure`), type (ii), for `f, g : {0, 1} → {0, 1}`. As for type (i), `v0`
and `v1` provide the values labeled `0` and `1`, and `α` (`sourceBitA`) and `β`
(`sourceBitB`) are the indicators that `W_A` and `W_B` take their values in `v1`.
In the profile `copyingProfile f g`, the vertices `Y₁, …, Y_r` copy `α`, the vertices
`X₁, …, X_s` copy `β`, `A` applies `f` to the value it copies, `B` applies `g` to the
value it copies, and every other member is `0`.

`eval_copyingProfile` computes the values this profile gives the members at every
`v₂`: the path vertices other than `A` and `B` equal `α` or `β`, `A = f α`, `B = g β`,
and the others are `0`. The two paths are disjoint, so the copying on one path does not
interfere with the other. The theorem needs only that `v0` and `v1` differ at every
member.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}

namespace MemberPath

variable {w : ExternalParent G block d} {v : Fin n}
  (p : MemberPath G block d w.val v) (v0 v1 : FullAssign val)

/-- The response function of a path vertex: it reads the parent chosen by
`copyParent` and copies its bit, except that the endpoint `v` applies `f` to it. -/
noncomputable def copyValue (f : Bool → Bool) (i : Member block d)
    (hi : i.val ∈ p.vertices) (pa : PaAssign G val i.val) : val i.val :=
  let j := p.copyParent i.val hi
  let z := BinaryValues.decode v1 j (pa ⟨j, p.copyParent_mem i.val hi⟩)
  BinaryValues.encode v0 v1 i.val (if i.val = v then f z else z)

/-- If the source takes the bit `z` and every path vertex other than the endpoint has
the bit `z`, then the parent chosen by `copyParent` for any path vertex has the bit
`z`. The value at the endpoint does not matter. -/
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

/-- The members' values in which the vertices on the first path other than `A` have
the bit `zA`, those on the second path other than `B` have the bit `zB`, `A` has the
bit `x`, `B` has the bit `y`, and every other member has the value in `v0`. -/
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

/-- The values that `copyingProfile f g` gives the members at `v₂ = e`: the first
path copies `α`, the second copies `β`, `A` has the bit `f α`, `B` has the bit
`g β`, and the other members take the value in `v0`. -/
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

/-- The column `d_{fg}` of `B`: the entry at row `(v₁, v₂)` is `1` if `v₁` is the
assignment of `eval_copyingProfile` at `v₂`, and `0` otherwise. -/
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
