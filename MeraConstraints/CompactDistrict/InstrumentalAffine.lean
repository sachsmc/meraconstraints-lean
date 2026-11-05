import MeraConstraints.CompactDistrict.InstrumentalProfiles
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.Ring

/-!
# The vector `t` for type (i) lies in the affine hull

This is the identity `t = a + b - c` in Step 3 of the proof of Remark 3
(`prop:ineqstructure`), type (i). The columns `a`, `b` and `c` of the matrix `B` are
those of the profiles `profileA`, `profileB` and `profileC` of the previous chapter.
In `t` (`instrumentalTarget`), `Z₁, …, Z_r` equal `ζ`, `A = 0`, `B = ζ`, and every
other member is `0`.

For `ζ = 0`, `t` is `a` and `b - c` is zero. For `ζ = 1`, `t` is `b` and `a - c` is
zero. This gives `t = a + b - c` at every row (`instrumentalTarget_eq_columns`),
so `t` lies in the affine hull of the columns of `B`
(`instrumentalTarget_mem_affineSpan_columns`) and of the district polytope. Each block
`t(· ∣ v₂)` is a probability vector (`instrumentalTarget_block_probability`), so `t`
lies in the cross-product of probability simplices.
-/

namespace MeraConstraints.CompactDistrict.InstrumentalWitness

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}
  {w : ExternalParent G block d} {a b : Member block d}
  (P : InstrumentalWitness G block d w a b) (v0 v1 : FullAssign val)

noncomputable def profileA : GlobalModel.Profile G val block d := P.copyingProfile v0 v1 id id
noncomputable def profileB : GlobalModel.Profile G val block d := P.copyingProfile v0 v1 Bool.not (fun _ => true)
noncomputable def profileC : GlobalModel.Profile G val block d := P.copyingProfile v0 v1 (fun _ => true) (fun _ => true)

noncomputable def assignmentColumn (z x y : Bool) (o : MemberAssign val block d) : ℝ := by
  classical
  exact if P.binaryAssignment v0 v1 z x y = o then 1 else 0

noncomputable def instrumentalTarget (row : Row G val block d) : ℝ :=
  P.assignmentColumn v0 v1 (sourceBit (w := w) v1 row.2) false (sourceBit (w := w) v1 row.2) row.1

/-- The identity `t = a + b - c` for the indicators of the members' values, with
`z = ζ`. -/
theorem assignmentColumn_affine (z : Bool) (o : MemberAssign val block d) :
    P.assignmentColumn v0 v1 z false z o =
      P.assignmentColumn v0 v1 z z z o + P.assignmentColumn v0 v1 z (!z) true o -
        P.assignmentColumn v0 v1 z true true o := by
  cases z <;> simp only [Bool.not_false, Bool.not_true] <;> ring

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [∀ i, Fintype (val i)] in
theorem matrix_copyingProfile (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (f g : Bool → Bool) (row : Row G val block d) :
    matrix G val block d row (P.copyingProfile v0 v1 f g) =
      P.assignmentColumn v0 v1 (sourceBit (w := w) v1 row.2)
        (f (sourceBit (w := w) v1 row.2)) (g (f (sourceBit (w := w) v1 row.2))) row.1 := by
  classical
  rw [matrix_eq_eval, P.eval_copyingProfile v0 v1 hlevels]
  unfold assignmentColumn
  split_ifs <;> rfl

omit [∀ i, Fintype (val i)] in
/-- `t = a + b - c` at every row `(v₁, v₂)`. -/
theorem instrumentalTarget_eq_columns (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (row : Row G val block d) :
    P.instrumentalTarget v0 v1 row =
      matrix G val block d row (P.profileA v0 v1) + matrix G val block d row (P.profileB v0 v1) -
        matrix G val block d row (P.profileC v0 v1) := by
  rw [profileA, profileB, profileC, P.matrix_copyingProfile v0 v1 hlevels,
    P.matrix_copyingProfile v0 v1 hlevels, P.matrix_copyingProfile v0 v1 hlevels]
  exact P.assignmentColumn_affine v0 v1 _ _

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem instrumentalTarget_zero_one (row : Row G val block d) :
    P.instrumentalTarget v0 v1 row = 0 ∨ P.instrumentalTarget v0 v1 row = 1 := by
  classical
  unfold instrumentalTarget assignmentColumn
  split <;> simp

theorem instrumentalTarget_block_probability (e : ExternalAssign G val block d) :
    (fun o => P.instrumentalTarget v0 v1 (o, e)) ∈ stdSimplex ℝ (MemberAssign val block d) := by
  classical
  have hs := ite_eq_mem_stdSimplex ℝ (P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e)
    false (sourceBit (w := w) v1 e))
  convert hs using 1
  funext o
  unfold instrumentalTarget assignmentColumn
  split_ifs <;> rfl

omit [∀ i, Fintype (val i)] in
theorem instrumentalTarget_mem_affineSpan_columns
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val) :
    P.instrumentalTarget v0 v1 ∈ affineSpan ℝ
      (Set.range fun r : GlobalModel.Profile G val block d => fun row : Row G val block d => matrix G val block d row r) := by
  have hcol (r : GlobalModel.Profile G val block d) :
      (fun row : Row G val block d => matrix G val block d row r) ∈ affineSpan ℝ
        (Set.range fun r : GlobalModel.Profile G val block d => fun row : Row G val block d => matrix G val block d row r) :=
    subset_affineSpan ℝ _ ⟨r, rfl⟩
  have hm := AffineSubspace.vadd_mem_of_mem_direction
    (AffineSubspace.vsub_mem_direction (hcol (P.profileA v0 v1)) (hcol (P.profileC v0 v1)))
    (hcol (P.profileB v0 v1))
  convert hm using 1
  funext row
  change P.instrumentalTarget v0 v1 row =
    matrix G val block d row (P.profileA v0 v1) - matrix G val block d row (P.profileC v0 v1) +
      matrix G val block d row (P.profileB v0 v1)
  rw [P.instrumentalTarget_eq_columns v0 v1 hlevels]
  ring

theorem instrumentalTarget_mem_affineSpan_mixture
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val) :
    P.instrumentalTarget v0 v1 ∈ affineSpan ℝ (Polytope.mixture (matrix G val block d)) := by
  rw [Polytope.mixture_eq_convexHull, affineSpan_convexHull]
  exact P.instrumentalTarget_mem_affineSpan_columns v0 v1 hlevels

end MeraConstraints.CompactDistrict.InstrumentalWitness
