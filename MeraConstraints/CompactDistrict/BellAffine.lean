import MeraConstraints.CompactDistrict.BellProfiles
import MeraConstraints.Examples.BellAffine

/-!
# The vector `t` for type (ii) lies in the affine hull

This is the construction of `t` and the identity `t = Σ λ_{fg} d_{fg}` in Step 3 of
the proof of Remark 3 (`prop:ineqstructure`), type (ii). At every `v₂`, the path
vertices and the other members have the values they have in the columns `d_{fg}`, and
`(A, B)` has the distribution `Pr(A = a, B = b) = 1/2` if `a ⊕ b = αβ`, and `0`
otherwise (`Examples.Bell.prBox`, the PR box). `bellTarget` is this vector `t`: the
distribution of `(A, B)` pushed forward to the complete assignment of the members.

The weights `λ_{fg}` are `3/16` and `-1/16` (`Examples.Bell.affineWeight`) and sum to
one. The identity for the two-variable PR box (`Examples.Bell.signed_mixture_eq_prBox`)
carries over through this map to an identity at every row of `B`
(`bellTarget_eq_signed_columns`). So `t` lies in the affine hull of the columns of
`B` and of the district polytope (`bellTarget_mem_affineSpan_mixture`). Each block
`t(· ∣ v₂)` is a probability vector (`bellTarget_block_probability`), so `t` lies in the
cross-product of probability simplices.
-/

namespace MeraConstraints.CompactDistrict.BellWitness

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}
  {wA wB : ExternalParent G block d} {a b : Member block d}
  (P : BellWitness G block d wA wB a b) (v0 v1 : FullAssign val)

noncomputable def assignmentColumn (zA zB : Bool) (o : Examples.Bell.Output)
    (x : MemberAssign val block d) : ℝ := by
  classical
  exact if P.binaryAssignment v0 v1 zA zB o.1 o.2 = x then 1 else 0

/-- The vector `t`: at row `(v₁, v₂)`, the probability that the PR box puts on the
bits of `(A, B)` that give the members the values `v₁`. -/
noncomputable def bellTarget (row : Row G val block d) : ℝ :=
  let zA := sourceBitA (wA := wA) v1 row.2
  let zB := sourceBitB (wB := wB) v1 row.2
  ∑ o : Examples.Bell.Output, Examples.Bell.prBox (zA, zB) o *
    P.assignmentColumn v0 v1 zA zB o row.1

omit [DecidableEq D] in
theorem binaryAssignment_injective (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (zA zB : Bool) :
    Function.Injective (fun o : Examples.Bell.Output => P.binaryAssignment v0 v1 zA zB o.1 o.2) := by
  intro o o' h
  apply Prod.ext
  · have hh := congrArg (fun x : MemberAssign val block d => BinaryValues.decode v1 a.val (x a)) h
    simpa only [P.binaryAssignment_at_A, BinaryValues.decode_encode v0 v1 a.val (hlevels a)] using hh
  · have hh := congrArg (fun x : MemberAssign val block d => BinaryValues.decode v1 b.val (x b)) h
    simpa only [P.binaryAssignment_at_B, BinaryValues.decode_encode v0 v1 b.val (hlevels b)] using hh

/-- At the assignment with endpoint bits `o`, `t` is the PR box probability of `o`:
`1/2` if `o` wins the parity game at `(α, β)`, and `0` otherwise. -/
theorem bellTarget_at_assignment
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (e : ExternalAssign G val block d) (o : Examples.Bell.Output) :
    P.bellTarget v0 v1
      (P.binaryAssignment v0 v1 (sourceBitA (wA := wA) v1 e)
        (sourceBitB (wB := wB) v1 e) o.1 o.2, e) =
      Examples.Bell.prBox (sourceBitA (wA := wA) v1 e, sourceBitB (wB := wB) v1 e) o := by
  classical
  simp only [bellTarget, assignmentColumn, (P.binaryAssignment_injective v0 v1 hlevels _ _).eq_iff]
  simp

theorem bellTarget_eq_zero_of_outside (row : Row G val block d)
    (h : ∀ o : Examples.Bell.Output,
      P.binaryAssignment v0 v1 (sourceBitA (wA := wA) v1 row.2)
        (sourceBitB (wB := wB) v1 row.2) o.1 o.2 ≠ row.1) :
    P.bellTarget v0 v1 row = 0 := by
  simp only [bellTarget, assignmentColumn, if_neg (h _), mul_zero, Finset.sum_const_zero]

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [∀ i, Fintype (val i)] in
/-- The column `d_{fg}` is the two-variable column of the binary Bell model carried
to the assignment of the members. -/
theorem matrix_copyingProfile_eq_pushforward
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (r : Examples.Bell.Profile) (row : Row G val block d) :
    matrix G val block d row (P.copyingProfile v0 v1 r.1 r.2) =
      ∑ o : Examples.Bell.Output,
        Examples.Bell.matrix
          ((sourceBitA (wA := wA) v1 row.2, sourceBitB (wB := wB) v1 row.2), o) r *
          P.assignmentColumn v0 v1 (sourceBitA (wA := wA) v1 row.2)
            (sourceBitB (wB := wB) v1 row.2) o row.1 := by
  classical
  rw [P.matrix_copyingProfile v0 v1 hlevels]
  simp only [Examples.Bell.matrix, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold assignmentColumn
  split_ifs <;> rfl

omit [∀ i, Fintype (val i)] in
/-- `t = Σ λ_{fg} d_{fg}` at every row `(v₁, v₂)`. -/
theorem bellTarget_eq_signed_columns
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val) (row : Row G val block d) :
    P.bellTarget v0 v1 row =
      ∑ r : Examples.Bell.Profile, Examples.Bell.affineWeight r *
        matrix G val block d row (P.copyingProfile v0 v1 r.1 r.2) := by
  classical
  symm
  simp_rw [P.matrix_copyingProfile_eq_pushforward v0 v1 hlevels]
  rw [show (∑ r : Examples.Bell.Profile, Examples.Bell.affineWeight r *
      ∑ o : Examples.Bell.Output,
        Examples.Bell.matrix ((sourceBitA (wA := wA) v1 row.2, sourceBitB (wB := wB) v1 row.2), o) r *
          P.assignmentColumn v0 v1 (sourceBitA (wA := wA) v1 row.2)
            (sourceBitB (wB := wB) v1 row.2) o row.1) =
      ∑ o : Examples.Bell.Output, (∑ r : Examples.Bell.Profile, Examples.Bell.affineWeight r *
        Examples.Bell.matrix ((sourceBitA (wA := wA) v1 row.2, sourceBitB (wB := wB) v1 row.2), o) r) *
          P.assignmentColumn v0 v1 (sourceBitA (wA := wA) v1 row.2)
            (sourceBitB (wB := wB) v1 row.2) o row.1 by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]]
  simp_rw [Examples.Bell.signed_mixture_eq_prBox]
  rfl

theorem bellTarget_block_probability (e : ExternalAssign G val block d) :
    (fun x => P.bellTarget v0 v1 (x, e)) ∈ stdSimplex ℝ (MemberAssign val block d) := by
  classical
  let zA := sourceBitA (wA := wA) v1 e
  let zB := sourceBitB (wB := wB) v1 e
  have hcol (o : Examples.Bell.Output) :
      P.assignmentColumn v0 v1 zA zB o ∈ stdSimplex ℝ (MemberAssign val block d) := by
    convert (ite_eq_mem_stdSimplex ℝ (P.binaryAssignment v0 v1 zA zB o.1 o.2)) using 1
    funext x
    unfold assignmentColumn
    split_ifs <;> rfl
  constructor
  · intro x
    exact Finset.sum_nonneg fun o _ => mul_nonneg
      ((Examples.Bell.prBox_mem_stdSimplex (zA, zB)).1 o) ((hcol o).1 x)
  · change (∑ x, ∑ o : Examples.Bell.Output, Examples.Bell.prBox (zA, zB) o *
      P.assignmentColumn v0 v1 zA zB o x) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (hcol _).2, mul_one]
    exact (Examples.Bell.prBox_mem_stdSimplex (zA, zB)).2

omit [∀ i, Fintype (val i)] in
theorem bellTarget_mem_affineSpan_columns
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val) :
    P.bellTarget v0 v1 ∈ affineSpan ℝ
      (Set.range fun r : GlobalModel.Profile G val block d =>
        fun row : Row G val block d => matrix G val block d row r) := by
  classical
  have hw : ∑ r ∈ (Finset.univ : Finset Examples.Bell.Profile), Examples.Bell.affineWeight r = 1 :=
    Examples.Bell.sum_affineWeight
  have hm := affineCombination_mem_affineSpan hw
    (fun r : Examples.Bell.Profile => fun row : Row G val block d =>
      matrix G val block d row (P.copyingProfile v0 v1 r.1 r.2))
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hm
  have heq : P.bellTarget v0 v1 = ∑ r : Examples.Bell.Profile,
      Examples.Bell.affineWeight r •
        (fun row : Row G val block d => matrix G val block d row (P.copyingProfile v0 v1 r.1 r.2)) := by
    funext row
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      P.bellTarget_eq_signed_columns v0 v1 hlevels row
  rw [← heq] at hm
  exact (affineSpan_mono ℝ (by
    rintro _ ⟨r, rfl⟩
    exact ⟨P.copyingProfile v0 v1 r.1 r.2, rfl⟩)) hm

theorem bellTarget_mem_affineSpan_mixture
    (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val) :
    P.bellTarget v0 v1 ∈ affineSpan ℝ (Polytope.mixture (matrix G val block d)) := by
  rw [Polytope.mixture_eq_convexHull, affineSpan_convexHull]
  exact P.bellTarget_mem_affineSpan_columns v0 v1 hlevels

end MeraConstraints.CompactDistrict.BellWitness
