import MeraConstraints.CompactDistrict.BellAffine

/-!
# The vector `t` for type (ii) is not in the district polytope

This is the last part of Step 3 of the proof of Remark 3 (`prop:ineqstructure`), type
(ii): the CHSH inequality holds on the district polytope, and `t` violates it. Fix the
external parents other than `W_A` and `W_B` at reference values, and let `W_A` and
`W_B` take their values labeled `0` and `1` (`referenceInput`).

By Step 1 (`Reachability`), in every profile the value of `A` does not depend on
`W_B`, and the value of `B` does not depend on `W_A`. So at the four reference values,
`1{A = 1}` is `f(α)` and `1{B = 1}` is `g(β)` for some `f` and `g`, and the score
`S(p)` (`gameScore`) is at most 3 at every column of `B`. Since `S` is linear, `S ≤ 3`
on the district polytope (`gameScore_le_three`). But `S(t) = 4` (`bellTarget_gameScore`),
so `t` is not in the polytope (`bellTarget_not_mem_mixture`). With the previous
chapter, `bell_affine_witness` shows that `t` lies in the cross-product of
probability simplices and in the affine hull of the district polytope, but not in the
polytope. The step from this to a nontrivial inequality is in
`HiddenGraph.BellInequalities`.
-/

namespace MeraConstraints.CompactDistrict.BellWitness

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}
  {wA wB : ExternalParent G block d} {a b : Member block d}

/-- The four values `v₂^{αβ}` of the external parents: `W_A` and `W_B` take the
values labeled `α` and `β`, and the others take their value in `v0`. -/
noncomputable def referenceInput (_P : BellWitness G block d wA wB a b)
    (v0 v1 : FullAssign val) (u : Examples.Bell.Input) : ExternalAssign G val block d := by
  classical
  exact fun j => if j = wA then BinaryValues.encode v0 v1 j.val u.1 else
    if j = wB then BinaryValues.encode v0 v1 j.val u.2 else v0 j.val

/-- The pair of bits `(1{A = 1}, 1{B = 1})` of an assignment of the members. -/
noncomputable def outputBits (_P : BellWitness G block d wA wB a b)
    (v1 : FullAssign val) (x : MemberAssign val block d) : Examples.Bell.Output :=
  (BinaryValues.decode v1 a.val (x a), BinaryValues.decode v1 b.val (x b))

variable (P : BellWitness G block d wA wB a b) (v0 v1 : FullAssign val)

omit [DecidableEq D] in
theorem reference_source_bits (hWA : v0 wA.val ≠ v1 wA.val) (hWB : v0 wB.val ≠ v1 wB.val)
    (u : Examples.Bell.Input) :
    sourceBitA (wA := wA) v1 (P.referenceInput v0 v1 u) = u.1 ∧
      sourceBitB (wB := wB) v1 (P.referenceInput v0 v1 u) = u.2 := by
  classical
  constructor
  · change BinaryValues.decode v1 wA.val (P.referenceInput v0 v1 u wA) = u.1
    simp only [referenceInput]
    exact BinaryValues.decode_encode v0 v1 wA.val hWA u.1
  · change BinaryValues.decode v1 wB.val (P.referenceInput v0 v1 u wB) = u.2
    simp only [referenceInput, if_neg P.sources_ne.symm]
    exact BinaryValues.decode_encode v0 v1 wB.val hWB u.2

/-- In every profile, changing only `W_B` does not change the value of `A`. -/
theorem eval_reference_A (r : GlobalModel.Profile G val block d) (u : Examples.Bell.Input) :
    eval G val block d r (P.referenceInput v0 v1 u) a =
      eval G val block d r (P.referenceInput v0 v1 (u.1, false)) a := by
  classical
  apply eval_eq_of_change_unreached G block d val r _ _ wB a P.not_reach_A
  intro j hj
  simp only [referenceInput, if_neg hj]

/-- In every profile, changing only `W_A` does not change the value of `B`. -/
theorem eval_reference_B (r : GlobalModel.Profile G val block d) (u : Examples.Bell.Input) :
    eval G val block d r (P.referenceInput v0 v1 u) b =
      eval G val block d r (P.referenceInput v0 v1 (false, u.2)) b := by
  classical
  apply eval_eq_of_change_unreached G block d val r _ _ wA b P.not_reach_B
  intro j hj
  simp only [referenceInput, if_neg hj]

noncomputable def responseProfile (r : GlobalModel.Profile G val block d) : Examples.Bell.Profile :=
  (fun z => BinaryValues.decode v1 a.val (eval G val block d r (P.referenceInput v0 v1 (z, false)) a),
   fun z => BinaryValues.decode v1 b.val (eval G val block d r (P.referenceInput v0 v1 (false, z)) b))

theorem outputBits_eval (r : GlobalModel.Profile G val block d) (u : Examples.Bell.Input) :
    P.outputBits v1 (eval G val block d r (P.referenceInput v0 v1 u)) =
      ((P.responseProfile v0 v1 r).1 u.1, (P.responseProfile v0 v1 r).2 u.2) := by
  unfold outputBits responseProfile
  rw [P.eval_reference_A v0 v1 r u, P.eval_reference_B v0 v1 r u]

omit [DecidableEq D] in
theorem outputBits_binaryAssignment (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (zA zB : Bool) (o : Examples.Bell.Output) :
    P.outputBits v1 (P.binaryAssignment v0 v1 zA zB o.1 o.2) = o := by
  unfold outputBits
  rw [P.binaryAssignment_at_A, P.binaryAssignment_at_B,
    BinaryValues.decode_encode v0 v1 a.val (hlevels a),
    BinaryValues.decode_encode v0 v1 b.val (hlevels b)]

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The CHSH score `S(p)`: the sum over the four values of `v₂^{αβ}` of the
probability that `1{A = 1} ⊕ 1{B = 1} = αβ`. -/
noncomputable def gameScore (p : Row G val block d → ℝ) : ℝ :=
  ∑ u : Examples.Bell.Input, ∑ x : MemberAssign val block d,
    Examples.Bell.win (P.outputBits v1 x).1 (P.outputBits v1 x).2 u.1 u.2 *
      p (x, P.referenceInput v0 v1 u)

theorem gameScore_column (r : GlobalModel.Profile G val block d) :
    P.gameScore v0 v1 (fun row => matrix G val block d row r) =
      Examples.Bell.score (P.responseProfile v0 v1 r) := by
  classical
  unfold gameScore
  simp only [matrix_eq_eval, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [P.outputBits_eval v0 v1 r]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Examples.Bell.score]
  ring

theorem gameScore_column_le_three (r : GlobalModel.Profile G val block d) :
    P.gameScore v0 v1 (fun row => matrix G val block d row r) ≤ 3 := by
  rw [P.gameScore_column v0 v1 r]
  exact Examples.Bell.score_le_three _

/-- `S` is linear, so its value at a mixture of columns is the corresponding mixture
of its values at the columns. -/
theorem gameScore_mulVec (q : GlobalModel.Profile G val block d → ℝ) :
    P.gameScore v0 v1 ((matrix G val block d).mulVec q) =
      ∑ r, q r * P.gameScore v0 v1 (fun row => matrix G val block d row r) := by
  classical
  simp only [gameScore, Matrix.mulVec, dotProduct, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem gameScore_le_three {p : Row G val block d → ℝ}
    (hp : p ∈ Polytope.mixture (matrix G val block d)) : P.gameScore v0 v1 p ≤ 3 := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [P.gameScore_mulVec v0 v1]
  calc
    _ ≤ ∑ r, q r * 3 := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left (P.gameScore_column_le_three v0 v1 r) (hq.1 r)
    _ = 3 := by rw [← Finset.sum_mul, hq.2, one_mul]

theorem bellTarget_gameScore (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (hWA : v0 wA.val ≠ v1 wA.val) (hWB : v0 wB.val ≠ v1 wB.val) :
    P.gameScore v0 v1 (P.bellTarget v0 v1) = 4 := by
  classical
  have hblock (u : Examples.Bell.Input) :
      (∑ x : MemberAssign val block d,
        Examples.Bell.win (P.outputBits v1 x).1 (P.outputBits v1 x).2 u.1 u.2 *
          P.bellTarget v0 v1 (x, P.referenceInput v0 v1 u)) = 1 := by
    simp only [bellTarget, (P.reference_source_bits v0 v1 hWA hWB u).1,
      (P.reference_source_bits v0 v1 hWA hWB u).2, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm (o : Examples.Bell.Output) :
        (∑ x : MemberAssign val block d,
          Examples.Bell.win (P.outputBits v1 x).1 (P.outputBits v1 x).2 u.1 u.2 *
            (Examples.Bell.prBox u o * P.assignmentColumn v0 v1 u.1 u.2 o x)) =
          Examples.Bell.prBox u o * Examples.Bell.win o.1 o.2 u.1 u.2 := by
      simp only [assignmentColumn, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [P.outputBits_binaryAssignment v0 v1 hlevels]
      ring
    simp_rw [hterm]
    exact Examples.Bell.prBox_wins u
  simp only [gameScore, hblock, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

theorem bellTarget_not_mem_mixture (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (hWA : v0 wA.val ≠ v1 wA.val) (hWB : v0 wB.val ≠ v1 wB.val) :
    P.bellTarget v0 v1 ∉ Polytope.mixture (matrix G val block d) := by
  intro hp
  have h := P.gameScore_le_three v0 v1 hp
  rw [P.bellTarget_gameScore v0 v1 hlevels hWA hWB] at h
  norm_num at h

/-- The vector `t` of type (ii) lies in the cross-product of probability simplices and
in the affine hull of the district polytope, but not in the polytope. -/
theorem bell_affine_witness (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (hWA : v0 wA.val ≠ v1 wA.val) (hWB : v0 wB.val ≠ v1 wB.val) :
    (∀ e : ExternalAssign G val block d,
      (fun x => P.bellTarget v0 v1 (x, e)) ∈ stdSimplex ℝ (MemberAssign val block d)) ∧
    P.bellTarget v0 v1 ∈ affineSpan ℝ (Polytope.mixture (matrix G val block d)) ∧
    P.bellTarget v0 v1 ∉ Polytope.mixture (matrix G val block d) :=
  ⟨P.bellTarget_block_probability v0 v1, P.bellTarget_mem_affineSpan_mixture v0 v1 hlevels,
    P.bellTarget_not_mem_mixture v0 v1 hlevels hWA hWB⟩

end MeraConstraints.CompactDistrict.BellWitness
