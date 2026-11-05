import MeraConstraints.CompactDistrict.InstrumentalAffine
import MeraConstraints.Polytope.ZeroOne

/-!
# The vector `t` for type (i) is not in the district polytope

This is the last part of Step 3 of the proof of Remark 3 (`prop:ineqstructure`), type
(i): `t ∉ 𝒫_D`. Take two values of `v₂` that differ only in `W`, taking the values
labeled `0` and `1`. In `t`, `A` is `0` at both, `Z₁, …, Z_r` copy `W`, `B` equals `ζ`,
and the other members are `0`. Since `W`, `Z₁, …, Z_r` are not parents of `B`, no
single profile gives both blocks of `t` (`instrumentalTarget_not_profile`).

A point of the district polytope with all entries `0` or `1` is a column of `B`
(`Polytope.zero_one_mixture_is_column`), and `t` has all entries `0` or `1`, so `t` is
not in the polytope (`instrumentalTarget_not_mem_mixture`). Together with the previous
chapter, `instrumental_affine_witness` shows that `t` lies in the cross-product of
probability simplices and in the affine hull of the district polytope, but not in the
polytope. The step from this to a nontrivial inequality is in
`HiddenGraph.InstrumentalInequalities`.
-/

namespace MeraConstraints.CompactDistrict.InstrumentalWitness

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}
  {w : ExternalParent G block d} {a b : Member block d}
  (P : InstrumentalWitness G block d w a b) (v0 v1 : FullAssign val)

omit [DecidableEq D] in
/-- The members' values in `t` at `ζ = 0` and at `ζ = 1` agree except at `B` and
`Z₁, …, Z_r`. In particular `A` is `0` in both. -/
theorem target_assignments_agree_off_path (i : Member block d)
    (hi : i.val ∉ insert b.val P.intermediates) :
    P.binaryAssignment v0 v1 false false false i = P.binaryAssignment v0 v1 true false true i := by
  classical
  have hib : i ≠ b := fun h => hi (h.symm ▸ Finset.mem_insert_self _ _)
  have hmid : i.val ∉ P.intermediates := fun hm => hi (Finset.mem_insert_of_mem hm)
  by_cases hia : i = a
  · subst i
    rw [P.binaryAssignment_at_treatment, P.binaryAssignment_at_treatment]
  · simp only [binaryAssignment, if_neg hia, if_neg hib, if_neg hmid]

/-- No single profile produces the members' values of `t` at every value of `v₂`.
This needs only that `v0` and `v1` differ at `W` and at `B`. -/
theorem instrumentalTarget_not_profile
    (hW : v0 w.val ≠ v1 w.val) (hB : v0 b.val ≠ v1 b.val) :
    ¬ ∃ r : GlobalModel.Profile G val block d,
      ∀ e : ExternalAssign G val block d,
        eval G val block d r e = P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e)
          false (sourceBit (w := w) v1 e) := by
  classical
  rintro ⟨r, hr⟩
  let e0 : ExternalAssign G val block d := fun j => v0 j.val
  let e1 : ExternalAssign G val block d := Function.update e0 w (v1 w.val)
  have hz0 : sourceBit (w := w) v1 e0 = false := by
    change BinaryValues.decode v1 w.val (v0 w.val) = false
    exact BinaryValues.decode_encode v0 v1 w.val hW false
  have hz1 : sourceBit (w := w) v1 e1 = true := by
    simp [sourceBit, e1, BinaryValues.decode]
  have he : ∀ j : ExternalParent G block d, j ≠ w → e0 j = e1 j := by
    intro j hj
    simp only [e1, Function.update_of_ne hj]
  have hc0 : Compatible G val block d (P.binaryAssignment v0 v1 false false false, e0) r := by
    apply (eval_eq_iff_compatible G val block d _ r).mp
    simpa only [hz0] using hr e0
  have hc1 : Compatible G val block d (P.binaryAssignment v0 v1 true false true, e1) r := by
    apply (eval_eq_iff_compatible G val block d _ r).mp
    simpa only [hz1] using hr e1
  have hb : P.binaryAssignment v0 v1 false false false b ≠ P.binaryAssignment v0 v1 true false true b := by
    rw [P.binaryAssignment_at_outcome, P.binaryAssignment_at_outcome]
    exact hB
  exact P.not_both_compatible val _ _ e0 e1 he (P.target_assignments_agree_off_path v0 v1) hb ⟨r, hc0, hc1⟩

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [∀ i, Fintype (val i)] in
/-- No column of `B` equals `t`. -/
theorem instrumentalTarget_not_column (hW : v0 w.val ≠ v1 w.val) (hB : v0 b.val ≠ v1 b.val) :
    ¬ ∃ r : GlobalModel.Profile G val block d,
      ∀ row : Row G val block d, matrix G val block d row r = P.instrumentalTarget v0 v1 row := by
  classical
  rintro ⟨r, hr⟩
  apply P.instrumentalTarget_not_profile v0 v1 hW hB
  refine ⟨r, fun e => ?_⟩
  let x := P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e) false (sourceBit (w := w) v1 e)
  have h := hr (x, e)
  have ht : P.instrumentalTarget v0 v1 (x, e) = 1 := by
    simp [instrumentalTarget, assignmentColumn, x]
  rw [matrix_eq_eval, ht] at h
  split_ifs at h with heq
  · exact heq
  · norm_num at h

theorem instrumentalTarget_not_mem_mixture (hW : v0 w.val ≠ v1 w.val) (hB : v0 b.val ≠ v1 b.val) :
    P.instrumentalTarget v0 v1 ∉ Polytope.mixture (matrix G val block d) := by
  intro hm
  have hbounds : ∀ row r, 0 ≤ matrix G val block d row r ∧ matrix G val block d row r ≤ 1 := by
    classical
    intro row r
    rw [matrix_eq_eval]
    split_ifs <;> norm_num
  exact P.instrumentalTarget_not_column v0 v1 hW hB
    (Polytope.zero_one_mixture_is_column _ _ hbounds (P.instrumentalTarget_zero_one v0 v1) hm)

theorem instrumental_affine_witness (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (hW : v0 w.val ≠ v1 w.val) :
    (∀ e : ExternalAssign G val block d,
      (fun o => P.instrumentalTarget v0 v1 (o, e)) ∈ stdSimplex ℝ (MemberAssign val block d)) ∧
    P.instrumentalTarget v0 v1 ∈ affineSpan ℝ (Polytope.mixture (matrix G val block d)) ∧
    P.instrumentalTarget v0 v1 ∉ Polytope.mixture (matrix G val block d) :=
  ⟨P.instrumentalTarget_block_probability v0 v1,
    P.instrumentalTarget_mem_affineSpan_mixture v0 v1 hlevels,
    P.instrumentalTarget_not_mem_mixture v0 v1 hW (hlevels b)⟩

end MeraConstraints.CompactDistrict.InstrumentalWitness
