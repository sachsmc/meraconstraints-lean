import MeraConstraints.CompactDistrict.InstrumentalAffine
import MeraConstraints.Polytope.ZeroOne

/-!
# The lifted instrumental target is outside the district polytope

Choose two external assignments differing only in W, at its chosen zero and
one levels. In the target, A stays zero, B changes, intermediate path members
copy W, and all remaining members stay zero. The checked excluded-parent
argument forbids one profile producing both output blocks.

A zero/one point of the compatibility mixture polytope would be an actual
column, so that same profile would produce both blocks. This contradiction
completes the instrumental target's block-probability/affine-hull/nonmembership
witness in the appendix. The final nontrivial H-row conclusion is separate.
-/

namespace MeraConstraints.CompactDistrict.InstrumentalWitness

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}
  {w : ExternalParent G block d} {a b : Member block d}
  (P : InstrumentalWitness G block d w a b) (v0 v1 : FullAssign val)

omit [DecidableEq D] in
/-- Changing the copied bit changes no other member except B and the
intermediate path vertices. In particular A stays at its zero level. -/
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

/-- A single deterministic profile cannot produce the complete target at
all external inputs. Only distinct levels at W and B are needed here. -/
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
/-- A compatibility column equal to the zero/one target would have to
produce its prescribed complete output at each external input. -/
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
