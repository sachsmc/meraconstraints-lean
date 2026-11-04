import MeraConstraints.HiddenGraph.StrongFaceReverse
import Mathlib.Data.Finset.Max

/-!
# Strong splitting acceptance is an observed-boundary fiber

This chapter addresses the reverse direction of manuscript `prop:strong`
(Strong Face Splitting). Write C for the union of its possibly overlapping
sets C_i. No disjointness between those sets or ancestry closure of C is
assumed. The boundary includes parents outside C, so paths that leave C
and later re-enter it are allowed.

The boundary is the union of C and its observed parents. Condition 1 puts
every boundary vertex before every D vertex. Below the least D vertex,
resampling can affect a mechanism only at C: selected roots have no other
children there, internal-C roots have no children outside C, and other inputs
are retained. If the candidate satisfies the C equations, induction therefore
preserves the whole boundary. Conversely, equality on the boundary verifies
each original C equation for the resampled evaluation.

Thus the actual replay checker is exactly an observed-boundary fiber, not
an unrelated positive-probability event. This structural identity needs no
probability or finite-state assumption; finite observed states are used by
the subsequent supported-fiber argument.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

def replayBoundary : Finset (Fin n) := unionC C ∪ (unionC C).biUnion A.parents

include h in
theorem replayBoundary_lt_D {i d : Fin n} (hi : i ∈ replayBoundary A C) (hd : d ∈ D) : i < d := by
  rcases Finset.mem_union.mp hi with hc | hp
  · exact A.parents_lt (unionC_parent A C D other h hd hc)
  · obtain ⟨c, hc, hic⟩ := Finset.mem_biUnion.mp hp
    exact A.parents_lt (unionC_parent_parent A C D other h hd hc hic)

def evalCandidate (x : ReplayCandidate A C D other M) : FullAssign val := M.eval x.1 x.2

noncomputable def resampleInputs (x q : ReplayCandidate A C D other M) : ReplayCandidate A C D other M :=
  (replayRoots A C D other M (encodeOriginalInputs A C D other M x.1 x.2) q,
    replayPrivate A C D other M q x.2)

abbrev BoundaryAssign := ∀ i : {i : Fin n // i ∈ replayBoundary A C}, val i.val

def boundaryObservation (x : ReplayCandidate A C D other M) : BoundaryAssign A C (val := val) :=
  fun i => evalCandidate A C D other M x i.val

/-- Prefix preservation stops before the least D vertex; no unchanged-value
claim is made for an earlier D vertex in a larger arbitrary prefix. -/
theorem eval_resample_prefix (x q : ReplayCandidate A C D other M)
    (d : Fin n) (hmin : ∀ e ∈ D, d ≤ e)
    (ha : globalReplayAccept A C D other M (evalCandidate A C D other M x)
      (encodeOriginalInputs A C D other M x.1 x.2) q)
    (i : Fin n) (hi : i < d) :
    evalCandidate A C D other M (resampleInputs A C D other M x q) i =
      evalCandidate A C D other M x i := by
  classical
  have hp : PaAssign.restrict (G := (originalGraph A C D other).observed)
      (evalCandidate A C D other M (resampleInputs A C D other M x q)) i =
      PaAssign.restrict (G := (originalGraph A C D other).observed)
        (evalCandidate A C D other M x) i := by
    funext j
    exact eval_resample_prefix x q d hmin ha j (lt_trans (A.parents_lt j.property) hi)
  change M.eval _ _ i = _
  rw [M.eval_eq]
  change M.F i (PaAssign.restrict (G := (originalGraph A C D other).observed)
      (evalCandidate A C D other M (resampleInputs A C D other M x q)) i)
    (fun r => replayRoots A C D other M (encodeOriginalInputs A C D other M x.1 x.2) q r.val)
    (replayPrivate A C D other M q x.2 i) = evalCandidate A C D other M x i
  rw [hp]
  by_cases hc : i ∈ unionC C
  · simpa only [replayPrivate, if_pos hc] using ha i hc
  · have hiD : i ∉ D := fun hid => (not_le_of_gt hi) (hmin i hid)
    have hr : (fun r : {r // i ∈ (originalGraph A C D other).children r} =>
        replayRoots A C D other M (encodeOriginalInputs A C D other M x.1 x.2) q r.val) =
        (fun r : {r // i ∈ (originalGraph A C D other).children r} => x.1 r.val) :=
      (outsideRootInputs_global A C D other M i hc hiD
        (encodeOriginalInputs A C D other M x.1 x.2) q).symm.trans
          (outsideRootInputs_encoded A C D other M i hiD x.1 x.2)
    rw [hr]
    simpa only [replayPrivate, if_neg hc, evalCandidate] using (M.eval_eq x.1 x.2 i).symm
termination_by i.val
decreasing_by exact A.parents_lt j.property

include h in
theorem boundaryObservation_eq_of_accept (x q : ReplayCandidate A C D other M)
    (ha : globalReplayAccept A C D other M (evalCandidate A C D other M x)
      (encodeOriginalInputs A C D other M x.1 x.2) q) :
    boundaryObservation A C D other M (resampleInputs A C D other M x q) =
      boundaryObservation A C D other M x := by
  let d := D.min' h.common_nonempty
  have hd : d ∈ D := Finset.min'_mem D h.common_nonempty
  have hmin : ∀ e ∈ D, d ≤ e := fun e he => Finset.min'_le D e he
  funext i
  exact eval_resample_prefix A C D other M x q d hmin ha i.val
    (replayBoundary_lt_D A C D other h i.property hd)

theorem accept_of_boundaryObservation_eq (x q : ReplayCandidate A C D other M)
    (hb : boundaryObservation A C D other M (resampleInputs A C D other M x q) =
      boundaryObservation A C D other M x) :
    globalReplayAccept A C D other M (evalCandidate A C D other M x)
      (encodeOriginalInputs A C D other M x.1 x.2) q := by
  intro c hc
  have hp : PaAssign.restrict (G := (originalGraph A C D other).observed)
      (evalCandidate A C D other M (resampleInputs A C D other M x q)) c =
      PaAssign.restrict (G := (originalGraph A C D other).observed)
        (evalCandidate A C D other M x) c := by
    funext j
    exact congrFun hb ⟨j, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hc, j.property⟩)⟩
  have hv := congrFun hb ⟨c, Finset.mem_union_left _ hc⟩
  have he := (M.eval_eq (resampleInputs A C D other M x q).1
    (resampleInputs A C D other M x q).2 c).symm
  change M.F c (PaAssign.restrict (G := (originalGraph A C D other).observed)
      (evalCandidate A C D other M (resampleInputs A C D other M x q)) c)
    (fun r => replayRoots A C D other M (encodeOriginalInputs A C D other M x.1 x.2) q r.val)
    (replayPrivate A C D other M q x.2 c) =
      evalCandidate A C D other M (resampleInputs A C D other M x q) c at he
  rw [hp] at he
  simpa only [replayPrivate, if_pos hc, boundaryObservation] using he.trans hv

include h in
/-- The graph-specific acceptance event is exactly its observed-boundary fiber. -/
theorem replayAccept_iff_boundaryFiber (x q : ReplayCandidate A C D other M) :
    globalReplayAccept A C D other M (evalCandidate A C D other M x)
        (encodeOriginalInputs A C D other M x.1 x.2) q ↔
      boundaryObservation A C D other M (resampleInputs A C D other M x q) =
        boundaryObservation A C D other M x :=
  ⟨boundaryObservation_eq_of_accept A C D other h M x q,
    accept_of_boundaryObservation_eq A C D other M x q⟩

include h in
/-- Each D mechanism's permitted-parent check tests this same boundary fiber. -/
theorem localReplayAccept_iff_boundaryFiber (d : Fin n) (hd : d ∈ D)
    (x q : ReplayCandidate A C D other M) :
    localReplayAccept A C D other h M d hd
        (PaAssign.restrict (G := (originalGraph A C D other).observed)
          (evalCandidate A C D other M x) d)
        (fun r => encodeOriginalInputs A C D other M x.1 x.2 r.val) q ↔
      boundaryObservation A C D other M (resampleInputs A C D other M x q) =
        boundaryObservation A C D other M x :=
  (localReplayAccept_iff_global A C D other h M d hd
    (evalCandidate A C D other M x)
    (encodeOriginalInputs A C D other M x.1 x.2) q).trans
      (replayAccept_iff_boundaryFiber A C D other h M x q)

end MeraConstraints.HiddenGraph.StrongFaceSplitting
