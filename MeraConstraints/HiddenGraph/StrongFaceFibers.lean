import MeraConstraints.HiddenGraph.StrongFaceReverse
import Mathlib.Data.Finset.Max

/-!
# The acceptance test is a fiber of the observed boundary

This chapter belongs to the direction "every original model is a split model" of
Proposition 6 (`prop:strong`). Write `C` for the union of the sets `C_i`, which may
overlap. The boundary (`replayBoundary`) is `C` together with the observed parents
of `C`, so paths may leave `C` and re-enter it. By the proposition's first numbered condition, every boundary vertex
precedes every vertex of `D` (`replayBoundary_lt_D`).

For original inputs `x` and a candidate `q`, `resampleInputs x q` replaces in `x` the
selected variables, the unselected variables with all children in `C`, and the
private noise at `C` by their values in `q`. Before the first vertex of `D`, this can
change a mechanism only at `C`. So if `q` passes the equations at `C`, the
resampled evaluation agrees with the original on the whole boundary, by induction
along the DAG. Conversely, agreement on the boundary gives the equations at `C`.
The result is `replayAccept_iff_boundaryFiber`: `q` is accepted at `x` exactly when
resampling does not change the observed values on the boundary. Accepted candidates
are therefore the candidates compatible with the observed boundary of `x`, which
is the conditioning event of the probability argument. These results involve no
probability.
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

/-- If `q` passes the global test at `x`, resampling with `q` leaves the observed
values at all vertices before `d` unchanged, where `d` is at most every vertex of
`D`. -/
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
/-- A candidate `q` passes the global test at `x` exactly when resampling `x` with
`q` leaves the observed values on the boundary unchanged. -/
theorem replayAccept_iff_boundaryFiber (x q : ReplayCandidate A C D other M) :
    globalReplayAccept A C D other M (evalCandidate A C D other M x)
        (encodeOriginalInputs A C D other M x.1 x.2) q ↔
      boundaryObservation A C D other M (resampleInputs A C D other M x q) =
        boundaryObservation A C D other M x :=
  ⟨boundaryObservation_eq_of_accept A C D other h M x q,
    accept_of_boundaryObservation_eq A C D other M x q⟩

include h in
/-- The local test at any vertex of `D` is the same condition. -/
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
