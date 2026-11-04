import MeraConstraints.HiddenGraph.StrongFaceCoupling

/-!
# The split and original replay contexts agree

Before the first D vertex the split mechanisms retain exactly the original
inputs, regardless of the common trial stream. Condition 1 places C and its
observed parents in this prefix. Thus the actual split evaluation and original
evaluation give the same acceptance context. No acceptance or probability
premise is needed for that alignment. On a successful stream, the general
structural replay theorem then identifies the actual split output with the
original evaluation after the already checked conditional resampling.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

omit [Fintype K] in
theorem outsideRootInputs_stream (i : Fin n) (hi : i ∉ D)
    (x : ReplayCandidate A C D other M) (trials : ℕ → ReplayCandidate A C D other M) :
    outsideRootInputs A C D other M i hi
      (fun r => encodeReplayStream A C D other M x trials r.val) =
      (fun r : {r // i ∈ (originalGraph A C D other).children r} => x.1 r.val) := by
  funext r
  rcases r with ⟨k | j, hr⟩ <;> rfl

theorem replayRoots_stream (x q : ReplayCandidate A C D other M)
    (trials : ℕ → ReplayCandidate A C D other M) :
    replayRoots A C D other M (encodeReplayStream A C D other M x trials) q =
      replayRoots A C D other M (encodeOriginalInputs A C D other M x.1 x.2) q := rfl

include h in
theorem coupledReplayEval_prefix (x : ReplayCandidate A C D other M)
    (trials : ℕ → ReplayCandidate A C D other M) (d : Fin n)
    (hmin : ∀ e ∈ D, d ≤ e) (i : Fin n) (hi : i < d) :
    coupledReplayEval A C D other h M (x, trials) i = evalCandidate A C D other M x i := by
  classical
  have hp : PaAssign.restrict (G := A) (coupledReplayEval A C D other h M (x, trials)) i =
      PaAssign.restrict (G := A) (evalCandidate A C D other M x) i := by
    funext j
    exact coupledReplayEval_prefix x trials d hmin j.val (lt_trans (A.parents_lt j.property) hi)
  have hiD : i ∉ D := fun hid => (not_le_of_gt hi) (hmin i hid)
  have he := (replayModel A C D other h M).eval_eq
    (encodeReplayStream A C D other M x trials) x.2 i
  simp only [replayModel, dif_neg hiD] at he
  change coupledReplayEval A C D other h M (x, trials) i = M.F i
    (PaAssign.restrict (G := A) (coupledReplayEval A C D other h M (x, trials)) i)
    (outsideRootInputs A C D other M i hiD
      (fun r => encodeReplayStream A C D other M x trials r.val)) (x.2 i) at he
  rw [hp, outsideRootInputs_stream] at he
  exact he.trans (M.eval_eq x.1 x.2 i).symm
termination_by i.val
decreasing_by exact A.parents_lt j.property

include h in
theorem coupledReplayEval_boundary (x : ReplayCandidate A C D other M)
    (trials : ℕ → ReplayCandidate A C D other M) (i : Fin n) (hi : i ∈ replayBoundary A C) :
    coupledReplayEval A C D other h M (x, trials) i = evalCandidate A C D other M x i := by
  let d := D.min' h.common_nonempty
  exact coupledReplayEval_prefix A C D other h M x trials d
    (fun e he => Finset.min'_le D e he) i
    (replayBoundary_lt_D A C D other h hi (Finset.min'_mem D h.common_nonempty))

include h in
theorem coupledReplayAccept_iff (x q : ReplayCandidate A C D other M)
    (trials : ℕ → ReplayCandidate A C D other M) :
    globalReplayAccept A C D other M (coupledReplayEval A C D other h M (x, trials))
      (encodeReplayStream A C D other M x trials) q ↔
    globalReplayAccept A C D other M (evalCandidate A C D other M x)
      (encodeOriginalInputs A C D other M x.1 x.2) q := by
  have hc (c : Fin n) (hcc : c ∈ unionC C) :=
    coupledReplayEval_boundary A C D other h M x trials c (Finset.mem_union_left _ hcc)
  have hp (c : Fin n) (hcc : c ∈ unionC C) :
      PaAssign.restrict (G := A) (coupledReplayEval A C D other h M (x, trials)) c =
        PaAssign.restrict (G := A) (evalCandidate A C D other M x) c := by
    funext j
    exact coupledReplayEval_boundary A C D other h M x trials j.val
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcc, j.property⟩))
  unfold globalReplayAccept
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hcc
  rw [show PaAssign.restrict (G := (originalGraph A C D other).observed)
      (coupledReplayEval A C D other h M (x, trials)) c =
      PaAssign.restrict (G := (originalGraph A C D other).observed)
        (evalCandidate A C D other M x) c from hp c hcc,
    hc c hcc, replayRoots_stream]

include h in
theorem coupledReplayEval_of_success (x : ReplayCandidate A C D other M)
    (trials : ℕ → ReplayCandidate A C D other M)
    (ht : ∃ t, (x, trials t) ∈ replayAcceptanceEvent A C D other M) :
    coupledReplayEval A C D other h M (x, trials) =
      evalCandidate A C D other M (resampleInputs A C D other M x
        (Replay.contextReplay (replayAcceptanceEvent A C D other M) (x, trials))) := by
  have hs : ∃ t, globalReplayAccept A C D other M
      (coupledReplayEval A C D other h M (x, trials)) (encodeReplayStream A C D other M x trials)
        (trials t) := by
    obtain ⟨t, ht⟩ := ht
    exact ⟨t, (coupledReplayAccept_iff A C D other h M x (trials t) trials).mpr ht⟩
  have hq := firstReplay_congr trials _ _ (fun q => coupledReplayAccept_iff A C D other h M x q trials)
  have he := replayModel_eval_of_consistent A C D other h M
    (encodeReplayStream A C D other M x trials) x.2 hs
  change coupledReplayEval A C D other h M (x, trials) = M.eval
    (replayRoots A C D other M (encodeReplayStream A C D other M x trials)
      (firstReplay trials (globalReplayAccept A C D other M
        (coupledReplayEval A C D other h M (x, trials)) (encodeReplayStream A C D other M x trials))))
    (replayPrivate A C D other M
      (firstReplay trials (globalReplayAccept A C D other M
        (coupledReplayEval A C D other h M (x, trials)) (encodeReplayStream A C D other M x trials))) x.2) at he
  rw [hq, replayRoots_stream] at he
  exact he

end MeraConstraints.HiddenGraph.StrongFaceSplitting
