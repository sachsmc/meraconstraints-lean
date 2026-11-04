import MeraConstraints.HiddenGraph.StrongFaceInputs
import MeraConstraints.Probability.ReplaySupport

/-!
# Strong splitting has supported measurable acceptance fibers

This is the probability-support step for manuscript `prop:strong`. The original
mechanisms are measurable functions of their permitted observed parents, root
inputs and private input. Evaluation is measurable by induction along the
original DAG. Thus the boundary observation and the actual joint acceptance
event are measurable.

The previous chapter derives independence of the external and local input
blocks from full mutual independence. Independent resampling and the exact
boundary-fiber identity then prove positive acceptance probability for almost
every original input. Countable observed state spaces suffice; in particular
the manuscript's finite state spaces qualify. Exogenous state spaces remain
arbitrary measurable spaces, and no positivity of the observed law is assumed.

Finally the explicit independent stream succeeds and accepts almost surely.
These results concern the original-context/replay coupling. They do not yet
assert the full split model's output law or probability-model equivalence.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)
  [∀ i, MeasurableSpace (val i)]
  [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

/-- Ordinary joint measurability of each original local mechanism, with
exactly its graph-permitted observed and root arguments. -/
def RootMechanismsMeasurable : Prop := ∀ i : Fin n,
  Measurable (fun z : PaAssign A val i ×
      ((∀ r : {r // i ∈ (originalGraph A C D other).children r}, M.rootValue r.val) × M.privateNoise i) =>
    M.F i z.1 z.2.1 z.2.2)

omit [Fintype K] in
theorem evalCandidate_apply_measurable (hF : RootMechanismsMeasurable A C D other M)
    (i : Fin n) : Measurable (fun x => evalCandidate A C D other M x i) := by
  have hp : Measurable (fun x => PaAssign.restrict (G := A)
      (evalCandidate A C D other M x) i) := by
    apply measurable_pi_iff.mpr
    intro j
    exact evalCandidate_apply_measurable hF j.val
  have hr : Measurable (fun x : ReplayCandidate A C D other M =>
      fun r : {r // i ∈ (originalGraph A C D other).children r} => x.1 r.val) :=
    measurable_pi_iff.mpr fun r => (measurable_pi_apply r.val).comp measurable_fst
  have hm := (hF i).comp (hp.prodMk (hr.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have heq : (fun x => evalCandidate A C D other M x i) =
      (fun x : ReplayCandidate A C D other M => M.F i
        (PaAssign.restrict (G := A) (evalCandidate A C D other M x) i)
        (fun r => x.1 r.val) (x.2 i)) := funext fun x => M.eval_eq x.1 x.2 i
  rw [heq]
  exact hm
termination_by i.val
decreasing_by exact A.parents_lt j.property

omit [Fintype K] in
theorem evalCandidate_measurable (hF : RootMechanismsMeasurable A C D other M) :
    Measurable (evalCandidate A C D other M) :=
  measurable_pi_iff.mpr (evalCandidate_apply_measurable A C D other M hF)

theorem boundaryObservation_measurable (hF : RootMechanismsMeasurable A C D other M) :
    Measurable (boundaryObservation A C D other M) :=
  measurable_pi_iff.mpr fun i => evalCandidate_apply_measurable A C D other M hF i.val

def replayAcceptanceEvent : Set (ReplayCandidate A C D other M × ReplayCandidate A C D other M) :=
  {z | globalReplayAccept A C D other M (evalCandidate A C D other M z.1)
    (encodeOriginalInputs A C D other M z.1.1 z.1.2) z.2}

variable [∀ i, MeasurableSingletonClass (val i)] [∀ i, Countable (val i)]

include h in
theorem replayAcceptanceEvent_measurable (hF : RootMechanismsMeasurable A C D other M) :
    MeasurableSet (replayAcceptanceEvent A C D other M) := by
  have heq : replayAcceptanceEvent A C D other M =
      {z | boundaryObservation A C D other M (resampleInputs A C D other M z.1 z.2) =
        boundaryObservation A C D other M z.1} := by
    ext z
    exact replayAccept_iff_boundaryFiber A C D other h M z.1 z.2
  rw [heq]
  exact Replay.measurableSet_observation_eq
    ((boundaryObservation_measurable A C D other M hF).comp (resampleInputs_measurable A C D other M))
    ((boundaryObservation_measurable A C D other M hF).comp measurable_fst)

variable [Fintype J] (ν : Measure (ReplayCandidate A C D other M)) [IsProbabilityMeasure ν]

include h in
/-- Acceptance-fiber positivity is derived from the original independent
inputs; it is neither an observed-law positivity assumption nor a premise
about the selected replay candidate. -/
theorem replayAcceptance_ae_positive (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    ∀ᵐ x ∂ν, ν {q | globalReplayAccept A C D other M (evalCandidate A C D other M x)
      (encodeOriginalInputs A C D other M x.1 x.2) q} ≠ 0 := by
  have hp := Replay.independent_resampling_ae_positive ν
    (maskInputs A C D other M false) (maskInputs A C D other M true)
    (fun z => resampleInputs A C D other M z.1 z.2) (boundaryObservation A C D other M)
    (maskInputs_measurable A C D other M false) (maskInputs_measurable A C D other M true)
    (resampleInputs_measurable A C D other M) (boundaryObservation_measurable A C D other M hF)
    (fun x => (resampleInputs_mask A C D other M x x).trans (resampleInputs_self A C D other M x))
    (replayBlocks_independent A C D other M ν hInd)
  filter_upwards [hp] with x hx
  simpa only [resampleInputs_mask, ← replayAccept_iff_boundaryFiber A C D other h M x] using hx

include h in
/-- Independent original-law trials hit the graph's actual acceptance fiber
almost surely under the original-context × stream product law. -/
theorem replayTrials_ae_success (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    ∀ᵐ z ∂ν.prod (Replay.trialMeasure ν), ∃ t,
      (z.1, z.2 t) ∈ replayAcceptanceEvent A C D other M :=
  Replay.context_replay_ae_success ν ν (replayAcceptanceEvent A C D other M)
    (replayAcceptanceEvent_measurable A C D other h M hF)
    (replayAcceptance_ae_positive A C D other h M ν hF hInd)

include h in
theorem replayTrials_ae_accept (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    ∀ᵐ z ∂ν.prod (Replay.trialMeasure ν),
      Replay.contextJoint (replayAcceptanceEvent A C D other M) z ∈
        replayAcceptanceEvent A C D other M :=
  Replay.context_replay_ae_accept ν ν (replayAcceptanceEvent A C D other M)
    (replayAcceptanceEvent_measurable A C D other h M hF)
    (replayAcceptance_ae_positive A C D other h M ν hF hInd)

include h in
/-- The graph-specific context/selected-candidate joint law, with its
acceptance measurability and supported-fiber premises now discharged. -/
theorem replayTrials_joint_law (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν)
    (B : Set (ReplayCandidate A C D other M × ReplayCandidate A C D other M))
    (hB : MeasurableSet B) :
    ((ν.prod (Replay.trialMeasure ν)).map
      (Replay.contextJoint (replayAcceptanceEvent A C D other M))) B =
      ∫⁻ x, (ν (Replay.acceptanceFiber (replayAcceptanceEvent A C D other M) x))⁻¹ *
        ν (Replay.acceptanceFiber (replayAcceptanceEvent A C D other M) x ∩
          Replay.acceptanceFiber B x) ∂ν :=
  Replay.context_replay_joint_law ν ν (replayAcceptanceEvent A C D other M)
    (replayAcceptanceEvent_measurable A C D other h M hF)
    (replayAcceptance_ae_positive A C D other h M ν hF hInd) B hB

end MeraConstraints.HiddenGraph.StrongFaceSplitting
