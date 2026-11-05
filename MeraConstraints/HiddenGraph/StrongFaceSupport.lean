import MeraConstraints.HiddenGraph.StrongFaceInputs
import MeraConstraints.Probability.ReplaySupport

/-!
# Conditional replay succeeds almost surely

Take an original model whose mechanisms are measurable (`RootMechanismsMeasurable`).
Its evaluation is then measurable, by induction along the DAG, and so are the
observed boundary values and the acceptance event `replayAcceptanceEvent`: the set
of pairs (original inputs `x`, candidate `q`) such that `q` passes the global test
at `x`.

By `StrongFaceInputs`, the external and local blocks of the original inputs are
independent. By `Probability.ReplaySupport` and the identity
`replayAccept_iff_boundaryFiber`, for almost every `x` the set of candidates
accepted at `x` has positive probability (`replayAcceptance_ae_positive`). The
observed values may be countable in number, in particular finite as in the
manuscript. The observed distribution need not be positive. The unobserved and
private input spaces are arbitrary measurable spaces. With `x` as the context and
an independent stream of draws from the law of the original inputs,
`Probability.ReplayContextLaw` gives that some trial is accepted almost surely
(`replayTrials_ae_success`), and the joint law of `x` and the first accepted
trial (`replayTrials_joint_law`). The law of the split model's output is
treated in `StrongFaceLaw`.
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

/-- Each mechanism of the original model `M` is jointly measurable in its observed
parents, its unobserved parents and its private noise. -/
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
/-- For almost every original input `x`, the set of candidates accepted at `x` has
positive probability under `ν`, the law of the original inputs. -/
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
/-- Under the product of `ν` and the law of an independent stream of draws from `ν`,
almost surely some trial is accepted at the original input. -/
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
/-- The joint law of the original input and the first accepted trial, as in
`Replay.context_replay_joint_law`. -/
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
