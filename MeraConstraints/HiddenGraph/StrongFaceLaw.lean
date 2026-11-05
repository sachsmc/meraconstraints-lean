import MeraConstraints.HiddenGraph.StrongFaceAlignment
import MeraConstraints.HiddenGraph.StrongFaceIndependence
import MeraConstraints.Probability.ReplayInvariance

/-!
# The split model has the observed distribution of the original model

This is the main probability step of the direction "every original model is a split
model" in Proposition 6 (`prop:strong`). Let the original inputs have law `ν`,
mutually independent, and draw an independent stream of candidates from `ν`.

1. Let `conditionalResampledInputs` be `resampleInputs x q`, where `q` is the first
   trial accepted at `x`. Conditional resampling preserves the law of the original
   inputs: the result has law `ν` (`conditionalResampledInputs_map`). This is
   `Probability.ReplayInvariance` applied to the observed boundary values, using
   the independence of the external and local blocks from `StrongFaceInputs` and
   the identity `replayAccept_iff_boundaryFiber`. The observed values are finitely
   many, and values of probability zero cause no difficulty.
2. By `StrongFaceAlignment`, with probability one the output of the split model
   equals the original evaluation at the resampled inputs
   (`coupledReplayEval_ae`).
3. Therefore the observed distribution of the split model equals that of the
   original model (`coupledReplayEval_map`), including values of probability zero.

The split model's inputs are mutually independent (`StrongFaceIndependence`) and its
mechanisms are measurable (`StrongFaceMeasurability`). They are assembled into a
`RootProbabilityModel` in `Completeness.StrongFaceSplitting`.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K] [Fintype J]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

noncomputable def conditionalResampledInputs
    (z : ReplayCandidate A C D other M × (ℕ → ReplayCandidate A C D other M)) : ReplayCandidate A C D other M :=
  resampleInputs A C D other M z.1 (Replay.contextReplay (replayAcceptanceEvent A C D other M) z)

variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]
  [∀ i, Fintype (val i)]
  [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

include h in
omit [Fintype J] in
theorem conditionalResampledInputs_measurable (hF : RootMechanismsMeasurable A C D other M) :
    Measurable (conditionalResampledInputs A C D other M) :=
  (resampleInputs_measurable A C D other M).comp (measurable_fst.prodMk
    (Replay.contextReplay_measurable _ (replayAcceptanceEvent_measurable A C D other h M hF)))

variable (ν : Measure (ReplayCandidate A C D other M)) [IsProbabilityMeasure ν]

include h in
/-- Resampling the local block conditionally on the observed boundary values
preserves the law `ν` of the original inputs. -/
theorem conditionalResampledInputs_map (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    (ν.prod (Replay.trialMeasure ν)).map (conditionalResampledInputs A C D other M) = ν := by
  have hE := replayAcceptanceEvent_measurable A C D other h M hF
  have hr := resampleInputs_measurable A C D other M
  have hj := Replay.contextJoint_measurable (replayAcceptanceEvent A C D other M) hE
  have hcomp : conditionalResampledInputs A C D other M =
      (fun z => resampleInputs A C D other M z.1 z.2) ∘
        Replay.contextJoint (replayAcceptanceEvent A C D other M) := rfl
  rw [hcomp, ← Measure.map_map hr hj]
  ext S hS
  rw [Measure.map_apply hr hS,
    replayTrials_joint_law A C D other h M ν hF hInd _ (hS.preimage hr)]
  have hm := Replay.independent_resampling_mass ν
    (maskInputs A C D other M false) (maskInputs A C D other M true)
    (fun z => resampleInputs A C D other M z.1 z.2) (boundaryObservation A C D other M)
    (maskInputs_measurable A C D other M false) (maskInputs_measurable A C D other M true)
    hr (boundaryObservation_measurable A C D other M hF)
    (fun x => (resampleInputs_mask A C D other M x x).trans (resampleInputs_self A C D other M x))
    (replayBlocks_independent A C D other M ν hInd) S hS
  have ha (x : ReplayCandidate A C D other M) :
      {q | boundaryObservation A C D other M
        (resampleInputs A C D other M (maskInputs A C D other M false x) (maskInputs A C D other M true q)) =
          boundaryObservation A C D other M x} =
        Replay.acceptanceFiber (replayAcceptanceEvent A C D other M) x := by
    ext q
    change boundaryObservation A C D other M
      (resampleInputs A C D other M (maskInputs A C D other M false x) (maskInputs A C D other M true q)) =
        boundaryObservation A C D other M x ↔ _
    rw [resampleInputs_mask]
    exact (replayAccept_iff_boundaryFiber A C D other h M x q).symm
  have hb (x : ReplayCandidate A C D other M) :
      {q | resampleInputs A C D other M (maskInputs A C D other M false x)
        (maskInputs A C D other M true q) ∈ S} =
        Replay.acceptanceFiber ((fun z => resampleInputs A C D other M z.1 z.2) ⁻¹' S) x := by
    ext q
    change resampleInputs A C D other M (maskInputs A C D other M false x)
      (maskInputs A C D other M true q) ∈ S ↔ resampleInputs A C D other M x q ∈ S
    rw [resampleInputs_mask]
  simpa only [ha, hb] using hm

include h in
theorem coupledReplayEval_ae (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    coupledReplayEval A C D other h M =ᵐ[ν.prod (Replay.trialMeasure ν)]
      (evalCandidate A C D other M) ∘ (conditionalResampledInputs A C D other M) := by
  filter_upwards [replayTrials_ae_success A C D other h M ν hF hInd] with z hz
  exact coupledReplayEval_of_success A C D other h M z.1 z.2 hz

include h in
/-- The split model on original inputs and an independent stream has the same
observed distribution as the original model. -/
theorem coupledReplayEval_map (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    (ν.prod (Replay.trialMeasure ν)).map (coupledReplayEval A C D other h M) =
      ν.map (evalCandidate A C D other M) := by
  rw [Measure.map_congr (coupledReplayEval_ae A C D other h M ν hF hInd),
    ← Measure.map_map (evalCandidate_measurable A C D other M hF)
      (conditionalResampledInputs_measurable A C D other h M hF),
    conditionalResampledInputs_map A C D other h M ν hF hInd]

end MeraConstraints.HiddenGraph.StrongFaceSplitting
