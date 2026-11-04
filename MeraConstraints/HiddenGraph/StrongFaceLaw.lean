import MeraConstraints.HiddenGraph.StrongFaceAlignment
import MeraConstraints.HiddenGraph.StrongFaceIndependence
import MeraConstraints.Probability.ReplayInvariance

/-!
# The concrete split model preserves the observed law

First show that conditional resampling preserves the entire native original
input law: at each fixed external block, averaging over the finite observed
boundary recovers the local input law. The product law of external/local
blocks is derived from original mutual independence. Null boundary fibers
are included by the finite law of total probability.

Boundary alignment then identifies the actual split evaluation with original
evaluation at these resampled inputs almost surely. Consequently their full
observed joint distributions agree, including zero-probability observations.
The complete encoded split input family is mutually independent by
`StrongFaceIndependence`, and split mechanisms are measurable by
`StrongFaceMeasurability`. This chapter proves the concrete reverse transport;
a bundled A1 probability-model equivalence remains to be assembled separately.
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
/-- Conditional replay preserves the entire reconstructed original input law,
not only a chosen observed event. Positivity is derived, not assumed. -/
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
/-- Equality of the full observed distributions for the actual split
evaluation with independent encoded inputs, including boundary laws. -/
theorem coupledReplayEval_map (hF : RootMechanismsMeasurable A C D other M)
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    (ν.prod (Replay.trialMeasure ν)).map (coupledReplayEval A C D other h M) =
      ν.map (evalCandidate A C D other M) := by
  rw [Measure.map_congr (coupledReplayEval_ae A C D other h M ν hF hInd),
    ← Measure.map_map (evalCandidate_measurable A C D other M hF)
      (conditionalResampledInputs_measurable A C D other h M hF),
    conditionalResampledInputs_map A C D other h M ν hF hInd]

end MeraConstraints.HiddenGraph.StrongFaceSplitting
