import MeraConstraints.Probability.ReplayContext

/-!
# Conditional replay with a random context

Let `ρ` be a probability measure on contexts and `ν` one on candidates, and let the
stream of candidates be independent of the context (the product measure
`ρ.prod (trialMeasure ν)`). The accepted candidates at context `c` form the fiber
`acceptanceFiber E c`. Suppose that for `ρ`-almost every `c` this fiber has positive
`ν`-probability. Then almost surely some trial is accepted
(`context_replay_ae_success`), and the joint law of the context and the replayed
candidate is given by `context_replay_joint_law`: given the context `c`, the
candidate has the law `ν` conditioned on its accepted fiber, and the law of the
context is unchanged (`context_replay_context_law`). This holds equally for any
independent context and stream with these laws
(`independent_context_replay_joint_law`). No regular conditional probabilities are
used.

In the split model the context is the original input and the accepted fiber is the
set of candidates reproducing its observed boundary values.
-/

namespace MeraConstraints.Replay

open MeasureTheory ProbabilityTheory Set
open HiddenGraph.StrongFaceSplitting (firstReplay)

variable {C T : Type*} [MeasurableSpace C] [MeasurableSpace T]
  (ρ : Measure C) [IsProbabilityMeasure ρ] (ν : Measure T) [IsProbabilityMeasure ν]
  (E : Set (C × T)) (hE : MeasurableSet E)

theorem context_trial_independent :
    IndepFun (Prod.fst : C × (ℕ → T) → C) Prod.snd (ρ.prod (trialMeasure ν)) :=
  indepFun_prod (μ := ρ) (ν := trialMeasure ν) measurable_id measurable_id

include hE in
theorem fixed_context_replay_map (c : C) (hc : ν (acceptanceFiber E c) ≠ 0) :
    (trialMeasure ν).map (fun ω => contextReplay E (c, ω)) =
      ProbabilityTheory.cond ν (acceptanceFiber E c) :=
  trials_replay_map_eq_cond ν (acceptanceFiber E c) (acceptanceFiber_measurable E hE c) hc

include hE in
/-- The conditional mass of `B` in the fiber at `c` is a measurable function of
`c`. On fibers of probability zero its value is 0. -/
theorem context_conditional_mass_measurable (B : Set (C × T)) (hB : MeasurableSet B) :
    Measurable (fun c => (ν (acceptanceFiber E c))⁻¹ *
      ν (acceptanceFiber E c ∩ acceptanceFiber B c)) := by
  have hmass : Measurable (fun c => ν (acceptanceFiber E c)) :=
    measurable_measure_prodMk_left hE
  have hinter : Measurable (fun c => ν (acceptanceFiber E c ∩ acceptanceFiber B c)) := by
    simpa only [acceptanceFiber, preimage_inter] using measurable_measure_prodMk_left (hE.inter hB)
  exact hmass.inv.mul hinter

include hE in
omit [IsProbabilityMeasure ρ] in
theorem context_replay_ae_success (hpos : ∀ᵐ c ∂ρ, ν (acceptanceFiber E c) ≠ 0) :
    ∀ᵐ z ∂ρ.prod (trialMeasure ν), ∃ n, (z.1, z.2 n) ∈ E := by
  apply (Measure.ae_prod_iff_ae_ae (contextReplay_success_measurable E hE)).mpr
  filter_upwards [hpos] with c hc
  exact trials_ae_success ν (acceptanceFiber E c) (acceptanceFiber_measurable E hE c) hc

include hE in
omit [IsProbabilityMeasure ρ] in
theorem context_replay_ae_accept (hpos : ∀ᵐ c ∂ρ, ν (acceptanceFiber E c) ≠ 0) :
    ∀ᵐ z ∂ρ.prod (trialMeasure ν), contextJoint E z ∈ E := by
  filter_upwards [context_replay_ae_success ρ ν E hE hpos] with z hz
  exact contextReplay_accept E z hz

include hE in
omit [IsProbabilityMeasure ρ] in
/-- The joint law of the context and the replayed candidate. Positive probability
of the accepted fiber is needed only for almost every context. -/
theorem context_replay_joint_law (hpos : ∀ᵐ c ∂ρ, ν (acceptanceFiber E c) ≠ 0)
    (B : Set (C × T)) (hB : MeasurableSet B) :
    ((ρ.prod (trialMeasure ν)).map (contextJoint E)) B =
      ∫⁻ c, (ν (acceptanceFiber E c))⁻¹ *
        ν (acceptanceFiber E c ∩ acceptanceFiber B c) ∂ρ := by
  rw [Measure.map_apply (contextJoint_measurable E hE) hB,
    Measure.prod_apply (hB.preimage (contextJoint_measurable E hE))]
  apply lintegral_congr_ae
  filter_upwards [hpos] with c hc
  exact firstReplay_preimage_measure (trialMeasure ν) ν (fun n ω => ω n)
    (fun n => measurable_pi_apply n) (trials_independent ν) (trials_common_law ν)
    (acceptanceFiber E c) (acceptanceFiber_measurable E hE c) hc
    (acceptanceFiber B c) (acceptanceFiber_measurable B hB c)

include hE in
omit [IsProbabilityMeasure ρ] in
/-- The context coordinate of the joint law has law `ρ`. -/
theorem context_replay_context_law :
    ((ρ.prod (trialMeasure ν)).map (contextJoint E)).map Prod.fst = ρ := by
  rw [Measure.map_map measurable_fst (contextJoint_measurable E hE)]
  change (ρ.prod (trialMeasure ν)).map Prod.fst = ρ
  rw [Measure.map_fst_prod, measure_univ, one_smul]

include hE in
omit [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] in
/-- If a context `Z` and a stream `W` on any probability space are independent
with laws `ρ` and `trialMeasure ν`, their joint law after replay is the same as for
the product measure. -/
theorem independent_context_replay_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → C) (W : Ω → ℕ → T)
    (hZ : Measurable Z) (hW : Measurable W) (hZW : IndepFun Z W μ)
    (hZlaw : μ.map Z = ρ) (hWlaw : μ.map W = trialMeasure ν) :
    μ.map (fun ω => contextJoint E (Z ω, W ω)) =
      (ρ.prod (trialMeasure ν)).map (contextJoint E) := by
  have hpair : μ.map (fun ω => (Z ω, W ω)) = ρ.prod (trialMeasure ν) := by
    rw [hZW.map_prod_eq_prod_map_map hZ.aemeasurable hW.aemeasurable, hZlaw, hWlaw]
  change μ.map ((contextJoint E) ∘ (fun ω => (Z ω, W ω))) = _
  rw [← Measure.map_map (contextJoint_measurable E hE) (hZ.prodMk hW), hpair]

include hE in
omit [IsProbabilityMeasure ρ] in
/-- `context_replay_joint_law` for an independent context `Z` and stream `W` on any
probability space, with laws `ρ` and `trialMeasure ν`. -/
theorem independent_context_replay_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → C) (W : Ω → ℕ → T)
    (hZ : Measurable Z) (hW : Measurable W) (hZW : IndepFun Z W μ)
    (hZlaw : μ.map Z = ρ) (hWlaw : μ.map W = trialMeasure ν)
    (hpos : ∀ᵐ c ∂ρ, ν (acceptanceFiber E c) ≠ 0) (B : Set (C × T)) (hB : MeasurableSet B) :
    (μ.map (fun ω => contextJoint E (Z ω, W ω))) B =
      ∫⁻ c, (ν (acceptanceFiber E c))⁻¹ *
        ν (acceptanceFiber E c ∩ acceptanceFiber B c) ∂ρ := by
  rw [independent_context_replay_map ρ ν E hE μ Z W hZ hW hZW hZlaw hWlaw]
  exact context_replay_joint_law ρ ν E hE hpos B hB

end MeraConstraints.Replay
