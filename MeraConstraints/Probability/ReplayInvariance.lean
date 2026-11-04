import MeraConstraints.Probability.ReplaySupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Conditional local resampling preserves the original law

For a finite-valued observation, averaging its fiberwise conditional laws
recovers the original measure, including zero-mass fibers. Apply this at each
fixed external input, then integrate over the independent external/local
product law. Conditional replay consequently preserves the reconstructed
input law. The observation is finite; both input spaces remain arbitrary
measurable spaces. No strictly positive observed distribution is required.
-/

namespace MeraConstraints.Replay

open MeasureTheory ProbabilityTheory Set

theorem finite_fiber_average {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (ν : Measure T) [IsFiniteMeasure ν]
    (f : T → B) (hf : Measurable f) (S : Set T) (hS : MeasurableSet S) :
    (∫⁻ x, (ν (f ⁻¹' {f x}))⁻¹ * ν ((f ⁻¹' {f x}) ∩ S) ∂ν) = ν S := by
  let H := fun b : B => (ν (f ⁻¹' {b}))⁻¹ * ν ((f ⁻¹' {b}) ∩ S)
  change (∫⁻ x, H (f x) ∂ν) = ν S
  rw [← lintegral_map (measurable_of_countable H) hf, lintegral_fintype]
  simp_rw [Measure.map_apply hf (measurableSet_singleton _)]
  have ht := congrArg (fun μ : Measure T => μ S) (sum_meas_smul_cond_fiber hf ν)
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, cond_apply' hS] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

theorem independent_resampling_mass {T E L B : Type*}
    [MeasurableSpace T] [MeasurableSpace E] [MeasurableSpace L] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (external : T → E) (localInput : T → L) (restore : E × L → T)
    (obs : T → B) (he : Measurable external) (hl : Measurable localInput)
    (hr : Measurable restore) (ho : Measurable obs)
    (hinv : ∀ x, restore (external x, localInput x) = x)
    (hind : IndepFun external localInput ν) (S : Set T) (hS : MeasurableSet S) :
    (∫⁻ x, (ν {q | obs (restore (external x, localInput q)) = obs x})⁻¹ *
      ν ({q | obs (restore (external x, localInput q)) = obs x} ∩
        {q | restore (external x, localInput q) ∈ S}) ∂ν) = ν S := by
  let ρ := ν.map external
  let η := ν.map localInput
  letI : IsProbabilityMeasure ρ := ν.isProbabilityMeasure_map he.aemeasurable
  letI : IsProbabilityMeasure η := ν.isProbabilityMeasure_map hl.aemeasurable
  let P : Set ((E × L) × L) := {z | obs (restore (z.1.1, z.2)) = obs (restore z.1)}
  let Q : Set ((E × L) × L) := {z | restore (z.1.1, z.2) ∈ S}
  have hP : MeasurableSet P := measurableSet_observation_eq
    (ho.comp (hr.comp (measurable_fst.fst.prodMk measurable_snd)))
    (ho.comp (hr.comp measurable_fst))
  have hQ : MeasurableSet Q := hS.preimage (hr.comp (measurable_fst.fst.prodMk measurable_snd))
  let H := fun z : E × L => (η (acceptanceFiber P z))⁻¹ * η (acceptanceFiber P z ∩ acceptanceFiber Q z)
  have hH : Measurable H := context_conditional_mass_measurable η P hP Q hQ
  have hk (x : T) : H (external x, localInput x) =
      (ν {q | obs (restore (external x, localInput q)) = obs x})⁻¹ *
        ν ({q | obs (restore (external x, localInput q)) = obs x} ∩
          {q | restore (external x, localInput q) ∈ S}) := by
    change ((ν.map localInput) (acceptanceFiber P (external x, localInput x)))⁻¹ *
      (ν.map localInput) (acceptanceFiber P (external x, localInput x) ∩
        acceptanceFiber Q (external x, localInput x)) = _
    rw [Measure.map_apply hl (acceptanceFiber_measurable P hP _),
      Measure.map_apply hl ((acceptanceFiber_measurable P hP _).inter (acceptanceFiber_measurable Q hQ _))]
    simp only [acceptanceFiber, P, Q, Set.preimage_setOf_eq, Set.preimage_inter, hinv]
  have hrestore : (ρ.prod η).map restore = ν := by
    change ((ν.map external).prod (ν.map localInput)).map restore = ν
    rw [← hind.map_prod_eq_prod_map_map he.aemeasurable hl.aemeasurable,
      Measure.map_map hr (he.prodMk hl)]
    have hid : restore ∘ (fun x => (external x, localInput x)) = id := funext hinv
    rw [hid, Measure.map_id]
  calc
    _ = ∫⁻ x, H (external x, localInput x) ∂ν := lintegral_congr fun x => (hk x).symm
    _ = ∫⁻ z, H z ∂ρ.prod η := by
      rw [← lintegral_map hH (he.prodMk hl), hind.map_prod_eq_prod_map_map he.aemeasurable hl.aemeasurable]
    _ = ∫⁻ e, ∫⁻ l, H (e, l) ∂η ∂ρ := lintegral_prod _ hH.aemeasurable
    _ = ∫⁻ e, η {l | restore (e, l) ∈ S} ∂ρ := by
      apply lintegral_congr
      intro e
      exact finite_fiber_average η (fun l => obs (restore (e, l)))
        (ho.comp (hr.comp (measurable_const.prodMk measurable_id)))
        {l | restore (e, l) ∈ S} (hS.preimage (hr.comp (measurable_const.prodMk measurable_id)))
    _ = (ρ.prod η) (restore ⁻¹' S) := (Measure.prod_apply (hS.preimage hr)).symm
    _ = ν S := by rw [← Measure.map_apply hr hS, hrestore]

end MeraConstraints.Replay
