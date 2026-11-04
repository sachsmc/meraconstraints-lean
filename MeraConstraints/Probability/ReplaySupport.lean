import MeraConstraints.Probability.ReplayContextLaw
import Mathlib.Probability.Independence.Basic

/-!
# Supported fibers for independent resampling

A countable-valued observation lies in a positive-mass fiber almost surely.
With independent external and local inputs, apply that fact separately at
each fixed external input and integrate. Replacing the local input by a fresh
draw therefore has positive probability of preserving the original observation
almost surely. Null unsupported observations are allowed.

The reconstruction map and its inverse identity identify the actual original
input law; independence is an input property, not a premise about the desired
replayed output. No conditional distributions or standard-Borel assumptions
on the input spaces are used.
-/

namespace MeraConstraints.Replay

open MeasureTheory ProbabilityTheory Set

theorem ae_positive_observation_fiber {T B : Type*} [MeasurableSpace T]
    [Countable B] (ν : Measure T) (f : T → B) :
    ∀ᵐ x ∂ν, ν {q | f q = f x} ≠ 0 := by
  have hall : ∀ b : B, ∀ᵐ x ∂ν, f x = b → ν {q | f q = b} ≠ 0 := by
    intro b
    by_cases hb : ν {q | f q = b} = 0
    · have hn : ∀ᵐ x ∂ν, x ∉ {q | f q = b} := by
        simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hb
      filter_upwards [hn] with x hx
      exact fun h => False.elim (hx h)
    · exact Filter.Eventually.of_forall fun _ _ => hb
  filter_upwards [ae_all_iff.mpr hall] with x hx
  exact hx (f x) rfl

theorem measurableSet_observation_eq {T B : Type*} [MeasurableSpace T]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    {f g : T → B} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x = g x} := by
  have heq : {x | f x = g x} = ⋃ b : B, (f ⁻¹' {b}) ∩ (g ⁻¹' {b}) := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨g x, h, rfl⟩, fun ⟨_, hf, hg⟩ => hf.trans hg.symm⟩
  rw [heq]
  exact MeasurableSet.iUnion fun b => (hf (measurableSet_singleton b)).inter
    (hg (measurableSet_singleton b))

theorem prod_ae_positive_observation_fiber {E L B : Type*}
    [MeasurableSpace E] [MeasurableSpace L] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B]
    (ρ : Measure E) (ν : Measure L) [SFinite ν]
    (f : E × L → B) (hf : Measurable f) :
    ∀ᵐ z ∂ρ.prod ν, ν {q | f (z.1, q) = f z} ≠ 0 := by
  have hm : Measurable (fun z : E × L => ν {q | f (z.1, q) = f z}) :=
    measurable_measure_prodMk_left (measurableSet_observation_eq
      (hf.comp (measurable_fst.fst.prodMk measurable_snd)) (hf.comp measurable_fst))
  apply (Measure.ae_prod_iff_ae_ae (hm (measurableSet_singleton 0) |>.compl)).mpr
  exact Filter.Eventually.of_forall fun e =>
    ae_positive_observation_fiber ν (fun l => f (e, l))

theorem independent_resampling_ae_positive {T E L B : Type*}
    [MeasurableSpace T] [MeasurableSpace E] [MeasurableSpace L]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (external : T → E) (localInput : T → L) (restore : E × L → T)
    (obs : T → B) (he : Measurable external) (hl : Measurable localInput)
    (hr : Measurable restore) (ho : Measurable obs)
    (hinv : ∀ x, restore (external x, localInput x) = x)
    (hind : IndepFun external localInput ν) :
    ∀ᵐ x ∂ν, ν {q | obs (restore (external x, localInput q)) = obs x} ≠ 0 := by
  letI : IsProbabilityMeasure (ν.map localInput) := ν.isProbabilityMeasure_map hl.aemeasurable
  have hp := prod_ae_positive_observation_fiber (ν.map external) (ν.map localInput)
    (fun z => obs (restore z)) (ho.comp hr)
  rw [← hind.map_prod_eq_prod_map_map he.aemeasurable hl.aemeasurable] at hp
  have ha := ae_of_ae_map (he.prodMk hl).aemeasurable hp
  filter_upwards [ha] with x hx
  have hs : MeasurableSet {l | obs (restore (external x, l)) = obs x} :=
    (ho.comp (hr.comp (measurable_const.prodMk measurable_id)))
      (measurableSet_singleton (obs x))
  rw [hinv x] at hx
  simpa only [Measure.map_apply hl hs, Set.preimage_setOf_eq] using hx

end MeraConstraints.Replay
