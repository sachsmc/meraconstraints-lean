import MeraConstraints.Probability.ReplayLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# An independent stream of candidate draws

The infinite product of a probability measure `ν` with itself is a probability
measure `trialMeasure ν` on sequences of draws. The coordinates are mutually
independent with law `ν` (`trials_independent`, `trials_common_law`), so the results
of `ReplayLaw` apply to them. For a fixed measurable set `S` with `ν S > 0`, almost
every sequence has a coordinate in `S` (`trials_ae_success`), and the first such
coordinate has the law `ν` conditioned on `S` (`trials_replay_map_eq_cond`). The
draws take values in an arbitrary measurable space. In the split model, this
sequence is the input of the new unobserved variable with children `D`, with `ν`
the law of the original inputs.
-/

namespace MeraConstraints.Replay

open MeasureTheory ProbabilityTheory
open HiddenGraph.StrongFaceSplitting (firstReplay)

variable {T : Type*} [MeasurableSpace T] (ν : Measure T) [IsProbabilityMeasure ν]

noncomputable def trialMeasure : Measure (ℕ → T) := Measure.infinitePi (fun _ : ℕ => ν)

instance trialMeasure_probability : IsProbabilityMeasure (trialMeasure ν) := by
  unfold trialMeasure
  infer_instance

theorem trials_independent : iIndepFun (fun n (ω : ℕ → T) => ω n) (trialMeasure ν) := by
  exact iIndepFun_infinitePi (X := fun (_ : ℕ) (x : T) => x) (fun _ => measurable_id)

theorem trials_common_law (n : ℕ) : (trialMeasure ν).map (fun ω => ω n) = ν :=
  Measure.infinitePi_map_eval (fun _ : ℕ => ν) n

/-- For a fixed measurable set `S` with `ν S > 0`, almost every stream has a
coordinate in `S`. -/
theorem trials_ae_success (S : Set T) (hS : MeasurableSet S) (hpos : ν S ≠ 0) :
    ∀ᵐ ω ∂trialMeasure ν, ∃ n, ω n ∈ S :=
  ae_exists_accepted (trialMeasure ν) ν (fun n ω => ω n)
    (fun n => measurable_pi_apply n) (trials_independent ν) (trials_common_law ν) S hS hpos

/-- For a fixed measurable set `S` with `ν S > 0`, the first coordinate in `S` has
the law `ν` conditioned on `S`. The fallback has probability zero. -/
theorem trials_replay_map_eq_cond (S : Set T) (hS : MeasurableSet S) (hpos : ν S ≠ 0) :
    (trialMeasure ν).map (fun ω => firstReplay ω (· ∈ S)) = ProbabilityTheory.cond ν S :=
  firstReplay_map_eq_cond (trialMeasure ν) ν (fun n ω => ω n)
    (fun n => measurable_pi_apply n) (trials_independent ν) (trials_common_law ν) S hS hpos

end MeraConstraints.Replay
