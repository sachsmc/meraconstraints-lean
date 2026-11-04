import MeraConstraints.Probability.ReplayLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# An actual independent candidate stream for conditional replay

The infinite product of the original candidate law supplies a probability
space of trial sequences. Coordinate projections are measurable, mutually
independent, and have the original law. The first-replay theorem therefore
applies to a concrete sampler, rather than only to a hypothetical iid family.

Mathlib's infinite product is available for arbitrary measurable probability
spaces. This construction imposes no finiteness, countability or standard-
Borel restriction on candidate states. Applying it to the graph's random
boundary context and proving supported-fiber positivity remain separate steps.
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

/-- A concrete independent stream almost surely supplies an accepted trial
on every fixed measurable acceptance set of positive original probability. -/
theorem trials_ae_success (S : Set T) (hS : MeasurableSet S) (hpos : ν S ≠ 0) :
    ∀ᵐ ω ∂trialMeasure ν, ∃ n, ω n ∈ S :=
  ae_exists_accepted (trialMeasure ν) ν (fun n ω => ω n)
    (fun n => measurable_pi_apply n) (trials_independent ν) (trials_common_law ν) S hS hpos

/-- Exact conditional law of the actual structural selector on the explicit
independent trial probability space. Its fallback has probability zero. -/
theorem trials_replay_map_eq_cond (S : Set T) (hS : MeasurableSet S) (hpos : ν S ≠ 0) :
    (trialMeasure ν).map (fun ω => firstReplay ω (· ∈ S)) = ProbabilityTheory.cond ν S :=
  firstReplay_map_eq_cond (trialMeasure ν) ν (fun n ω => ω n)
    (fun n => measurable_pi_apply n) (trials_independent ν) (trials_common_law ν) S hS hpos

end MeraConstraints.Replay
