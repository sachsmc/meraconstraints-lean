import MeraConstraints.Probability.ReplaySelection
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The first accepted trial has the conditional law

Let the trials `X 0, X 1, …` be mutually independent with a common law `ν`, and let
`S` be a measurable set with `ν S > 0`. The probability that the first accepted
trial is the `n`th and lies in `B` is `(1 - ν S)^n * ν (S ∩ B)`. Summing the
geometric series shows that some trial is accepted almost surely
(`ae_exists_accepted`), and that the first accepted trial has the law `ν`
conditioned on `S` (`firstReplay_map_eq_cond`). This is the step that makes
conditional replay produce the correct conditional distribution. The trials take
values in an arbitrary measurable space. The independent trials are hypotheses
here; `ReplayTrials` constructs them.
-/

namespace MeraConstraints.Replay

open MeasureTheory ProbabilityTheory Set
open HiddenGraph.StrongFaceSplitting (firstReplay)

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
  (X : ℕ → Ω → T) (hX : ∀ n, Measurable (X n)) (hInd : iIndepFun X μ)
  (hLaw : ∀ n, μ.map (X n) = ν) (S : Set T) (hS : MeasurableSet S)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include hX hLaw in
theorem trial_preimage (n : ℕ) (B : Set T) (hB : MeasurableSet B) : μ (X n ⁻¹' B) = ν B := by
  rw [← Measure.map_apply (hX n) hB, hLaw n]

include hX hInd hLaw hS

omit [IsProbabilityMeasure μ] in
/-- The probability that the first accepted trial is the `n`th and lies in `B`.
This uses mutual independence of all the trials. -/
theorem firstHit_measure (B : Set T) (hB : MeasurableSet B) (n : ℕ) :
    μ (firstHit X S B n) = (1 - ν S) ^ n * ν (S ∩ B) := by
  classical
  have hm (j : ℕ) : MeasurableSet (if j = n then S ∩ B else Sᶜ) := by
    split
    · exact hS.inter hB
    · exact hS.compl
  rw [firstHit, hInd.measure_inter_preimage_eq_mul _ (fun j _ => hm j)]
  rw [Finset.prod_insert (by simp)]
  have hrest : (∏ j ∈ Finset.range n, μ (X j ⁻¹' (if j = n then S ∩ B else Sᶜ))) =
      (ν Sᶜ) ^ n := by
    calc
      _ = ∏ j ∈ Finset.range n, ν Sᶜ := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_neg (ne_of_lt (Finset.mem_range.mp hj))]
        exact trial_preimage μ ν X hX hLaw j Sᶜ hS.compl
      _ = _ := by simp
  rw [if_pos rfl, trial_preimage μ ν X hX hLaw n (S ∩ B) (hS.inter hB), hrest,
    measure_compl hS (measure_ne_top ν S), measure_univ]
  exact mul_comm _ _

omit [IsProbabilityMeasure μ] in
/-- Summing over `n`, the probability that some trial is accepted and the first
one lies in `B` is `ν (S ∩ B) / ν S`. -/
theorem firstHit_union_measure (B : Set T) (hB : MeasurableSet B) :
    μ (⋃ n, firstHit X S B n) = (ν S)⁻¹ * ν (S ∩ B) := by
  rw [measure_iUnion (firstHit_pairwise_disjoint X S B)
    (fun n => firstHit_measurable X S B hX hS hB n)]
  simp_rw [firstHit_measure μ ν X hX hInd hLaw S hS B hB]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel (by simp) (prob_le_one : ν S ≤ 1)]

/-- If `ν S > 0`, almost surely some trial is accepted. -/
theorem ae_exists_accepted (hpos : ν S ≠ 0) : ∀ᵐ ω ∂μ, ∃ n, X n ω ∈ S := by
  apply (mem_ae_iff_prob_eq_one (success_measurable X S hX hS)).mpr
  rw [success_eq_union, firstHit_union_measure μ ν X hX hInd hLaw S hS Set.univ MeasurableSet.univ,
    inter_univ, ENNReal.inv_mul_cancel hpos (measure_ne_top ν S)]

/-- The first accepted trial lies in a measurable set `B` with probability
`ν (S ∩ B) / ν S`. -/
theorem firstReplay_preimage_measure (hpos : ν S ≠ 0) (B : Set T) (hB : MeasurableSet B) :
    μ ((fun ω => firstReplay (fun n => X n ω) (· ∈ S)) ⁻¹' B) = (ν S)⁻¹ * ν (S ∩ B) := by
  have heq : ((fun ω => firstReplay (fun n => X n ω) (· ∈ S)) ⁻¹' B) =ᵐ[μ]
      (⋃ n, firstHit X S B n) := by
    filter_upwards [ae_exists_accepted μ ν X hX hInd hLaw S hS hpos] with ω hω
    apply propext
    change firstReplay (fun n => X n ω) (· ∈ S) ∈ B ↔ ω ∈ ⋃ n, firstHit X S B n
    simpa only [mem_iUnion] using mem_selected_iff X S B ω hω
  rw [measure_congr heq]
  exact firstHit_union_measure μ ν X hX hInd hLaw S hS B hB

/-- The law of the first accepted trial is `ν` conditioned on `S`. The fallback,
used when no trial is accepted, occurs with probability zero. -/
theorem firstReplay_map_eq_cond (hpos : ν S ≠ 0) :
    μ.map (fun ω => firstReplay (fun n => X n ω) (· ∈ S)) = ProbabilityTheory.cond ν S := by
  ext B hB
  rw [Measure.map_apply (firstReplay_measurable X S hX hS) hB,
    firstReplay_preimage_measure μ ν X hX hInd hLaw S hS hpos B hB,
    ProbabilityTheory.cond_apply hS]

end MeraConstraints.Replay
