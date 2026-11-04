import MeraConstraints.Probability.ReplaySelection
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Independent first replay has the conditional law

For measurable independent trials with a common law, the first hit in a
measurable acceptance set has geometric first-hit masses. Their sum is one
when that set has positive probability, proving almost-sure success. The
selected candidate has exactly the common law conditioned on acceptance.

The selector is the actual `firstReplay` used by the split SCM. No success
or conditional-distribution conclusion is assumed, and no restriction is
placed on the candidate measurable space. The trial sequence and its full
mutual independence are inputs to this generic law; constructing it and
applying the law to graph-dependent fibers are separate assembly steps.
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
/-- Exact finite-cylinder probability; full independence is used here. -/
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
/-- Summing disjoint first-hit cylinders gives the conditional mass. -/
theorem firstHit_union_measure (B : Set T) (hB : MeasurableSet B) :
    μ (⋃ n, firstHit X S B n) = (ν S)⁻¹ * ν (S ∩ B) := by
  rw [measure_iUnion (firstHit_pairwise_disjoint X S B)
    (fun n => firstHit_measurable X S B hX hS hB n)]
  simp_rw [firstHit_measure μ ν X hX hInd hLaw S hS B hB]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel (by simp) (prob_le_one : ν S ≤ 1)]

/-- Positive acceptance probability implies almost-sure success. -/
theorem ae_exists_accepted (hpos : ν S ≠ 0) : ∀ᵐ ω ∂μ, ∃ n, X n ω ∈ S := by
  apply (mem_ae_iff_prob_eq_one (success_measurable X S hX hS)).mpr
  rw [success_eq_union, firstHit_union_measure μ ν X hX hInd hLaw S hS Set.univ MeasurableSet.univ,
    inter_univ, ENNReal.inv_mul_cancel hpos (measure_ne_top ν S)]

/-- The first accepted trial has the conditional probability of every
measurable event, including for arbitrary infinite candidate spaces. -/
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

/-- Exact measure-valued conditional law of the same replay selector as
the structural construction. The no-hit fallback lies on a null event. -/
theorem firstReplay_map_eq_cond (hpos : ν S ≠ 0) :
    μ.map (fun ω => firstReplay (fun n => X n ω) (· ∈ S)) = ProbabilityTheory.cond ν S := by
  ext B hB
  rw [Measure.map_apply (firstReplay_measurable X S hX hS) hB,
    firstReplay_preimage_measure μ ν X hX hInd hLaw S hS hpos B hB,
    ProbabilityTheory.cond_apply hS]

end MeraConstraints.Replay
