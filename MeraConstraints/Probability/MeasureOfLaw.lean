import MeraConstraints.Probability.MeasureFinite
import Mathlib.Data.ENNReal.BigOperators

/-!
# Probability measures from probability vectors

The proof of Proposition 3 (`prop:complete`) constructs a model from probability
vectors `r_j` for the response function variables of the districts. This chapter
turns a probability vector `q` on a finite type into a probability measure
`measureOfLaw q hq`, the sum of point masses with weights `q a`. The law of this
measure is `q` (`law_measureOfLaw`), and the law of any function of it is the
`pushforward` of `q` (`law_measureOfLaw_eval`).

For a product vector `Independent.joint q`, the measure is the product measure of
the coordinate measures (`measureOfLaw_joint_eq_pi`), so the coordinate maps are
mutually independent (`iIndepFun_measureOfLaw_joint`). The value types are finite
with measurable singletons, so every subset is measurable.
-/

namespace MeraConstraints.MeasureFinite

open MeasureTheory ProbabilityTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The probability measure on `α` that gives each point `a` the mass `q a`. -/
noncomputable def measureOfLaw (q : α → ℝ) (_hq : q ∈ stdSimplex ℝ α) : Measure α :=
  ∑ a, ENNReal.ofReal (q a) • Measure.dirac a

instance measureOfLaw_isProbabilityMeasure (q : α → ℝ) (hq : q ∈ stdSimplex ℝ α) :
    IsProbabilityMeasure (measureOfLaw q hq) := by
  constructor
  have hu : measureOfLaw q hq Set.univ = ∑ a, ENNReal.ofReal (q a) := by
    simp [measureOfLaw, Measure.coe_finsetSum, Finset.sum_apply]
  rw [hu]
  simpa only [hq.2, ENNReal.ofReal_one] using
    (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun a _ => hq.1 a)).symm

@[simp] theorem measureOfLaw_singleton (q : α → ℝ) (hq : q ∈ stdSimplex ℝ α) (a : α) :
    measureOfLaw q hq {a} = ENNReal.ofReal (q a) := by
  classical
  simp [measureOfLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Set.indicator_apply, mul_ite]

/-- The law of the identity map under `measureOfLaw q hq` is `q`. -/
@[simp] theorem law_measureOfLaw (q : α → ℝ) (hq : q ∈ stdSimplex ℝ α) :
    law (measureOfLaw q hq) id = q := by
  funext a
  simp only [law, Set.preimage_id, measureOfLaw_singleton, ENNReal.toReal_ofReal (hq.1 a)]

/-- The law of `f` under `measureOfLaw q hq` is the pushforward of `q` along `f`. -/
theorem law_measureOfLaw_eval {β : Type*} [DecidableEq β]
    (q : α → ℝ) (hq : q ∈ stdSimplex ℝ α) (f : α → β) :
    law (measureOfLaw q hq) f = pushforward f q := by
  have h := law_comp (measureOfLaw q hq) id measurable_id f
  simpa only [Function.comp_id, law_measureOfLaw] using h

section ProductLaws

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {R : D → Type*} [∀ d, Fintype (R d)]
variable [∀ d, MeasurableSpace (R d)] [∀ d, MeasurableSingletonClass (R d)]

/-- The measure of a product vector is the product of the coordinate measures. -/
theorem measureOfLaw_joint_eq_pi (q : ∀ d, R d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (R d)) :
    measureOfLaw (Independent.joint q) (Independent.joint_mem_stdSimplex q hq) =
      Measure.pi (fun d => measureOfLaw (q d) (hq d)) := by
  apply Measure.ext_of_singleton
  intro r
  rw [measureOfLaw_singleton, Measure.pi_singleton]
  simp_rw [measureOfLaw_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun d _ => (hq d).1 (r d))

/-- Under the measure of a product vector, the coordinate maps are mutually
independent random variables. -/
theorem iIndepFun_measureOfLaw_joint (q : ∀ d, R d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (R d)) :
    iIndepFun (fun d (r : ∀ d, R d) => r d)
      (measureOfLaw (Independent.joint q) (Independent.joint_mem_stdSimplex q hq)) := by
  rw [measureOfLaw_joint_eq_pi q hq]
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

end ProductLaws
end MeraConstraints.MeasureFinite
