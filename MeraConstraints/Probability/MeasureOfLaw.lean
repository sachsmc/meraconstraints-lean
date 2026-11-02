import MeraConstraints.Probability.MeasureFinite
import Mathlib.Data.ENNReal.BigOperators

/-!
# Actual probability measures for finite simplex laws

The response-profile sufficiency construction first produces a nonnegative
real vector of total mass one. To obtain a literal original probability
model, this chapter turns that vector into an actual probability measure:
the finite sum of Dirac masses with those weights.

Its real atom law is the original vector, and observing any finite-input
evaluation map has precisely the algebraic `pushforward` law. For a product
vector, the resulting measure is the usual product measure of its coordinate
measures. Consequently its coordinate maps are mutually independent in the
measure-theoretic sense. Thus finite simplex witnesses can be used as genuine
probability-space witnesses, rather than as a substitute definition of one.

Normalization and nonnegativity are explicit hypotheses throughout. The
measurable spaces have measurable singletons; on finite state spaces this
makes all subsets measurable.
-/

namespace MeraConstraints.MeasureFinite

open MeasureTheory ProbabilityTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The actual finite probability measure with the prescribed real masses. -/
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

/-- Recover the prescribed real atom vector from its probability measure. -/
@[simp] theorem law_measureOfLaw (q : α → ℝ) (hq : q ∈ stdSimplex ℝ α) :
    law (measureOfLaw q hq) id = q := by
  funext a
  simp only [law, Set.preimage_id, measureOfLaw_singleton, ENNReal.toReal_ofReal (hq.1 a)]

/-- Evaluation under the literal probability measure agrees with the finite
vector pushforward used in the matrix development. -/
theorem law_measureOfLaw_eval {β : Type*} [DecidableEq β]
    (q : α → ℝ) (hq : q ∈ stdSimplex ℝ α) (f : α → β) :
    law (measureOfLaw q hq) f = pushforward f q := by
  have h := law_comp (measureOfLaw q hq) id measurable_id f
  simpa only [Function.comp_id, law_measureOfLaw] using h

section ProductLaws

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {R : D → Type*} [∀ d, Fintype (R d)]
variable [∀ d, MeasurableSpace (R d)] [∀ d, MeasurableSingletonClass (R d)]

/-- A product simplex vector produces exactly the product of its actual
coordinate probability measures. -/
theorem measureOfLaw_joint_eq_pi (q : ∀ d, R d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (R d)) :
    measureOfLaw (Independent.joint q) (Independent.joint_mem_stdSimplex q hq) =
      Measure.pi (fun d => measureOfLaw (q d) (hq d)) := by
  apply Measure.ext_of_singleton
  intro r
  rw [measureOfLaw_singleton, Measure.pi_singleton]
  simp_rw [measureOfLaw_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun d _ => (hq d).1 (r d))

/-- Independent profile coordinates as actual measurable random variables. -/
theorem iIndepFun_measureOfLaw_joint (q : ∀ d, R d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (R d)) :
    iIndepFun (fun d (r : ∀ d, R d) => r d)
      (measureOfLaw (Independent.joint q) (Independent.joint_mem_stdSimplex q hq)) := by
  rw [measureOfLaw_joint_eq_pi q hq]
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

end ProductLaws
end MeraConstraints.MeasureFinite
