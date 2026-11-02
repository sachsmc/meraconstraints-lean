import MeraConstraints.Probability.Independent
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite response laws from arbitrary probability spaces

The manuscript does not assume finite original latent state spaces. A finite
response partition therefore needs a probability argument in addition to the
pointwise structural identities. Here the sample space `Ω` is arbitrary and
`μ` is an actual probability measure. A measurable finite-valued map induces
a nonnegative real mass vector of total mass one.

We prove that finite observation maps transport these masses by the same
`pushforward` used by the algebraic development. For a **mutually independent**
family of finite response maps, their joint law is the product of the marginal
mass vectors. Independence is the usual measure-theoretic `iIndepFun`, not
pairwise independence or a new definition of the desired factorization.

All measurability assumptions are explicit. The original latent space can be
continuous, infinite, or multivariate. These results do not replace the separate
proof that a particular original graph model supplies the required independent
district maps.
-/

namespace MeraConstraints.MeasureFinite

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Atomic real masses of a finite observation of an arbitrary measure. -/
noncomputable def law {α : Type*} (μ : Measure Ω) (f : Ω → α) : α → ℝ :=
  fun a => (μ (f ⁻¹' {a})).toReal

theorem law_nonneg {α : Type*} (μ : Measure Ω) (f : Ω → α) (a : α) :
    0 ≤ law μ f a := ENNReal.toReal_nonneg

section FiniteLaw

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → α) (hf : Measurable f)

include hf

theorem sum_law : (∑ a, law μ f a) = 1 := by
  unfold law
  rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top μ (f ⁻¹' {a}))]
  have h := sum_measure_preimage_singleton (μ := μ) Finset.univ
    (f := f) (fun a _ => hf (measurableSet_singleton a))
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
  rw [h]
  norm_num

theorem law_mem_stdSimplex : law μ f ∈ stdSimplex ℝ α :=
  ⟨law_nonneg μ f, sum_law μ f hf⟩

/-- Observing a finite function after a measurable response partition is
exactly the finite-vector pushforward; the original sample space is arbitrary. -/
theorem law_comp [DecidableEq β] (g : α → β) :
    law μ (g ∘ f) = pushforward g (law μ f) := by
  classical
  funext b
  unfold law pushforward
  rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top μ (f ⁻¹' {a}))]
  congr 1
  have h := sum_measure_preimage_singleton (μ := μ)
    (Finset.univ.filter fun a => g a = b)
    (f := f) (fun a _ => hf (measurableSet_singleton a))
  have hs : f ⁻¹' (↑(Finset.univ.filter fun a => g a = b) : Set α) =
      (g ∘ f) ⁻¹' {b} := by
    ext ω
    simp
  rw [hs] at h
  exact h.symm

end FiniteLaw

section Independence

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {R : D → Type*} [∀ d, Fintype (R d)]
variable [∀ d, MeasurableSpace (R d)] [∀ d, MeasurableSingletonClass (R d)]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ∀ d, Ω → R d)

omit [DecidableEq D] [∀ d, Fintype (R d)] [IsProbabilityMeasure μ] in
/-- Full mutual independence gives the finite product law used in the paper.
No finite or countable assumption is imposed on `Ω`. -/
theorem law_joint_of_iIndepFun (hX : iIndepFun X μ) :
    law μ (fun ω d => X d ω) = Independent.joint (fun d => law μ (X d)) := by
  classical
  funext r
  have hs : (fun ω d => X d ω) ⁻¹' {r} = ⋂ d, X d ⁻¹' {r d} := by
    ext ω
    simp [funext_iff]
  have h : μ (⋂ d, X d ⁻¹' {r d}) = ∏ d, μ (X d ⁻¹' {r d}) := by
    simpa using hX.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun d => {r d}) (fun d _ => measurableSet_singleton (r d))
  unfold law Independent.joint
  rw [hs, h, ENNReal.toReal_prod]

/-- An arbitrary measurable evaluation of mutually independent finite responses
has exactly the real finite-vector law used by the Lean matrix construction. -/
theorem law_eval_of_iIndepFun {W : Type*} [DecidableEq W]
    (hXmeas : ∀ d, Measurable (X d)) (hX : iIndepFun X μ)
    (evaluate : (∀ d, R d) → W) :
    law μ (fun ω => evaluate (fun d => X d ω)) =
      pushforward evaluate (Independent.joint (fun d => law μ (X d))) := by
  have hmeas : Measurable (fun ω d => X d ω) := measurable_pi_lambda _ hXmeas
  have h := law_comp μ (fun ω d => X d ω) hmeas evaluate
  rw [law_joint_of_iIndepFun μ X hX] at h
  exact h

end Independence
end MeraConstraints.MeasureFinite
