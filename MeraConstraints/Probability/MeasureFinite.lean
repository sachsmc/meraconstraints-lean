import MeraConstraints.Probability.Independent
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite laws of measurable maps on arbitrary probability spaces

The manuscript does not assume that the unobserved variables have finitely many
values. The sample space `Ω` here is arbitrary and `μ` is a probability measure on
it. A measurable map `f` into a finite type has a law `law μ f`: the vector of
probabilities `μ (f = a)`, which is a probability vector (`law_mem_stdSimplex`).

Applying a further map `g` to `f` corresponds to the finite-vector `pushforward`
(`law_comp`). If the maps `X d` are mutually independent (`iIndepFun`), the law of
the vector `(X d)_d` is the product `Independent.joint` of their laws
(`law_joint_of_iIndepFun`). Mutual independence is assumed in this form, not
pairwise independence.

These facts connect a model with arbitrary unobserved variables to the finite
vectors used in the algebra of the district polytopes.
-/

namespace MeraConstraints.MeasureFinite

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law of `f` under `μ`: the vector of probabilities `μ (f = a)`. -/
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

/-- The law of `g ∘ f` is the pushforward along `g` of the law of `f`. The sample
space is arbitrary. -/
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
/-- If the maps `X d` are mutually independent, the law of the vector `(X d)_d` is
the product of their laws. The sample space is arbitrary. -/
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

/-- Any function `evaluate` of mutually independent finite-valued maps has the
law obtained by pushing the product of their laws forward along `evaluate`. -/
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
