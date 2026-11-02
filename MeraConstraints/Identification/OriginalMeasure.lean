import MeraConstraints.HiddenGraph.MeasureCanonicalization
import MeraConstraints.HiddenGraph.Measurability
import MeraConstraints.HiddenGraph.Intervention
import MeraConstraints.Identification
import MeraConstraints.CompactDistrict.Observable

/-!
# Observable district identification for the original measurable SCM

This chapter connects the actual original model, its observable product,
and its district intervention. The original input spaces are arbitrary.
We assume measurable structural mechanisms and mutually independent original
root/private inputs, and use the manuscript's standing strict positivity of
the observed law only for observational conditioning.

`original_measure_district_linear` identifies the product with the compact
binary matrix applied to the profile law **induced by the original model**.
`externalInterventionLaw` evaluates an actual surgical intervention on that
same model, preserving the actual input law. Pointwise intervention faithfulness
then gives its probability as the same matrix expression.

The equality `observableFactor_eq_externalInterventionLaw` is the probability
statement of `causalprop`, with the revised cumulative conditioning sets and
the explicit do-operation. No numerical or graphical-identification oracle is
an input to the proof. These identities hold at every c-degree; freedom to
choose arbitrary profile laws for completeness still requires c-degree ≤ 1.
-/

namespace MeraConstraints.Identification

open MeasureTheory ProbabilityTheory HiddenGraph

universe u v w z

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]
variable [∀ x, MeasurableSpace (Canonicalization.InputValue M x)]
variable {Ω : Type z} [MeasurableSpace Ω]

/-- The do-distribution obtained by intervening on precisely the external
observed parents of one district in the given original structural model. -/
noncomputable def externalInterventionLaw (μ : Measure Ω)
    (A : ∀ x, Ω → Canonicalization.InputValue M x) (d : DistrictId G)
    (setTo : FullAssign val) : CompactDistrict.MemberAssign val (observedDistrict G) d → ℝ :=
  MeasureFinite.law μ (fun ω => fun i : CompactDistrict.Member (observedDistrict G) d =>
    (M.intervene (CompactDistrict.externalTargets G.observed (observedDistrict G) d) setTo).eval
      (fun j => (A (.inr j) ω).down) (fun j => (A (.inl j) ω).down) i)

/-- The intervention reads just the original district profile. This law
identity requires measurability but does not require independence or positivity. -/
theorem externalInterventionLaw_eq_pushforward (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hMechanisms : Measurability.MechanismsMeasurable M)
    (d : DistrictId G) (setTo : FullAssign val) :
    externalInterventionLaw M μ A d setTo =
      pushforward (fun r => CompactDistrict.eval G.observed val (observedDistrict G) d r
        (fun j => setTo j)) (MeasureCanonicalization.canonicalLaw M μ A d) := by
  have hLocal := Measurability.localProfile_measurable M hMechanisms
  have hpoint : (fun ω => fun i : CompactDistrict.Member (observedDistrict G) d =>
      (M.intervene (CompactDistrict.externalTargets G.observed (observedDistrict G) d) setTo).eval
        (fun j => (A (.inr j) ω).down) (fun j => (A (.inl j) ω).down) i) =
      (fun ω => CompactDistrict.eval G.observed val (observedDistrict G) d
        (MeasureCanonicalization.profileMaps M A d ω) (fun j => setTo j)) := by
    funext ω
    exact M.eval_intervene_external_eq_compact
      (fun j => (A (.inr j) ω).down) (fun j => (A (.inl j) ω).down) d setTo
  unfold externalInterventionLaw
  rw [hpoint]
  exact MeasureFinite.law_comp μ (MeasureCanonicalization.profileMaps M A d)
    (MeasureCanonicalization.profileMaps_measurable M A hA hLocal d)
    (fun r => CompactDistrict.eval G.observed val (observedDistrict G) d r (fun j => setTo j))

/-- Interventional probabilities are compatibility sums for the original
model's induced profile law, including when the observed law has zeros. -/
theorem externalInterventionLaw_eq_mulVec (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hMechanisms : Measurability.MechanismsMeasurable M)
    (d : DistrictId G) (setTo : FullAssign val)
    (out : CompactDistrict.MemberAssign val (observedDistrict G) d) :
    externalInterventionLaw M μ A d setTo out =
      (CompactDistrict.matrix G.observed val (observedDistrict G) d).mulVec
        (MeasureCanonicalization.canonicalLaw M μ A d) (out, fun j => setTo j) := by
  classical
  rw [externalInterventionLaw_eq_pushforward M μ A hA hMechanisms d setTo]
  simp [pushforward, Matrix.mulVec, dotProduct, CompactDistrict.matrix_eq_eval,
    Finset.sum_filter, ite_mul]

/-- Proposition `prop:ident`, for the original measurable model: the observable
cumulative-conditioning product is `B r` with the induced district profile law. -/
theorem original_measure_district_linear (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hInd : iIndepFun A μ)
    (hMechanisms : Measurability.MechanismsMeasurable M)
    (hpos : ∀ y, 0 < MeasureCanonicalization.observedLaw M μ A y)
    (d : DistrictId G) (a : FullAssign val) :
    Reconstruction.observableFactor G.observed val (observedDistrict G)
        (MeasureCanonicalization.observedLaw M μ A) d a =
      (CompactDistrict.matrix G.observed val (observedDistrict G) d).mulVec
        (MeasureCanonicalization.canonicalLaw M μ A d)
        (CompactDistrict.project G.observed val (observedDistrict G) d a) := by
  have hLocal := Measurability.localProfile_measurable M hMechanisms
  have hobs := MeasureCanonicalization.observedLaw_eq_globalModel M μ A hA hInd hLocal
  have hq := MeasureCanonicalization.canonicalLaw_mem_stdSimplex M μ A hA hLocal
  have hposq : ∀ y, 0 < GlobalModel.observed G.observed val (observedDistrict G)
      (MeasureCanonicalization.canonicalLaw M μ A) y := by simpa [← hobs] using hpos
  rw [hobs]
  rw [← generated_factor_eq_observableFactor G.observed val (observedDistrict G)
    (MeasureCanonicalization.canonicalLaw M μ A) hq hposq d a]
  rw [GlobalModel.factor_eq_mulVec]
  exact (CompactDistrict.mulVec_project G.observed val (observedDistrict G) d _ a).symm

/-- Proposition `causalprop`: the observable product identifies the actual
external-parent intervention on the original SCM, not just a canonical proxy. -/
theorem observableFactor_eq_externalInterventionLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hInd : iIndepFun A μ)
    (hMechanisms : Measurability.MechanismsMeasurable M)
    (hpos : ∀ y, 0 < MeasureCanonicalization.observedLaw M μ A y)
    (d : DistrictId G) (a : FullAssign val) :
    Reconstruction.observableFactor G.observed val (observedDistrict G)
        (MeasureCanonicalization.observedLaw M μ A) d a =
      externalInterventionLaw M μ A d a (fun i => a i) := by
  rw [original_measure_district_linear M μ A hA hInd hMechanisms hpos d a,
    externalInterventionLaw_eq_mulVec M μ A hA hMechanisms d a]
  rfl

end MeraConstraints.Identification
