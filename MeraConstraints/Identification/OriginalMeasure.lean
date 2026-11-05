import MeraConstraints.HiddenGraph.MeasureCanonicalization
import MeraConstraints.HiddenGraph.Measurability
import MeraConstraints.HiddenGraph.Intervention
import MeraConstraints.Identification
import MeraConstraints.CompactDistrict.Observable

/-!
# Propositions 1 and 2 for the structural model

This chapter proves the identification statements for a structural model on the hidden
variables DAG whose unobserved inputs take values in arbitrary measurable spaces. The
hypotheses are measurable mechanisms, mutually independent unobserved inputs and,
for the conditionals defining the district factor, a strictly positive observed
distribution.

`original_measure_district_linear` is Proposition 1 (`prop:ident`): the district factor
equals `B r`, where `r` is the distribution of the response function variables that the
model induces on the district's profiles (`canonicalLaw`, from
`HiddenGraph.MeasureCanonicalization`). `externalInterventionLaw` is the distribution of
the district's members after the structural model is intervened on the external
parents. `districtFactor_eq_externalInterventionLaw` is Proposition 2 (`causalprop`): the
district factor equals `Pr(V₁ ∣ do(V₂ = v₂))`.

The manuscript states Proposition 1 for c-degree at most 1, and it should be read in
that setting, where `r` can be any probability vector, so the district factors form
the district polytope. The proof of the identity does not use the bound, so the
statement omits it. Proposition 2 has no c-degree restriction in the manuscript.
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

/-- The distribution of the members of district `d` after the structural model is
intervened on the external parents of `d`, setting them to their values in `setTo`:
`Pr(V₁ ∣ do(V₂ = v₂))`. -/
noncomputable def externalInterventionLaw (μ : Measure Ω)
    (A : ∀ x, Ω → Canonicalization.InputValue M x) (d : DistrictId G)
    (setTo : FullAssign val) : CompactDistrict.MemberAssign val (observedDistrict G) d → ℝ :=
  MeasureFinite.law μ (fun ω => fun i : CompactDistrict.Member (observedDistrict G) d =>
    (M.intervene (CompactDistrict.externalTargets G.observed (observedDistrict G) d) setTo).eval
      (fun j => (A (.inr j) ω).down) (fun j => (A (.inl j) ω).down) i)

/-- The interventional distribution is the image of the profile distribution
`canonicalLaw` under evaluating the district with the external parents set to `setTo`.
It needs measurability only, not independence or positivity. -/
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

/-- The interventional probabilities are `B r` for the induced profile distribution
`r = canonicalLaw`. The observed distribution may have zero probabilities. -/
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

/-- Proposition 1 (`prop:ident`) for the structural model: the district factor of the
observed distribution is `B r`, where `r` is the profile distribution the model
induces. There is no c-degree assumption. -/
theorem original_measure_district_linear (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hInd : iIndepFun A μ)
    (hMechanisms : Measurability.MechanismsMeasurable M)
    (hpos : ∀ y, 0 < MeasureCanonicalization.observedLaw M μ A y)
    (d : DistrictId G) (a : FullAssign val) :
    Reconstruction.districtFactor G.observed val (observedDistrict G)
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
  rw [← generated_factor_eq_districtFactor G.observed val (observedDistrict G)
    (MeasureCanonicalization.canonicalLaw M μ A) hq hposq d a]
  rw [GlobalModel.factor_eq_mulVec]
  exact (CompactDistrict.mulVec_project G.observed val (observedDistrict G) d _ a).symm

/-- Proposition 2 (`causalprop`): the district factor of the observed distribution
equals the interventional distribution of the district's members under the
intervention on its external parents (`externalInterventionLaw`). There is no c-degree
assumption. -/
theorem districtFactor_eq_externalInterventionLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hInd : iIndepFun A μ)
    (hMechanisms : Measurability.MechanismsMeasurable M)
    (hpos : ∀ y, 0 < MeasureCanonicalization.observedLaw M μ A y)
    (d : DistrictId G) (a : FullAssign val) :
    Reconstruction.districtFactor G.observed val (observedDistrict G)
        (MeasureCanonicalization.observedLaw M μ A) d a =
      externalInterventionLaw M μ A d a (fun i => a i) := by
  rw [original_measure_district_linear M μ A hA hInd hMechanisms hpos d a,
    externalInterventionLaw_eq_mulVec M μ A hA hMechanisms d a]
  rfl

end MeraConstraints.Identification
