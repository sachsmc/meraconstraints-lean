import MeraConstraints.HiddenGraph.Canonicalization
import MeraConstraints.Probability.MeasureFinite
import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# Canonicalization of arbitrary measurable original inputs

The observed variables are finite; the original latent and private input
spaces in this chapter are not restricted to be finite or countable. They
are random variables on an arbitrary probability space with the usual full
mutual independence assumption. Structural mechanisms are the actual given
`HiddenGraph.SCM`, not a chosen canonical representative.

The deterministic `Canonicalization.localProfile` map reads only original
inputs in its own graph district. Disjoint grouping preserves independence
of the original input variables, and measurable local profile maps preserve
that independence. `MeasureFinite` then turns their induced finite measures
into the normalized real vectors required by the matrix development.

Measurability is an explicit NPSEM requirement: `hLocal` asks that each local
response map be measurable in its original inputs. It is not a hypothesis
of output independence or of observational identification. With finite
observed state spaces this is the finite collection of measurable structural
mechanisms indexed by parent assignments.

The resulting equality of observed laws is valid at every c-degree and even
on zero-probability configurations. Only the converse unrestricted-profile
realization requires c-degree at most one.
-/

namespace MeraConstraints.HiddenGraph.MeasureCanonicalization

open MeasureTheory ProbabilityTheory
open Canonicalization

universe u v w z

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]
variable [∀ x, MeasurableSpace (InputValue M x)]
variable {Ω : Type z} [MeasurableSpace Ω]

/-- District response maps induced by the given original random inputs. -/
def profileMaps (A : ∀ x, Ω → InputValue M x) (d : DistrictId G) :
    Ω → ResponseProfile M d :=
  fun ω => localProfile M d (fun x => A x ω)

omit [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, MeasurableSingletonClass (val i)] in
theorem profileMaps_measurable (A : ∀ x, Ω → InputValue M x)
    (hA : ∀ x, Measurable (A x))
    (hLocal : ∀ d, Measurable (localProfile M d)) (d : DistrictId G) :
    Measurable (profileMaps M A d) :=
  (hLocal d).comp (measurable_pi_lambda _ (fun x => hA x))

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, MeasurableSingletonClass (val i)] in
/-- Independence of response profiles follows from the original input
independence and local mechanisms; it is not imposed after canonicalization. -/
theorem profileMaps_iIndepFun (μ : Measure Ω) (A : ∀ x, Ω → InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hInd : iIndepFun A μ)
    (hLocal : ∀ d, Measurable (localProfile M d)) :
    iIndepFun (profileMaps M A) μ := by
  have h := Independent.iIndepFun_grouped (districtOf G) (InputValue M) μ A hA hInd
  exact h.comp (localProfile M) hLocal

/-- Finite district masses obtained from the actual original probability law. -/
noncomputable def canonicalLaw (μ : Measure Ω) (A : ∀ x, Ω → InputValue M x)
    (d : DistrictId G) : ResponseProfile M d → ℝ :=
  MeasureFinite.law μ (profileMaps M A d)

theorem canonicalLaw_mem_stdSimplex (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → InputValue M x) (hA : ∀ x, Measurable (A x))
    (hLocal : ∀ d, Measurable (localProfile M d)) (d : DistrictId G) :
    canonicalLaw M μ A d ∈ stdSimplex ℝ (ResponseProfile M d) :=
  MeasureFinite.law_mem_stdSimplex μ _ (profileMaps_measurable M A hA hLocal d)

/-- The law of the original SCM evaluated at its given original inputs. -/
noncomputable def observedLaw (μ : Measure Ω) (A : ∀ x, Ω → InputValue M x) :
    FullAssign val → ℝ :=
  MeasureFinite.law μ (fun ω => evalInputs M (fun x => A x ω))

/-- Probability-law faithfulness for arbitrary measurable independent inputs.
There is no finite latent-input assumption, no c-degree bound, and no
assumed equality of observable and interventional factors. -/
theorem observedLaw_eq_globalModel (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → InputValue M x) (hA : ∀ x, Measurable (A x))
    (hInd : iIndepFun A μ) (hLocal : ∀ d, Measurable (localProfile M d)) :
    observedLaw M μ A = GlobalModel.observed G.observed val (observedDistrict G)
      (canonicalLaw M μ A) := by
  have hmeas := profileMaps_measurable M A hA hLocal
  have hind := profileMaps_iIndepFun M μ A hA hInd hLocal
  have hpoint : (fun ω => evalInputs M (fun x => A x ω)) =
      (fun ω => evalR (GlobalModel.assemble G.observed val (observedDistrict G)
        (fun d => profileMaps M A d ω))) := by
    funext ω
    exact evalInputs_eq_assembled M _
  unfold observedLaw
  rw [hpoint]
  exact MeasureFinite.law_eval_of_iIndepFun μ (profileMaps M A) hmeas hind
    (fun r => evalR (GlobalModel.assemble G.observed val (observedDistrict G) r))

theorem observedLaw_mem_stdSimplex (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → InputValue M x) (hA : ∀ x, Measurable (A x))
    (hInd : iIndepFun A μ) (hLocal : ∀ d, Measurable (localProfile M d)) :
    observedLaw M μ A ∈ stdSimplex ℝ (FullAssign val) := by
  rw [observedLaw_eq_globalModel M μ A hA hInd hLocal]
  exact GlobalModel.observed_mem_stdSimplex _ _ _ _
    (canonicalLaw_mem_stdSimplex M μ A hA hLocal)

end MeraConstraints.HiddenGraph.MeasureCanonicalization
