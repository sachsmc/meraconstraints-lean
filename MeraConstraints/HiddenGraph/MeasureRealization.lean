import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.SCMRealization
import MeraConstraints.Probability.MeasureOfLaw
import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# The realization as a probability model

This file turns the construction of `SCMRealization.lean` into a
`HiddenGraph.ProbabilityModel`, given a distribution of the profile of each
district (`probabilityModelOfProfiles`). Its observed distribution is
`sourceObserved` (`probabilityModelOfProfiles_observed`). With
`sourceObserved_eq_observed` this realizes the distributions of
Proposition 3 (`prop:complete`) by a structural model with independent inputs
on the original hidden variables DAG, when every district has c-degree at most
one.

The probability space is the finite set of tuples of source profiles, with the
product distribution used for `sourceObserved`. Each source is the input of one
vertex: an unobserved variable, or an observed variable with no unobserved
parent. The input of a vertex is a function of its own source only, so the
inputs are mutually independent. The private noise of an observed variable with
an unobserved parent is constant. All spaces are discrete, so measurability is
automatic. The identity `probabilityModelOfProfiles_observed` itself holds for
every c-degree.
-/

namespace MeraConstraints.HiddenGraph

open MeasureTheory ProbabilityTheory

universe u

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type u)
  [∀ i, Nonempty (val i)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [DecidableEq (DistrictId G)]

abbrev RealizationSample := ∀ s : Source G, SourceProfile G val s

local instance sourceProfileSpace (s : Source G) : MeasurableSpace (SourceProfile G val s) := ⊤
local instance sourceProfileSingleton (s : Source G) :
    MeasurableSingletonClass (SourceProfile G val s) := by infer_instance

local instance realizerLatentFintype (j : Fin ℓ) :
    Fintype ((profileSCM G val).latentValue j) := by
  change Fintype (SourceProfile G val (.inl j))
  infer_instance

local instance realizerPrivateFintype (i : Fin n) :
    Fintype ((profileSCM G val).privateNoise i) := by
  change Fintype (RespFun G.observed val i)
  infer_instance

abbrev RealizationInput (x : Vertex (n := n) (ℓ := ℓ)) :=
  Canonicalization.InputValue (profileSCM G val) x

local instance realizationInputSpace (x : Vertex (n := n) (ℓ := ℓ)) :
    MeasurableSpace (RealizationInput G val x) := ⊤
local instance realizationInputSingleton (x : Vertex (n := n) (ℓ := ℓ)) :
    MeasurableSingletonClass (RealizationInput G val x) := by infer_instance

/-- The vertex whose input is the source: the unobserved variable, or the
observed variable whose private noise it is. -/
def realizationSourceVertex : Source G → Vertex (n := n) (ℓ := ℓ)
  | .inl j => .inr j
  | .inr i => .inl i

/-- The input of the vertex `x`, as a function of the sample. -/
noncomputable def realizationInputs (x : Vertex (n := n) (ℓ := ℓ))
    (r : RealizationSample G val) : RealizationInput G val x :=
  match x with
  | .inl i => ULift.up (sourcePrivateInput G val r i)
  | .inr j => ULift.up (sourceLatentInput G val r j)

abbrev GroupedRealizationInput (x : Vertex (n := n) (ℓ := ℓ)) :=
  ∀ s : {s : Source G // realizationSourceVertex G s = x}, SourceProfile G val s

/-- The input of a vertex as a function of the sources assigned to it. The
private noise of an observed variable with an unobserved parent is constant, and
no source is assigned to it. -/
noncomputable def groupedRealizationMap (x : Vertex (n := n) (ℓ := ℓ)) :
    GroupedRealizationInput G val x → RealizationInput G val x := by
  classical
  cases x with
  | inl i =>
      exact fun r => if hi : HasLatentParent G i then ULift.up (defaultResponse G val i)
        else ULift.up (r ⟨.inr ⟨i, hi⟩, rfl⟩ ⟨i, rfl⟩)
  | inr j => exact fun r => ULift.up (r ⟨.inl j, rfl⟩)

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [DecidableEq (DistrictId G)] in
theorem groupedRealizationMap_restrict (x : Vertex (n := n) (ℓ := ℓ))
    (r : RealizationSample G val) :
    groupedRealizationMap G val x (fun s => r s.val) = realizationInputs G val x r := by
  cases x with
  | inl i =>
      by_cases hi : HasLatentParent G i <;>
        simp [groupedRealizationMap, realizationInputs, sourcePrivateInput, hi]
  | inr j => rfl

/-- The product distribution of the sources, as a probability measure. -/
noncomputable def realizationMeasure (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) :
    Measure (RealizationSample G val) :=
  MeasureFinite.measureOfLaw (Independent.joint (fun s => q (sourceDistrict G s)))
    (Independent.joint_mem_stdSimplex _ (fun s => hq (sourceDistrict G s)))

instance realizationMeasure_probability (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) :
    IsProbabilityMeasure (realizationMeasure G val q hq) := by
  unfold realizationMeasure
  infer_instance

/-- The inputs are mutually independent, because each is a function of its own
source and the sources are independent. -/
theorem realizationInputs_independent (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) :
    iIndepFun (realizationInputs G val) (realizationMeasure G val q hq) := by
  classical
  have hsource : iIndepFun (fun s (r : RealizationSample G val) => r s)
      (realizationMeasure G val q hq) :=
    MeasureFinite.iIndepFun_measureOfLaw_joint (fun s => q (sourceDistrict G s))
      (fun s => hq (sourceDistrict G s))
  have hgroup := Independent.iIndepFun_grouped (realizationSourceVertex G)
    (SourceProfile G val) (realizationMeasure G val q hq)
    (fun s (r : RealizationSample G val) => r s)
    (fun s => measurable_pi_apply s) hsource
  have hmaps : ∀ x, Measurable (groupedRealizationMap G val x) :=
    fun x => measurable_of_finite _
  have h := hgroup.comp (groupedRealizationMap G val) hmaps
  simpa only [Function.comp_def, groupedRealizationMap_restrict] using h

variable [∀ i, MeasurableSpace (val i)]

/-- The structural model with independent inputs that realizes the given
distributions of the district profiles. -/
noncomputable def probabilityModelOfProfiles (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) : ProbabilityModel G val where
  model := profileSCM G val
  sample := RealizationSample G val
  sampleSpace := inferInstance
  inputSpaces := fun _ => ⊤
  measure := realizationMeasure G val q hq
  probability := realizationMeasure_probability G val q hq
  inputs := realizationInputs G val
  measurableInputs := fun _ => measurable_of_finite _
  independent := realizationInputs_independent G val q hq
  measurableMechanisms := by
    intro i pa
    exact measurable_of_finite _

/-- The observed distribution of `probabilityModelOfProfiles` is
`sourceObserved`. -/
theorem probabilityModelOfProfiles_observed (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) :
    (probabilityModelOfProfiles G val q hq).observed = sourceObserved G val q := by
  classical
  change MeasureFinite.law (realizationMeasure G val q hq)
    (fun r => Canonicalization.evalInputs (profileSCM G val)
      (fun x => realizationInputs G val x r)) = _
  unfold realizationMeasure
  rw [MeasureFinite.law_measureOfLaw_eval]
  exact (sourceObserved_eq_profileSCM G val q).symm

end MeraConstraints.HiddenGraph
