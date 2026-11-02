import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.SCMRealization
import MeraConstraints.Probability.MeasureOfLaw
import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# Probability-space realization of simplex profile witnesses

The earlier realization constructs an original-graph SCM and a product mass
vector on its independent sources. Here we construct a literal probability
model in `HiddenGraph.ProbabilityModel`, with an actual probability measure
and full mutual independence of the **original** latent/private inputs.

The sample space is the finite tuple of source profiles. Its probability
measure has exactly the product masses already used by `sourceObserved`.
To verify original input independence, assign every source coordinate to its
own original graph vertex: a latent source to its latent root, a private
source to its unconfounded observed vertex. Grouping those disjoint coordinates
preserves mutual independence. Each original input is a function of only its
own group; the unused private inputs of confounded vertices are constants.
Empty groups are therefore handled without adding artificial random dependence.

All spaces used for the auxiliary finite sources and original inputs are
discrete. Measurability of inputs and mechanisms follows from their finite
discrete domains. No observed constraint is a field or assumption of the
constructed probability model. Equality of its observed law with the existing
source construction is a theorem about actual SCM evaluation.

The identity with `sourceObserved` does not need c-degree one. The separate
source/district equivalence is what identifies `sourceObserved` with arbitrary
district-profile laws when the graph c-degree is at most one.
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

/-- The source's original graph vertex, used to group sources by independent
original input coordinate rather than merely by district. -/
def realizationSourceVertex : Source G → Vertex (n := n) (ℓ := ℓ)
  | .inl j => .inr j
  | .inr i => .inl i

/-- The actual original latent/private random input, with universe lifts
removed immediately when its structural mechanism is called. -/
noncomputable def realizationInputs (x : Vertex (n := n) (ℓ := ℓ))
    (r : RealizationSample G val) : RealizationInput G val x :=
  match x with
  | .inl i => ULift.up (sourcePrivateInput G val r i)
  | .inr j => ULift.up (sourceLatentInput G val r j)

abbrev GroupedRealizationInput (x : Vertex (n := n) (ℓ := ℓ)) :=
  ∀ s : {s : Source G // realizationSourceVertex G s = x}, SourceProfile G val s

/-- Each original input uses only its own group. A confounded vertex's
unused private input is a constant; its group of source coordinates is empty. -/
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

/-- Product source masses as an actual probability measure. -/
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

/-- Full mutual independence of the original latent/private inputs follows
from disjoint source grouping and local measurable maps. -/
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

/-- A literal original probability-model witness for the simplex source
construction. Its fields contain only mechanisms, original inputs, and a law. -/
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

/-- Actual SCM evaluation under the constructed probability measure has the
previously proved source-simplex observed law. No constraints are assumed. -/
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
