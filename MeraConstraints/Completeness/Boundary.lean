import MeraConstraints.GlobalModel.BoundaryCompletion
import MeraConstraints.CompactDistrict
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.MeasureRealization

/-!
# Boundary completeness in the original hidden-variable model

Remark `rmk:positivity` is expressed here using the manuscript's compact
district/external-parent rows. A completion satisfies the district H-system
and agrees with every known observed row; first-undefined rows impose no
equation. Full-assignment indexing appears only when specifying which compact
row an observed assignment determines, via the proved projection map.

The finite-profile boundary reconstruction theorem gives simplex witnesses
from these completions. At c-degree at most one the original-graph realization
constructs an actual measurable SCM probability model with independent original
inputs. Conversely, an arbitrary original probability model, whose latent
state spaces may be infinite or continuous, is canonically reduced to finite
independent profile laws. Necessity includes zero-probability observations.

Thus the final equivalence has original probability models on its left side,
and the ordered Markov equations plus compact H-completions on its right. The
H-system's exactness is still a checked input; no numerical V-to-H conversion
or particular R implementation is trusted.
-/

namespace MeraConstraints.Completeness.Boundary

open HiddenGraph BoundaryCompletion

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The district H-system is completed only at rows whose observed value is
known. Multiple full assignments projecting to the same compact row merely
give redundant copies of its agreement requirement. -/
def CompactHCompletion {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) : Prop :=
  ∀ d, ∃ f : CompactDistrict.Row G.observed val (observedDistrict G) d → ℝ,
    ((∀ i, ∑ x, (H d).inequalities i x * f x ≤ (H d).upper i) ∧
      (∀ e, ∑ x, (H d).equalities e x * f x = (H d).target e)) ∧
    ∀ w, Known G.observed val (observedDistrict G) p d w →
      f (CompactDistrict.project G.observed val (observedDistrict G) d w) =
        knownValue G.observed val (observedDistrict G) p d w

theorem feasibleKnownRows_iff_compact_HCompletion {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) :
    FeasibleKnownRows G.observed val (observedDistrict G) p ↔ CompactHCompletion G val H p := by
  constructor
  · intro h d
    obtain ⟨qd, hqd, hmatch⟩ := h d
    refine ⟨(CompactDistrict.matrix G.observed val (observedDistrict G) d).mulVec qd,
      ((H d).exact_representation _).mp ⟨qd, hqd, rfl⟩, ?_⟩
    intro w hw
    rw [CompactDistrict.mulVec_project]
    exact hmatch w hw
  · intro h d
    obtain ⟨f, hH, hmatch⟩ := h d
    obtain ⟨qd, hqd, heq⟩ := ((H d).exact_representation f).mpr hH
    refine ⟨qd, hqd, ?_⟩
    intro w hw
    rw [← CompactDistrict.mulVec_project, heq]
    exact hmatch w hw

/-- Exact compact-row boundary characterization of the finite profile model. -/
theorem finite_profile_iff_compact_HCompletion {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    (∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
        GlobalModel.observed G.observed val (observedDistrict G) q = p) ↔
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p ∧ CompactHCompletion G val H p := by
  rw [finite_profile_iff_known_rows G.observed val (observedDistrict G) p hp,
    feasibleKnownRows_iff_compact_HCompletion G val H p]

variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- Canonical profile witnesses derived from an actual original probability
model, with no positivity assumption and no finite original-input restriction. -/
theorem probabilityModel_profile_witness (P : ProbabilityModel G val) :
    ∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
        GlobalModel.observed G.observed val (observedDistrict G) q = P.observed := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  letI := P.probability
  have hLocal := Measurability.localProfile_measurable P.model P.measurableMechanisms
  exact ⟨MeasureCanonicalization.canonicalLaw P.model P.measure P.inputs,
    MeasureCanonicalization.canonicalLaw_mem_stdSimplex P.model P.measure P.inputs P.measurableInputs hLocal,
    (MeasureCanonicalization.observedLaw_eq_globalModel P.model P.measure P.inputs
      P.measurableInputs P.independent hLocal).symm⟩

variable [∀ i, Nonempty (val i)]

/-- Full boundary version of the original marginal-model completeness theorem.
Known zero rows and fully defined rows are fixed by the observed law; precisely
first-undefined rows are free in the checked compact H-completion. -/
theorem original_model_iff_boundary_compact_HCompletion
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p ∧ CompactHCompletion G val H p := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨q, hq, hobs⟩ := probabilityModel_profile_witness G val P
    exact (finite_profile_iff_compact_HCompletion G val H p hp).mp ⟨q, hq, hobs.trans hP⟩
  · intro hc
    obtain ⟨q, hq, hobs⟩ := (finite_profile_iff_compact_HCompletion G val H p hp).mpr hc
    exact ⟨probabilityModelOfProfiles G val q hq,
      (probabilityModelOfProfiles_observed G val q hq).trans
        ((sourceObserved_eq_observed G val hdegree q).trans hobs)⟩

end MeraConstraints.Completeness.Boundary
