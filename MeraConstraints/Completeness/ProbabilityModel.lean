import MeraConstraints.Completeness.OriginalMeasure
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.MeasureRealization

/-!
# Original marginal-model completeness for checked compact H-systems

The left side of the final equivalence quantifies over original measurable
SCMs and their actual independent-input probability spaces, via
`HiddenGraph.ProbabilityModel`. No response-profile law is assumed to exist
in that definition. Necessity follows by constructing those laws from the
original inputs; sufficiency constructs an explicit original SCM together
with a genuine probability measure and mutually independent original inputs.

For strictly positive observed laws and graphs of c-degree at most one, the
original marginal model is therefore characterized by the derived ordered
conditional-independence equations and the checked district H-constraints.
The latter use exactly the manuscript's compact district/external-parent rows.

This is the content of `prop:complete` with a sufficient ordered set of
conditional-independence equations. It does not enumerate every d-separation
statement, verify an external numerical H-conversion, or claim the boundary
free-entry completion theorem for nonpositive observed laws.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]
variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- An arbitrary original probability model satisfies the compact constraints.
The original input spaces need not be finite or countable. -/
theorem probabilityModel_satisfies_compact_HRep
    (P : ProbabilityModel G val) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (hpos : ∀ y, 0 < P.observed y) :
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) P.observed ∧
      ∀ d,
        (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d P.observed x ≤
            (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d P.observed x =
            (H d).target e) := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  letI := P.probability
  exact original_measure_satisfies_compact_HRep P.model P.measure P.inputs
    P.measurableInputs P.independent P.measurableMechanisms H hpos

/-- The original marginal model equals the positive laws satisfying the
ordered independencies and a checked compact H-representation in every district.
Both original-model directions are proved; canonical profiles are intermediate
constructions, not part of the left-hand model definition. -/
theorem original_model_iff_compact_HRep
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ y, 0 < p y) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p ∧
      ∀ d,
        (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d p x ≤
            (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d p x =
            (H d).target e) := by
  constructor
  · rintro ⟨P, hP⟩
    have hposP : ∀ y, 0 < P.observed y := by simpa [hP] using hpos
    simpa [hP] using probabilityModel_satisfies_compact_HRep G val P H hposP
  · intro hc
    obtain ⟨q, hq, hobs⟩ := (finite_source_iff_compact_HRep G val hdegree H p hp hpos).mpr hc
    exact ⟨probabilityModelOfProfiles G val q hq,
      (probabilityModelOfProfiles_observed G val q hq).trans hobs⟩

end MeraConstraints.Completeness
