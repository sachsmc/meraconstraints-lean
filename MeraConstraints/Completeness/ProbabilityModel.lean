import MeraConstraints.Completeness.OriginalMeasure
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.MeasureRealization

/-!
# The marginal model with the ordered local Markov property

This is Proposition 3 (`prop:complete`) for the marginal model, before the
ordered local Markov property is replaced by the graph's conditional
independencies; see `Completeness.lean` for the route. `HiddenGraph.ProbabilityModel` is the
marginal model of the manuscript: a structural model on `G` with measurable
mechanisms and mutually independent unobserved inputs on a probability space.
Its definition mentions no response function variables.

For strictly positive distributions and c-degree at most 1, a distribution is in
the marginal model exactly when it satisfies the ordered local Markov property
and the H-representation constraints on the rows `(v₁, v₂)`. Necessity is
`Completeness/OriginalMeasure.lean`. For sufficiency, the response function
model gives distributions of the response function variables, and these define a
`ProbabilityModel`. Here the conditional independencies are the ordered local
Markov property. `Completeness/Global.lean` replaces it by the conditional
independencies implied by the graph.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]
variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- Every `ProbabilityModel` with a strictly positive observed distribution
satisfies the ordered local Markov property and the H-representation constraints.
The input spaces need not be finite or countable. -/
theorem probabilityModel_satisfies_compact_HRep
    (P : ProbabilityModel G val) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (hpos : ∀ y, 0 < P.observed y) :
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) P.observed ∧
      ∀ d,
        (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d P.observed x ≤
            (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d P.observed x =
            (H d).target e) := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  letI := P.probability
  exact original_measure_satisfies_compact_HRep P.model P.measure P.inputs
    P.measurableInputs P.independent P.measurableMechanisms H hpos

/-- Proposition 3 (`prop:complete`) with the ordered local Markov property: at
c-degree at most 1, a strictly positive `p` is in the marginal model exactly when
it satisfies the ordered local Markov property and the H-representation
constraints of every district. -/
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
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d p x ≤
            (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d p x =
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
