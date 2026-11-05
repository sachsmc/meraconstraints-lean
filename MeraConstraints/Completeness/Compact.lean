import MeraConstraints.Completeness
import MeraConstraints.CompactDistrict.Observable

/-!
# Completeness with the rows `(v₁, v₂)` of the matrix `B`

This is part of the proof of Proposition 3 (`prop:complete`); see
`Completeness.lean` for the route. There the rows of the matrix are complete
observed assignments. The manuscript's matrix `B` has rows `(v₁, v₂)`, the values
of a district's members and external parents. The Lean name `CompactDistrict`
refers to this matrix.

The theorem here is the equivalence for the response function model, with the
H-representation given on the rows `(v₁, v₂)`.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

/-- Proposition 3 (`prop:complete`) for the response function model, with the
H-representation of the matrix `B` with rows `(v₁, v₂)`. -/
theorem finite_source_iff_compact_HRep
    (hdegree : ∀ x, cDegree G x ≤ 1)
    {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ w, 0 < p w) :
    (∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
        sourceObserved G val q = p) ↔
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p ∧
      ∀ d,
        (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d p x ≤
            (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d p x =
            (H d).target e) := by
  constructor
  · rintro ⟨q, hq, hobs⟩
    have hc := (Identification.finite_profile_iff_constraints G.observed val
      (observedDistrict G) p hp hpos).mp
      ⟨q, hq, (sourceObserved_eq_observed G val hdegree q).symm.trans hobs⟩
    refine ⟨hc.1, fun d => ?_⟩
    exact (CompactDistrict.districtFactor_mem_mixture_iff_HRep
      G.observed val (observedDistrict G) d (H d) p).mp (hc.2 d)
  · rintro ⟨hMarkov, hH⟩
    apply realize_of_orderedMarkov_and_factor_feasible G val hdegree p hp hpos hMarkov
    intro d
    exact (CompactDistrict.districtFactor_mem_mixture_iff_HRep
      G.observed val (observedDistrict G) d (H d) p).mpr (hH d)

end MeraConstraints.Completeness
