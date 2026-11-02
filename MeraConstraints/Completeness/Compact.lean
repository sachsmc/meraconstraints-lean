import MeraConstraints.Completeness
import MeraConstraints.CompactDistrict.Observable

/-!
# Completeness with the manuscript's compact district rows

The original finite-source equivalence used a full observed assignment as a
row index. The paper instead uses just `(v₁,v₂)`: a district's members and
its external observed parents. The compact chapter proves that these are
exactly the relevant coordinates, and that compact feasibility is equivalent
to full-row feasibility for the observable factor.

Here a checked H-system is supplied on those compact rows. There is no need
to compute an H-system on duplicated full rows, and no unproved identification
of the two row types is assumed. The equivalence remains the canonical finite
source model; original-SCM canonicalization supplies its necessity bridge.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

/-- Positive canonical finite-source equivalence with actual compact district
H-matrices. The row projection and its surjectivity were proved separately. -/
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
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d p x ≤
            (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d p x =
            (H d).target e) := by
  constructor
  · rintro ⟨q, hq, hobs⟩
    have hc := (Identification.finite_profile_iff_constraints G.observed val
      (observedDistrict G) p hp hpos).mp
      ⟨q, hq, (sourceObserved_eq_observed G val hdegree q).symm.trans hobs⟩
    refine ⟨hc.1, fun d => ?_⟩
    exact (CompactDistrict.observableFactor_mem_mixture_iff_HRep
      G.observed val (observedDistrict G) d (H d) p).mp (hc.2 d)
  · rintro ⟨hMarkov, hH⟩
    apply realize_of_orderedMarkov_and_factor_feasible G val hdegree p hp hpos hMarkov
    intro d
    exact (CompactDistrict.observableFactor_mem_mixture_iff_HRep
      G.observed val (observedDistrict G) d (H d) p).mpr (hH d)

end MeraConstraints.Completeness
