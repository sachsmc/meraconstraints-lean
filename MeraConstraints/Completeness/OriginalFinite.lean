import MeraConstraints.Completeness.Compact
import MeraConstraints.HiddenGraph.Canonicalization

/-!
# Constraints satisfied by every structural model with finite inputs

This is the necessity half of Proposition 3 (`prop:complete`) for finite inputs;
see `Completeness.lean` for the route. Take a structural model on `G` whose
unobserved inputs are independent and take finitely many values. Pushing the
input distributions forward through the mechanisms gives, for each district, the
distribution of its response function variables, and the observed distribution
is that of the response function model. Hence the observed distribution
satisfies the ordered local Markov property and the H-representation
constraints on the rows `(v₁, v₂)`.

This direction holds at every c-degree. `Completeness/OriginalMeasure.lean`
removes the finiteness of the inputs.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

universe u v w

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [∀ j, Fintype (M.latentValue j)] [∀ i, Fintype (M.privateNoise i)]
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

/-- Necessity in Proposition 3 for a structural model with finite independent
inputs: if the observed distribution is strictly positive, it satisfies the
ordered local Markov property and the H-representation constraints of every
district. -/
theorem original_finite_satisfies_compact_HRep
    (μ : ∀ x, Canonicalization.InputValue M x → ℝ)
    (hμ : ∀ x, μ x ∈ stdSimplex ℝ (Canonicalization.InputValue M x))
    {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (hpos : ∀ z, 0 < Canonicalization.observedLaw M μ z) :
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G)
        (Canonicalization.observedLaw M μ) ∧
      ∀ d,
        (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d
            (Canonicalization.observedLaw M μ) x ≤ (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d
            (Canonicalization.observedLaw M μ) x = (H d).target e) := by
  have hc := (Identification.finite_profile_iff_constraints G.observed val
    (observedDistrict G) (Canonicalization.observedLaw M μ)
    (Canonicalization.observedLaw_mem_stdSimplex M μ hμ) hpos).mp
    ⟨Canonicalization.canonicalLaw M μ,
      Canonicalization.canonicalLaw_mem_stdSimplex M μ hμ,
      (Canonicalization.observedLaw_eq_globalModel M μ).symm⟩
  refine ⟨hc.1, fun d => ?_⟩
  exact (CompactDistrict.districtFactor_mem_mixture_iff_HRep
    G.observed val (observedDistrict G) d (H d) _).mp (hc.2 d)

end MeraConstraints.Completeness
