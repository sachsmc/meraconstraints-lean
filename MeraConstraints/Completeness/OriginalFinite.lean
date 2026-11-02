import MeraConstraints.Completeness.Compact
import MeraConstraints.HiddenGraph.Canonicalization

/-!
# Constraints of every finite-input original SCM

Previously the canonical model was realized by an original-graph SCM, but an
arbitrary original SCM had not been reduced back to that model. The finite
canonicalization chapter now constructs each district law by pushing forward
the **given** independent original input laws through the **given** mechanisms.

We use that proved distributional identity to derive the ordered Markov and
compact H-constraints for every original SCM with finite independent inputs.
No freedom of the induced profile laws is assumed. Necessity consequently
holds at every c-degree; sufficiency of arbitrary district laws remains
specific to graphs whose district c-degrees are at most one.

The measure-theoretic extension removes the finite-input assumption in a
separate chapter. Exactness of any H-system is always a proof input, not an
unchecked output of the R conversion routine.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

universe u v w

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [∀ j, Fintype (M.latentValue j)] [∀ i, Fintype (M.privateNoise i)]
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

/-- Every finite-input original SCM satisfies the manuscript's compact district
constraints and the ordered Markov equations under strict observed positivity. -/
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
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d
            (Canonicalization.observedLaw M μ) x ≤ (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d
            (Canonicalization.observedLaw M μ) x = (H d).target e) := by
  have hc := (Identification.finite_profile_iff_constraints G.observed val
    (observedDistrict G) (Canonicalization.observedLaw M μ)
    (Canonicalization.observedLaw_mem_stdSimplex M μ hμ) hpos).mp
    ⟨Canonicalization.canonicalLaw M μ,
      Canonicalization.canonicalLaw_mem_stdSimplex M μ hμ,
      (Canonicalization.observedLaw_eq_globalModel M μ).symm⟩
  refine ⟨hc.1, fun d => ?_⟩
  exact (CompactDistrict.observableFactor_mem_mixture_iff_HRep
    G.observed val (observedDistrict G) d (H d) _).mp (hc.2 d)

end MeraConstraints.Completeness
