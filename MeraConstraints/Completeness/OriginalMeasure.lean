import MeraConstraints.Completeness.Compact
import MeraConstraints.HiddenGraph.MeasureCanonicalization
import MeraConstraints.HiddenGraph.Measurability

/-!
# Constraints satisfied by every structural model

This is the necessity half of Proposition 3 (`prop:complete`) for general
inputs; see `Completeness.lean` for the route. The unobserved inputs may take values in any
measurable space, including continuous ones. They are mutually independent
random variables on a probability space, and the mechanisms are measurable. The
mechanisms induce response functions, and the distribution of the response
function variables of each district is obtained from the probability measure.
These distributions are independent across districts.

So every strictly positive observed distribution of a structural model satisfies
the ordered local Markov property and the H-representation constraints on the
rows `(v₁, v₂)`. This holds at every c-degree. The converse needs c-degree at
most 1.
-/

namespace MeraConstraints.Completeness

open MeasureTheory ProbabilityTheory HiddenGraph

universe u v w z

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]
variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]
variable [∀ x, MeasurableSpace (Canonicalization.InputValue M x)]
variable {Ω : Type z} [MeasurableSpace Ω]

/-- Necessity in Proposition 3 for a structural model with arbitrary measurable
input spaces. The only independence assumption is that the unobserved inputs
are mutually independent. -/
theorem original_measure_satisfies_compact_HRep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ∀ x, Ω → Canonicalization.InputValue M x)
    (hA : ∀ x, Measurable (A x)) (hInd : iIndepFun A μ)
    (hMechanisms : Measurability.MechanismsMeasurable M)
    {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (hpos : ∀ y, 0 < MeasureCanonicalization.observedLaw M μ A y) :
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G)
        (MeasureCanonicalization.observedLaw M μ A) ∧
      ∀ d,
        (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d
            (MeasureCanonicalization.observedLaw M μ A) x ≤ (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d
            (MeasureCanonicalization.observedLaw M μ A) x = (H d).target e) := by
  have hLocal := Measurability.localProfile_measurable M hMechanisms
  have hc := (Identification.finite_profile_iff_constraints G.observed val
    (observedDistrict G) (MeasureCanonicalization.observedLaw M μ A)
    (MeasureCanonicalization.observedLaw_mem_stdSimplex M μ A hA hInd hLocal) hpos).mp
    ⟨MeasureCanonicalization.canonicalLaw M μ A,
      MeasureCanonicalization.canonicalLaw_mem_stdSimplex M μ A hA hLocal,
      (MeasureCanonicalization.observedLaw_eq_globalModel M μ A hA hInd hLocal).symm⟩
  refine ⟨hc.1, fun d => ?_⟩
  exact (CompactDistrict.districtFactor_mem_mixture_iff_HRep
    G.observed val (observedDistrict G) d (H d) _).mp (hc.2 d)

end MeraConstraints.Completeness
