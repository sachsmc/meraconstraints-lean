import MeraConstraints.Completeness.Compact
import MeraConstraints.HiddenGraph.MeasureCanonicalization
import MeraConstraints.HiddenGraph.Measurability

/-!
# Observable constraints for arbitrary original latent probability spaces

The necessity direction of Proposition `prop:complete` must cover original
latent spaces of arbitrary cardinality, including continuous variables. Here
the original root and private inputs are measurable, mutually independent
random variables on an arbitrary probability space. The ordinary measurable
structural mechanisms induce finite response maps; their laws are constructed
from the original probability measure and retain mutual district independence.

Combining the measure canonicalization with the derived finite-model ordered
equations proves every strictly positive original observed law satisfies the
district H-constraints on the manuscript's compact `(v₁,v₂)` rows. There is no
finite/countable assumption on original input states, and no independence or
factorization assumption about response profiles or observed data is added.

This necessity holds at any c-degree. The already proved converse construction
with an explicit original SCM requires c-degree at most one. These results
still take the exactness proof of the chosen H-system as an input; they do not
trust an R or cdd output as a proof of that exactness.
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

/-- Necessity for original SCMs with arbitrary measurable input spaces.
All independence assumptions concern the original roots/private inputs. -/
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
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d
            (MeasureCanonicalization.observedLaw M μ A) x ≤ (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d
            (MeasureCanonicalization.observedLaw M μ A) x = (H d).target e) := by
  have hLocal := Measurability.localProfile_measurable M hMechanisms
  have hc := (Identification.finite_profile_iff_constraints G.observed val
    (observedDistrict G) (MeasureCanonicalization.observedLaw M μ A)
    (MeasureCanonicalization.observedLaw_mem_stdSimplex M μ A hA hInd hLocal) hpos).mp
    ⟨MeasureCanonicalization.canonicalLaw M μ A,
      MeasureCanonicalization.canonicalLaw_mem_stdSimplex M μ A hA hLocal,
      (MeasureCanonicalization.observedLaw_eq_globalModel M μ A hA hInd hLocal).symm⟩
  refine ⟨hc.1, fun d => ?_⟩
  exact (CompactDistrict.observableFactor_mem_mixture_iff_HRep
    G.observed val (observedDistrict G) d (H d) _).mp (hc.2 d)

end MeraConstraints.Completeness
