import MeraConstraints.GlobalModel.MoralMarkov
import MeraConstraints.Completeness.Boundary

/-!
# Graphical independencies of actual original probability models

The graph-cut theorem applies also to district kernels induced by independent
finite profiles. Actual original measurable SCMs have such profile laws by
the proved canonicalization of their original mutually independent inputs.
Consequently every actual original model at c-degree at most one satisfies
the global ancestral-moral Markov predicate, including boundary laws.

No finite original latent-state assumption or observed positivity is used.
The predicate is the graph-defined one in `MoralSeparation`; no Markov
assumption is added to the original `ProbabilityModel` bundle.
-/

namespace MeraConstraints.Completeness

open HiddenGraph GlobalModel.KernelReconstruction

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem finite_profiles_moralGlobalMarkov (hdegree : ∀ x, cDegree G x ≤ 1)
    (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) :
    MoralGlobalMarkov G val (GlobalModel.observed G.observed val (observedDistrict G) q) := by
  classical
  let K : Kernels G val := fun d =>
    (CompactDistrict.matrix G.observed val (observedDistrict G) d).mulVec (q d)
  have hNO : NormalizedOrdered G val K := by
    intro d
    exact CompactDistrict.OrderingConstraints.constraints_of_mixture G val d _ ⟨q d, hq d, rfl⟩
  have hobs : joint G val K = GlobalModel.observed G.observed val (observedDistrict G) q := by
    funext w
    rw [GlobalModel.observed_eq_prod_factor]
    apply Finset.prod_congr rfl
    intro d _
    change (CompactDistrict.matrix G.observed val (observedDistrict G) d).mulVec (q d)
      (CompactDistrict.project G.observed val (observedDistrict G) d w) = _
    rw [CompactDistrict.mulVec_project, GlobalModel.factor_eq_mulVec]
  rw [← hobs]
  exact joint_moralGlobalMarkov G val K hNO hdegree

variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- Original-model global graphical necessity, including zero observed
probabilities and arbitrary measurable original latent inputs. -/
theorem probabilityModel_moralGlobalMarkov (hdegree : ∀ x, cDegree G x ≤ 1)
    (P : ProbabilityModel G val) : MoralGlobalMarkov G val P.observed := by
  obtain ⟨q, hq, hobs⟩ := Boundary.probabilityModel_profile_witness G val P
  rw [← hobs]
  exact finite_profiles_moralGlobalMarkov G val hdegree q hq

end MeraConstraints.Completeness
