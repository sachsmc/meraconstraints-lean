import MeraConstraints.GlobalModel.MoralMarkov
import MeraConstraints.Completeness.Boundary

/-!
# Every model satisfies the graph's conditional independencies

At c-degree at most 1, the observed distribution of every `ProbabilityModel`
satisfies `GlobalMarkov`, the conditional independencies implied by the graph.
This is the necessity half of Proposition 3 (`prop:complete`) in its final form;
see `Completeness.lean` for the route. The proof first shows it for the response
function model with independent distributions `q d` of the response function
variables, then applies it to the distributions that a `ProbabilityModel`
induces. The unobserved inputs may be infinite, and `p` may have zero
probabilities. `GlobalMarkov` is defined by separation in the ancestral moral
graph (`HiddenGraph.MoralSeparated`), and `ProbabilityModel` does not assume it.
-/

namespace MeraConstraints.Completeness

open HiddenGraph GlobalModel.KernelReconstruction

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem finite_profiles_globalMarkov (hdegree : ∀ x, cDegree G x ≤ 1)
    (q : ∀ d, DistrictProfile G val d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) :
    GlobalMarkov G val (GlobalModel.observed G.observed val (observedDistrict G) q) := by
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
  exact joint_globalMarkov G val K hNO hdegree

variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- At c-degree at most 1, the observed distribution of a `ProbabilityModel`
satisfies the conditional independencies implied by the graph. -/
theorem probabilityModel_globalMarkov (hdegree : ∀ x, cDegree G x ≤ 1)
    (P : ProbabilityModel G val) : GlobalMarkov G val P.observed := by
  obtain ⟨q, hq, hobs⟩ := Boundary.probabilityModel_profile_witness G val P
  rw [← hobs]
  exact finite_profiles_globalMarkov G val hdegree q hq

end MeraConstraints.Completeness
