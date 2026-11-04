import MeraConstraints.GlobalModel.ObservableConstraints

/-!
# The positive kernel domain is exactly the graphical observed-law image

Appendix `prop:nontrivial`, Step 2, for one selected district. Insert an
arbitrary positive (N)/(O) kernel at that district and the normalized uniform
output kernels at all others. The checked reconstruction gives a positive
normalized globally Markov observed law and recovers the selected compact
observable factor exactly. Conversely, the already proved necessity theorem
puts every such observable factor in the same (N)/(O) solution set.

This theorem concerns graphical compatibility, not hidden-variable model
membership. It makes no polytope assumption on the selected kernel.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open HiddenGraph CompactDistrict.OrderingConstraints
open GlobalModel.OrderingInvariance

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)]

/-- Any one positive (N)/(O) kernel is the actual observable factor of a
positive graph-compatible observed probability law. -/
theorem realize_single_positive_kernel (hdegree : ∀ x, cDegree G x ≤ 1)
    (d : DistrictId G) (q : CompactRow G val d → ℝ) (hq : ∀ x, 0 < q x)
    (hNO : EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) q) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      MoralGlobalMarkov G val p ∧
      CompactDistrict.observableFactor G.observed val (observedDistrict G) d p = q := by
  classical
  let K : Kernels G val := fun e => if he : e = d then he.symm ▸ q else uniformKernel G val e
  have hKd : K d = q := by simp [K]
  have hKNO : NormalizedOrdered G val K := by
    intro e
    by_cases he : e = d
    · subst e
      simpa only [hKd] using hNO
    · simpa only [K, dif_neg he] using uniformKernel_feasible G val e
  have hKpos : Positive G val K := by
    intro e x
    by_cases he : e = d
    · subst e
      simpa only [hKd] using hq x
    · simpa only [K, dif_neg he] using uniformKernel_pos G val e x
  obtain ⟨p, hp, hpos, hGlobal, hfactor⟩ :=
    reconstruct_positive_kernels_global G val K hKNO hKpos hdegree
  refine ⟨p, hp, hpos, hGlobal, ?_⟩
  funext x
  let w := CompactDistrict.extend G.observed val (observedDistrict G) d x
  have hw := CompactDistrict.project_extend G.observed val (observedDistrict G) d x
  have h := hfactor d w
  rw [hKd, hw] at h
  have hc := CompactDistrict.observableFactor_project G.observed val (observedDistrict G) d p w
  rw [hw] at hc
  exact hc.trans h

/-- Exact domain equivalence on positive kernels, with normalized observed
laws and literal compact factor equality on the right. -/
theorem positive_kernel_iff_graphical_image (hdegree : ∀ x, cDegree G x ≤ 1)
    (d : DistrictId G) (q : CompactRow G val d → ℝ) (hq : ∀ x, 0 < q x) :
    EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) q ↔
      ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
        MoralGlobalMarkov G val p ∧
        CompactDistrict.observableFactor G.observed val (observedDistrict G) d p = q := by
  constructor
  · exact realize_single_positive_kernel G val hdegree d q hq
  · rintro ⟨p, _, hpos, hGlobal, rfl⟩
    exact observable_constraints G val p hpos hGlobal d

end MeraConstraints.GlobalModel.KernelReconstruction
