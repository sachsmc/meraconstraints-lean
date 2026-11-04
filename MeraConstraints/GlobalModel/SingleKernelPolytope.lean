import MeraConstraints.GlobalModel.SingleKernel
import MeraConstraints.CompactDistrict.PositiveReference

/-!
# A graphical realization preserving every other district polytope

This is the stronger form of Appendix `prop:nontrivial`, Step 2, needed for
the facet witness. The selected positive kernel need only satisfy (N)/(O).
Every other district receives the positive average of its response columns.
Global kernel reconstruction recovers all these compact factors exactly.
Thus every other factor belongs to its actual district polytope and satisfies
every checked H-representation, without placing the selected factor there.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open HiddenGraph CompactDistrict CompactDistrict.OrderingConstraints

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)]

theorem realize_single_kernel_other_polytopes (hdegree : ∀ x, cDegree G x ≤ 1)
    (d : DistrictId G) (q : CompactRow G val d → ℝ) (hq : ∀ x, 0 < q x)
    (hNO : EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) q) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      MoralGlobalMarkov G val p ∧
      observableFactor G.observed val (observedDistrict G) d p = q ∧
      ∀ e, e ≠ d → observableFactor G.observed val (observedDistrict G) e p ∈
        Polytope.mixture (CompactDistrict.matrix G.observed val (observedDistrict G) e) := by
  classical
  let K : Kernels G val := fun e => if he : e = d then he.symm ▸ q else positiveReference G val e
  have hKd : K d = q := by simp [K]
  have hKNO : NormalizedOrdered G val K := by
    intro e
    by_cases he : e = d
    · subst e
      simpa only [hKd] using hNO
    · simpa only [K, dif_neg he] using positiveReference_constraints G val e
  have hKpos : Positive G val K := by
    intro e x
    by_cases he : e = d
    · subst e
      simpa only [hKd] using hq x
    · simpa only [K, dif_neg he] using positiveReference_pos G val e x
  obtain ⟨p, hp, hpos, hGlobal, hfactor⟩ :=
    reconstruct_positive_kernels_global G val K hKNO hKpos hdegree
  have hcompact (e : DistrictId G) : observableFactor G.observed val (observedDistrict G) e p = K e := by
    funext x
    let w := extend G.observed val (observedDistrict G) e x
    have hw := project_extend G.observed val (observedDistrict G) e x
    have h := hfactor e w
    rw [hw] at h
    have hc := observableFactor_project G.observed val (observedDistrict G) e p w
    rw [hw] at hc
    exact hc.trans h
  refine ⟨p, hp, hpos, hGlobal, (hcompact d).trans hKd, ?_⟩
  intro e he
  rw [hcompact, show K e = positiveReference G val e from dif_neg he]
  exact positiveReference_mem_mixture G val e

end MeraConstraints.GlobalModel.KernelReconstruction
