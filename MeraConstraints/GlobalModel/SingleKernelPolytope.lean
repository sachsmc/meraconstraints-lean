import MeraConstraints.GlobalModel.SingleKernel
import MeraConstraints.CompactDistrict.PositiveReference

/-!
# A realization with the other districts in their polytopes

This is the form of Step 2 of the proof of Proposition 4 (`prop:nontrivial`) used for
the witness in Step 4, at c-degree at most 1. The selected positive vector `q` for
district `d` need only satisfy (N) and (O). Every other district receives the average
of the columns of its matrix `B`, which is positive and lies in its district polytope.
The reconstruction gives a strictly positive distribution satisfying `GlobalMarkov`
whose district factor is `q` for `d` and lies in the district polytope for every other
district (`realize_single_kernel_other_polytopes`). It therefore satisfies the
H-representation constraints of the other districts, though `q` need not.
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
      GlobalMarkov G val p ∧
      districtFactor G.observed val (observedDistrict G) d p = q ∧
      ∀ e, e ≠ d → districtFactor G.observed val (observedDistrict G) e p ∈
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
  have hcompact (e : DistrictId G) : districtFactor G.observed val (observedDistrict G) e p = K e := by
    funext x
    let w := extend G.observed val (observedDistrict G) e x
    have hw := project_extend G.observed val (observedDistrict G) e x
    have h := hfactor e w
    rw [hw] at h
    have hc := districtFactor_project G.observed val (observedDistrict G) e p w
    rw [hw] at hc
    exact hc.trans h
  refine ⟨p, hp, hpos, hGlobal, (hcompact d).trans hKd, ?_⟩
  intro e he
  rw [hcompact, show K e = positiveReference G val e from dif_neg he]
  exact positiveReference_mem_mixture G val e

end MeraConstraints.GlobalModel.KernelReconstruction
