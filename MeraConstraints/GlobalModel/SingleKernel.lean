import MeraConstraints.GlobalModel.ObservableConstraints

/-!
# Positive solutions of (N) and (O) are district factors

Step 2 of the proof of Proposition 4 (`prop:nontrivial`), for one district `d`, at
c-degree at most 1. Let `q` be a positive vector satisfying (N) and (O). Use `q` as
the kernel of `d` and a uniform kernel for every other district. Then `joint` of
these kernels is a strictly positive distribution satisfying the conditional
independencies implied by the graph (`GlobalMarkov`), and its district factor for `d`
is `q` (`realize_single_positive_kernel`). Conversely, by `observable_constraints` every
such district factor satisfies (N) and (O), so the positive solutions of (N) and (O)
are exactly the positive district factors of such distributions
(`positive_kernel_iff_graphical_image`).

These statements concern distributions satisfying the independencies, not membership
of the marginal model. The vector `q` is not assumed to lie in the district polytope.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open HiddenGraph CompactDistrict.OrderingConstraints
open GlobalModel.OrderingInvariance

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)]

/-- Every positive vector satisfying (N) and (O) is the district factor of a strictly
positive distribution satisfying `GlobalMarkov`. -/
theorem realize_single_positive_kernel (hdegree : ∀ x, cDegree G x ≤ 1)
    (d : DistrictId G) (q : CompactRow G val d → ℝ) (hq : ∀ x, 0 < q x)
    (hNO : EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) q) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      GlobalMarkov G val p ∧
      CompactDistrict.districtFactor G.observed val (observedDistrict G) d p = q := by
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
  have hc := CompactDistrict.districtFactor_project G.observed val (observedDistrict G) d p w
  rw [hw] at hc
  exact hc.trans h

/-- A positive vector satisfies (N) and (O) if and only if it is the district factor of a
strictly positive distribution satisfying `GlobalMarkov`. -/
theorem positive_kernel_iff_graphical_image (hdegree : ∀ x, cDegree G x ≤ 1)
    (d : DistrictId G) (q : CompactRow G val d → ℝ) (hq : ∀ x, 0 < q x) :
    EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) q ↔
      ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
        GlobalMarkov G val p ∧
        CompactDistrict.districtFactor G.observed val (observedDistrict G) d p = q := by
  constructor
  · exact realize_single_positive_kernel G val hdegree d q hq
  · rintro ⟨p, _, hpos, hGlobal, rfl⟩
    exact observable_constraints G val p hpos hGlobal d

end MeraConstraints.GlobalModel.KernelReconstruction
