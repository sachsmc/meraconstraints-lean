import MeraConstraints.CompactDistrict.FacetCriterion

/-!
# A positive reference point inside every district polytope

Appendix `prop:nontrivial`, Steps 2 and 4, uses the average of all response
columns. Here it is the compatibility matrix applied to the uniform profile
law. Every coordinate is positive because a constant-output profile covers
that coordinate. Membership is certified by the explicit uniform simplex
weights, so every checked district H-system holds at this reference point.
-/

namespace MeraConstraints.CompactDistrict

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)] (d : HiddenGraph.DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (HiddenGraph.observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (HiddenGraph.observedDistrict G) d
local notation "C" => matrix G.observed val (HiddenGraph.observedDistrict G) d

noncomputable def positiveReference : Rows → ℝ :=
  (matrix G.observed val (HiddenGraph.observedDistrict G) d).mulVec (uniformDist Profiles)

omit [∀ i, Nonempty (val i)] in
theorem column_mem_mixture (r : Profiles) : (fun x => C x r) ∈ Polytope.mixture C := by
  rw [Polytope.mixture_eq_convexHull]
  exact subset_convexHull ℝ _ ⟨r, rfl⟩

theorem positiveReference_mem_mixture : positiveReference G val d ∈ Polytope.mixture C :=
  ⟨uniformDist Profiles, uniformDist_mem_stdSimplex Profiles, rfl⟩

theorem positiveReference_pos (x : Rows) : 0 < positiveReference G val d x := by
  classical
  change 0 < ∑ r : Profiles, C x r * uniformDist Profiles r
  apply Finset.sum_pos'
  · intro r _
    exact mul_nonneg (compatibility_nonneg G val d x r) (uniformDist_pos Profiles r).le
  · obtain ⟨r, hr⟩ := compatibility_row_covered G val d x
    exact ⟨r, Finset.mem_univ _, mul_pos hr (uniformDist_pos Profiles r)⟩

theorem positiveReference_constraints :
    EqualityConstraints.Feasible (OrderingConstraints.constraintsMatrix G val d)
      (OrderingConstraints.constraintsRhs G val d) (positiveReference G val d) :=
  OrderingConstraints.constraints_of_mixture G val d _ (positiveReference_mem_mixture G val d)

end MeraConstraints.CompactDistrict
