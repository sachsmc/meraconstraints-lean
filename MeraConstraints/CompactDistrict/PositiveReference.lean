import MeraConstraints.CompactDistrict.FacetCriterion

/-!
# A strictly positive point of the district polytope

Steps 2 and 4 of the proof of Proposition 4 (`prop:nontrivial`) use the average of
the columns of the matrix `B`. Here it is `B` applied to the uniform distribution
on profiles. It lies in the district polytope (`positiveReference_mem_mixture`),
satisfies (N) and (O) (`positiveReference_constraints`), and is strictly positive
(`positiveReference_pos`): for each row some profile has every member constant at
its value in that row, so the row has entry `1` in that column.
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
