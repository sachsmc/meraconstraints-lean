import MeraConstraints.HiddenGraph

/-!
# Merging the unobserved variables of each district

Remark 4 (`prop:merge`) replaces all the unobserved variables of a district by a
single unobserved parent of all its members. This file constructs the graph
`mergedGraph G` that results, and shows that it satisfies Conditions 1 and 2, has
c-degree at most one (`mergedGraph_graphCDegree_le_one`), and has the same
partition of the observed variables into districts (`districtEquiv`).

There is one new unobserved variable for each district of `G` that contains an
unobserved variable. Its children are the observed members of that district.
It has at least two children, because it has the children of an unobserved
variable of `G`, and distinct new child sets are disjoint, which gives the
antichain part of Condition 2. Observed arrows are unchanged. An observed
variable with no unobserved parent stays in a district by itself.

Only the graph is treated here. The inclusion of the marginal model of the
original graph in that of the merged graph, `𝓜(𝒢') ⊆ 𝓜(𝒢)` in the remark's
notation, is proved in `Completeness/Merging.lean`.
-/

namespace MeraConstraints.HiddenGraph.Merging

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ)

/-- The districts of `G` that contain an unobserved variable. -/
abbrev Root := {d : DistrictId G // ∃ j : Fin ℓ, districtOf G (.inr j) = d}

noncomputable instance : Fintype (Root G) := by
  classical
  exact Fintype.ofFinite _

/-- A numbering of the new unobserved variables by `Fin`. -/
noncomputable def rootEquiv : Fin (Fintype.card (Root G)) ≃ Root G :=
  (Fintype.equivFin (Root G)).symm

noncomputable def mergedChildren (j : Fin (Fintype.card (Root G))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => observedDistrict G i = (rootEquiv G j).val

@[simp] theorem mem_mergedChildren (j : Fin (Fintype.card (Root G))) (i : Fin n) :
    i ∈ mergedChildren G j ↔ observedDistrict G i = (rootEquiv G j).val := by
  classical
  simp [mergedChildren]

theorem mergedChildren_two_le_card (j : Fin (Fintype.card (Root G))) :
    2 ≤ (mergedChildren G j).card := by
  classical
  obtain ⟨k, hk⟩ := (rootEquiv G j).property
  have hsub : G.children k ⊆ mergedChildren G j := by
    intro i hi
    apply (mem_mergedChildren G j i).2
    exact ((districtOf_eq_iff G _ _).2 (connected_child G k i hi)).symm.trans hk
  exact (G.two_le_card k).trans (Finset.card_le_card hsub)

theorem mergedChildren_antichain (j k : Fin (Fintype.card (Root G)))
    (hsub : mergedChildren G j ⊆ mergedChildren G k) : j = k := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.1
    (lt_of_lt_of_le (by decide : 0 < 2) (mergedChildren_two_le_card G j))
  apply (rootEquiv G).injective
  apply Subtype.ext
  exact ((mem_mergedChildren G j i).1 hi).symm.trans
    ((mem_mergedChildren G k i).1 (hsub hi))

/-- The graph with the unobserved variables of each district merged into one. -/
noncomputable def mergedGraph : HiddenGraph.Graph n (Fintype.card (Root G)) where
  observed := G.observed
  children := mergedChildren G
  two_le_card := mergedChildren_two_le_card G
  child_antichain := mergedChildren_antichain G

@[simp] theorem mergedGraph_observed : (mergedGraph G).observed = G.observed := rfl

/-- The new unobserved variable into which an unobserved variable of `G` is
merged. -/
noncomputable def mergedRootFor (j : Fin ℓ) : Fin (Fintype.card (Root G)) :=
  (rootEquiv G).symm ⟨districtOf G (.inr j), ⟨j, rfl⟩⟩

@[simp] theorem rootEquiv_mergedRootFor (j : Fin ℓ) :
    rootEquiv G (mergedRootFor G j) = ⟨districtOf G (.inr j), ⟨j, rfl⟩⟩ :=
  (rootEquiv G).apply_symm_apply _

theorem original_children_subset (j : Fin ℓ) :
    G.children j ⊆ (mergedGraph G).children (mergedRootFor G j) := by
  intro i hi
  apply (mem_mergedChildren G _ i).2
  rw [rootEquiv_mergedRootFor]
  exact ((districtOf_eq_iff G _ _).2 (connected_child G j i hi)).symm

/-- The children of a new unobserved variable are the union of the children of
the unobserved variables merged into it. -/
theorem mem_mergedChildren_iff_original (j : Fin (Fintype.card (Root G))) (i : Fin n) :
    i ∈ mergedChildren G j ↔
      ∃ k : Fin ℓ, mergedRootFor G k = j ∧ i ∈ G.children k := by
  classical
  constructor
  · intro hi
    have hid := (mem_mergedChildren G j i).1 hi
    obtain ⟨v, hv⟩ := (rootEquiv G j).property
    have hparent : ∃ k, i ∈ G.children k := by
      by_cases hp : ∃ k, i ∈ G.children k
      · exact hp
      · have hconn : Connected G (.inl i) (.inr v) :=
          (districtOf_eq_iff G _ _).1 (hid.trans hv.symm)
        have hbad := connected_observed_eq_of_no_latent_parent G i hp hconn
        cases hbad
    obtain ⟨k, hk⟩ := hparent
    refine ⟨k, ?_, hk⟩
    apply (rootEquiv G).injective
    apply Subtype.ext
    rw [rootEquiv_mergedRootFor]
    exact ((districtOf_eq_iff G _ _).2 (connected_child G k i hk)).trans hid
  · rintro ⟨k, hkj, hi⟩
    have h := original_children_subset G k hi
    change i ∈ mergedChildren G (mergedRootFor G k) at h
    simpa only [hkj] using h

/-- The district of `G` that a vertex of the merged graph belongs to. It does
not change along an arrow from an unobserved variable. -/
noncomputable def owner : Vertex (n := n) (ℓ := Fintype.card (Root G)) → DistrictId G
  | .inl i => observedDistrict G i
  | .inr j => (rootEquiv G j).val

theorem incidence_owner {x y : Vertex (n := n) (ℓ := Fintype.card (Root G))}
    (h : Incidence (mergedGraph G) x y) : owner G x = owner G y := by
  cases x with
  | inl i =>
      cases y with
      | inl k => cases h
      | inr j => exact (mem_mergedChildren G j i).1 h
  | inr j =>
      cases y with
      | inl i => exact ((mem_mergedChildren G j i).1 h).symm
      | inr k => cases h

theorem connected_owner {x y : Vertex (n := n) (ℓ := Fintype.card (Root G))}
    (h : Connected (mergedGraph G) x y) : owner G x = owner G y := by
  induction h with
  | rel _ _ h => exact incidence_owner G h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- Every district of the merged graph has at most one unobserved variable. -/
theorem mergedGraph_cDegree_le_one (x : Vertex (n := n) (ℓ := Fintype.card (Root G))) :
    cDegree (mergedGraph G) x ≤ 1 := by
  classical
  apply Finset.card_le_one.2
  intro j hj k hk
  have h₁ := connected_owner G ((mem_latentMembers (mergedGraph G) x j).1 hj)
  have h₂ := connected_owner G ((mem_latentMembers (mergedGraph G) x k).1 hk)
  exact (rootEquiv G).injective (Subtype.ext (h₁.symm.trans h₂))

theorem mergedGraph_graphCDegree_le_one : graphCDegree (mergedGraph G) ≤ 1 :=
  (graphCDegree_le_iff (mergedGraph G) 1).2 (mergedGraph_cDegree_le_one G)

/-- The district of `G` corresponding to a district of the merged graph. -/
noncomputable def districtToOriginal : DistrictId (mergedGraph G) → DistrictId G :=
  Quotient.lift (owner G) (fun _ _ h => connected_owner G h)

@[simp] theorem districtToOriginal_observed (i : Fin n) :
    districtToOriginal G (observedDistrict (mergedGraph G) i) = observedDistrict G i := rfl

theorem merged_connected_of_original (i j : Fin n)
    (hij : observedDistrict G i = observedDistrict G j) :
    Connected (mergedGraph G) (.inl i) (.inl j) := by
  classical
  by_cases hi : ∃ k, i ∈ G.children k
  · obtain ⟨k, hk⟩ := hi
    have hmi : i ∈ (mergedGraph G).children (mergedRootFor G k) :=
      original_children_subset G k hk
    have hmj : j ∈ (mergedGraph G).children (mergedRootFor G k) := by
      apply (mem_mergedChildren G _ j).2
      rw [rootEquiv_mergedRootFor]
      exact hij.symm.trans ((districtOf_eq_iff G _ _).2 (connected_child G k i hk)).symm
    exact children_same_district (mergedGraph G) _ i j hmi hmj
  · have hconn : Connected G (.inl i) (.inl j) := (districtOf_eq_iff G _ _).1 hij
    have hji : j = i := Sum.inl.inj
      (connected_observed_eq_of_no_latent_parent G i hi hconn)
    subst j
    exact Relation.EqvGen.refl _

/-- Two observed variables are in the same district of the merged graph if and
only if they are in the same district of `G`. -/
theorem observedDistrict_eq_iff (i j : Fin n) :
    observedDistrict (mergedGraph G) i = observedDistrict (mergedGraph G) j ↔
      observedDistrict G i = observedDistrict G j := by
  constructor
  · intro h
    exact congrArg (districtToOriginal G) h
  · intro h
    exact (districtOf_eq_iff (mergedGraph G) _ _).2 (merged_connected_of_original G i j h)

theorem districtToOriginal_bijective : Function.Bijective (districtToOriginal G) := by
  constructor
  · intro d e h
    obtain ⟨i, rfl⟩ := observedDistrict_surjective (mergedGraph G) d
    obtain ⟨j, rfl⟩ := observedDistrict_surjective (mergedGraph G) e
    exact (observedDistrict_eq_iff G i j).2 h
  · intro d
    obtain ⟨i, hi⟩ := observedDistrict_surjective G d
    exact ⟨observedDistrict (mergedGraph G) i, hi⟩

/-- The districts of the merged graph correspond to the districts of `G`. -/
noncomputable def districtEquiv : DistrictId (mergedGraph G) ≃ DistrictId G :=
  Equiv.ofBijective (districtToOriginal G) (districtToOriginal_bijective G)

@[simp] theorem districtEquiv_observed (i : Fin n) :
    districtEquiv G (observedDistrict (mergedGraph G) i) = observedDistrict G i := rfl

end MeraConstraints.HiddenGraph.Merging
