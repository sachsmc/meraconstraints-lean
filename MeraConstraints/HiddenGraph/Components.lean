import MeraConstraints.HiddenGraph

/-!
# Independent input sources of c-degree-one graphs

The proof of `prop:complete` chooses one unrestricted profile law per district.
To realize those laws in the original hidden-variable graph, distinct latent
roots must still be independent. A joint profile cannot simply be copied to
several roots in the same district: that would add unallowed dependence at
higher c-degree.

For a graph whose district c-degrees are at most one, each district has exactly
one independent input source. A degree-one district uses its latent root. A
degree-zero district is a single observed vertex and uses that vertex's
private disturbance. We prove that these sources are in bijection with the
actual graph districts. This supplies the independence-preserving reindexing
needed by the response-profile construction.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

def HasLatentParent (i : Fin n) : Prop := ∃ u, i ∈ G.children u

/-- Actual latent roots, plus private inputs of unconfounded singleton vertices.
Private inputs of confounded vertices can be fixed constants in a realization. -/
abbrev Source := Fin ℓ ⊕ {i : Fin n // ¬ HasLatentParent G i}

noncomputable instance : Fintype (Source G) := by
  classical
  exact Fintype.ofFinite _

def sourceDistrict : Source G → DistrictId G
  | .inl u => districtOf G (.inr u)
  | .inr i => observedDistrict G i

/-- Every district has an input source, without any c-degree restriction. -/
theorem sourceDistrict_surjective : Function.Surjective (sourceDistrict G) := by
  classical
  intro d
  obtain ⟨i, rfl⟩ := observedDistrict_surjective G d
  by_cases hi : HasLatentParent G i
  · obtain ⟨u, hu⟩ := hi
    exact ⟨.inl u, (districtOf_eq_iff G _ _).2 (connected_child G u i hu)⟩
  · exact ⟨.inr ⟨i, hi⟩, rfl⟩

/-- If every district has c-degree at most one, no two different independent
sources are assigned to the same district. -/
theorem sourceDistrict_injective
    (hdegree : ∀ x, cDegree G x ≤ 1) : Function.Injective (sourceDistrict G) := by
  classical
  intro a b hab
  cases a with
  | inl u =>
      cases b with
      | inl v =>
          have huv : Connected G (.inr u) (.inr v) := (districtOf_eq_iff G _ _).1 hab
          have hu : u ∈ latentMembers G (.inr u) :=
            (mem_latentMembers G _ _).2 (Relation.EqvGen.refl _)
          have hv : v ∈ latentMembers G (.inr u) := (mem_latentMembers G _ _).2 huv
          have huv' : u = v := Finset.card_le_one.1 (hdegree (.inr u)) u hu v hv
          exact congrArg Sum.inl huv'
      | inr i =>
          have hui : Connected G (.inr u) (.inl i.val) := (districtOf_eq_iff G _ _).1 hab
          exact False.elim (i.property ⟨u, child_of_cDegree_le_one G u i (hdegree _) hui⟩)
  | inr i =>
      cases b with
      | inl u =>
          have hiu : Connected G (.inl i.val) (.inr u) := (districtOf_eq_iff G _ _).1 hab
          have h := connected_observed_eq_of_no_latent_parent G i i.property hiu
          cases h
      | inr j =>
          have hij : Connected G (.inl i.val) (.inl j.val) := (districtOf_eq_iff G _ _).1 hab
          have h := connected_observed_eq_of_no_latent_parent G i i.property hij
          have hji : j.val = i.val := Sum.inl.inj h
          exact congrArg Sum.inr (Subtype.ext hji.symm)

noncomputable def sourceDistrictEquiv (hdegree : ∀ x, cDegree G x ≤ 1) :
    Source G ≃ DistrictId G :=
  Equiv.ofBijective (sourceDistrict G)
    ⟨sourceDistrict_injective G hdegree, sourceDistrict_surjective G⟩

/-- Each observed mechanism may read this source: either one of its listed
latent parents, or its own private disturbance when it has no latent parent. -/
noncomputable def sourceOf (i : Fin n) : Source G := by
  classical
  exact if hi : HasLatentParent G i then .inl (Classical.choose hi) else .inr ⟨i, hi⟩

theorem sourceOf_district (i : Fin n) :
    sourceDistrict G (sourceOf G i) = observedDistrict G i := by
  classical
  unfold sourceOf
  split
  · rename_i hi
    exact (districtOf_eq_iff G _ _).2 (connected_child G _ i (Classical.choose_spec hi))
  · rfl

theorem sourceOf_latent_parent (i : Fin n) (u : Fin ℓ)
    (hi : sourceOf G i = .inl u) : i ∈ G.children u := by
  classical
  unfold sourceOf at hi
  split at hi
  · rename_i hp
    have hu : Classical.choose hp = u := Sum.inl.inj hi
    simpa [hu] using Classical.choose_spec hp
  · cases hi

/-- A private disturbance is read only by its own observed vertex. -/
theorem sourceOf_private_vertex (i : Fin n) (j : {j : Fin n // ¬ HasLatentParent G j})
    (hi : sourceOf G i = .inr j) : i = j.val := by
  classical
  unfold sourceOf at hi
  split at hi
  · cases hi
  · exact congrArg Subtype.val (Sum.inr.inj hi)

end MeraConstraints.HiddenGraph
