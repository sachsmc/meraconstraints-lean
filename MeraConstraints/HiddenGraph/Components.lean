import MeraConstraints.HiddenGraph

/-!
# One independent input for each district

The proof of Proposition 3 (`prop:complete`) chooses a distribution of the
response function variables for each district. To generate these in the hidden
variables DAG, each district needs one independent input of the graph.

A `Source` is an unobserved variable, or the private noise of an observed
variable with no unobserved parent. If every district has c-degree at most one,
sources are in bijection with districts (`sourceDistrictEquiv`): a district of
c-degree one has its unobserved variable, and a district of c-degree zero is a
single observed variable with its private noise. Without the c-degree
assumption every district still has a source (`sourceDistrict_surjective`).
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

def HasLatentParent (i : Fin n) : Prop := ∃ u, i ∈ G.children u

/-- The unobserved variables, and the private noise of the observed variables
with no unobserved parent. -/
abbrev Source := Fin ℓ ⊕ {i : Fin n // ¬ HasLatentParent G i}

noncomputable instance : Fintype (Source G) := by
  classical
  exact Fintype.ofFinite _

def sourceDistrict : Source G → DistrictId G
  | .inl u => districtOf G (.inr u)
  | .inr i => observedDistrict G i

/-- Every district contains a source, with no assumption on the c-degree. -/
theorem sourceDistrict_surjective : Function.Surjective (sourceDistrict G) := by
  classical
  intro d
  obtain ⟨i, rfl⟩ := observedDistrict_surjective G d
  by_cases hi : HasLatentParent G i
  · obtain ⟨u, hu⟩ := hi
    exact ⟨.inl u, (districtOf_eq_iff G _ _).2 (connected_child G u i hu)⟩
  · exact ⟨.inr ⟨i, hi⟩, rfl⟩

/-- If every district has c-degree at most one, no district contains two
different sources. -/
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

/-- The source that an observed variable reads: one of its unobserved parents,
or its own private noise if it has none. -/
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

/-- A private noise is read only by its own observed variable. -/
theorem sourceOf_private_vertex (i : Fin n) (j : {j : Fin n // ¬ HasLatentParent G j})
    (hi : sourceOf G i = .inr j) : i = j.val := by
  classical
  unfold sourceOf at hi
  split at hi
  · cases hi
  · exact congrArg Subtype.val (Sum.inr.inj hi)

end MeraConstraints.HiddenGraph
