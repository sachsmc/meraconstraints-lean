import MeraConstraints.HiddenGraph.AncestralSets

/-!
# Districts and Markov blankets after retaining an ancestral set

Retaining observed vertices deletes latent incidences to omitted vertices;
it need not preserve the observed district partition in general. At c-degree
at most one it does: a non-singleton original district has one shared root,
so its retained members remain connected through that same root.

`RetainedDistrictConnected` defines the actual retained connectivity by
chains of shared latent parents, rather than assuming district intersection
is the induced district. The equivalence below proves that correspondence
under the manuscript's degree bound. `ancestralBlanket` then spells out
the other retained district members and their external observed parents.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

def RetainedLatentAdjacent (A : Finset (Fin n)) (i j : Fin n) : Prop :=
  i ∈ A ∧ j ∈ A ∧ ∃ u : Fin ℓ, i ∈ G.children u ∧ j ∈ G.children u

abbrev RetainedDistrictConnected (A : Finset (Fin n)) := Relation.EqvGen (RetainedLatentAdjacent G A)

theorem retainedDistrictConnected_implies_district (A : Finset (Fin n)) (i j : Fin n)
    (h : RetainedDistrictConnected G A i j) : observedDistrict G i = observedDistrict G j := by
  induction h with
  | rel i j hij =>
    obtain ⟨_, _, u, hui, huj⟩ := hij
    exact (districtOf_eq_iff G _ _).mpr (children_same_district G u i j hui huj)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Actual retained latent-incidence connectivity equals original district
membership on retained vertices when every district has at most one root. -/
theorem retainedDistrictConnected_iff (A : Finset (Fin n))
    (hdegree : ∀ x, cDegree G x ≤ 1) (i j : Fin n) (hi : i ∈ A) (hj : j ∈ A) :
    RetainedDistrictConnected G A i j ↔ observedDistrict G i = observedDistrict G j := by
  constructor
  · exact retainedDistrictConnected_implies_district G A i j
  · intro hij
    have hc : Connected G (.inl i) (.inl j) := (districtOf_eq_iff G _ _).mp hij
    by_cases hu : ∃ u, i ∈ G.children u
    · obtain ⟨u, hui⟩ := hu
      have huj : j ∈ G.children u := child_of_cDegree_le_one G u j (hdegree _)
        (Relation.EqvGen.trans _ _ _ (connected_child G u i hui) hc)
      exact Relation.EqvGen.rel _ _ ⟨hi, hj, u, hui, huj⟩
    · have he : j = i := Sum.inl.inj (connected_observed_eq_of_no_latent_parent G i hu hc)
      subst j
      exact Relation.EqvGen.refl _

variable [DecidableEq (DistrictId G)]

/-- The other members of `D_i ∩ A`, together with its external observed
parents. Ancestrality ensures those parents also lie in `A`. -/
def ancestralBlanket (A : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  A.filter (fun j => (j ≠ i ∧ observedDistrict G j = observedDistrict G i) ∨
    (observedDistrict G j ≠ observedDistrict G i ∧
      ∃ l ∈ A, observedDistrict G l = observedDistrict G i ∧ j ∈ G.observed.parents l))

theorem ancestralBlanket_subset_erase (A : Finset (Fin n)) (i : Fin n) :
    ancestralBlanket G A i ⊆ A.erase i := by
  intro j hj
  obtain ⟨hjA, hm | ⟨hne, _⟩⟩ := Finset.mem_filter.mp hj
  · exact Finset.mem_erase.mpr ⟨hm.1, hjA⟩
  · exact Finset.mem_erase.mpr ⟨fun hji => hne (congrArg (observedDistrict G) hji), hjA⟩

theorem member_mem_ancestralBlanket (A : Finset (Fin n)) (i j : Fin n)
    (hjA : j ∈ A) (hji : j ≠ i) (hjd : observedDistrict G j = observedDistrict G i) :
    j ∈ ancestralBlanket G A i := Finset.mem_filter.mpr ⟨hjA, Or.inl ⟨hji, hjd⟩⟩

theorem parent_mem_ancestralBlanket (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i l j : Fin n) (hlA : l ∈ A) (hld : observedDistrict G l = observedDistrict G i)
    (hjl : j ∈ G.observed.parents l) (hjd : observedDistrict G j ≠ observedDistrict G i) :
    j ∈ ancestralBlanket G A i :=
  Finset.mem_filter.mpr ⟨hA l hlA j (observedAncestor_of_parent G hjl),
    Or.inr ⟨hjd, l, hlA, hld, hjl⟩⟩

/-- Markov blanket expressed through actual connectivity in the retained
latent-incidence graph, without assuming district intersection is correct. -/
noncomputable def inducedAncestralBlanket (A : Finset (Fin n)) (i : Fin n) : Finset (Fin n) := by
  classical
  exact A.filter (fun j => (j ≠ i ∧ RetainedDistrictConnected G A i j) ∨
    (¬ RetainedDistrictConnected G A i j ∧
      ∃ l ∈ A, RetainedDistrictConnected G A i l ∧ j ∈ G.observed.parents l))

theorem inducedAncestralBlanket_eq (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A)
    (hdegree : ∀ x, cDegree G x ≤ 1) : inducedAncestralBlanket G A i = ancestralBlanket G A i := by
  classical
  have heq (j : Fin n) (hj : j ∈ A) :
      RetainedDistrictConnected G A i j ↔ observedDistrict G j = observedDistrict G i :=
    (retainedDistrictConnected_iff G A hdegree i j hi hj).trans eq_comm
  ext j
  simp only [inducedAncestralBlanket, ancestralBlanket, Finset.mem_filter]
  constructor
  · rintro ⟨hj, h | h⟩
    · exact ⟨hj, Or.inl ⟨h.1, (heq j hj).mp h.2⟩⟩
    · obtain ⟨hne, l, hl, hconn, hjl⟩ := h
      exact ⟨hj, Or.inr ⟨fun hd => hne ((heq j hj).mpr hd), l, hl, (heq l hl).mp hconn, hjl⟩⟩
  · rintro ⟨hj, h | h⟩
    · exact ⟨hj, Or.inl ⟨h.1, (heq j hj).mpr h.2⟩⟩
    · obtain ⟨hne, l, hl, hld, hjl⟩ := h
      exact ⟨hj, Or.inr ⟨fun hc => hne ((heq j hj).mp hc), l, hl, (heq l hl).mpr hld, hjl⟩⟩

end MeraConstraints.HiddenGraph
