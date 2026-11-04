import MeraConstraints.HiddenGraph.MoralSeparation

/-!
# An ancestral sink is separated from vertices outside its blanket

This supplies the graphical direction needed when a probability law is
assumed globally Markov, rather than constructed from district kernels.
For an observed ancestral set `A` and its sink `i`, the other retained
district members and their external parents separate `i` from all remaining
vertices of `A` in the original hidden DAG's ancestral moral graph.

The cut labels original districts, including latent roots. Any unconditioned
observed vertex in `i`'s district must be `i` itself. Since `i` is a sink,
an allowed observed parent cannot lie in that district. A latent parent
shares its child's district. These facts prove cut invariance on both
parent-child edges and moral co-parent edges. No independence assumption
or desired local equation is part of this graph proof.

The separation with the original district blanket holds without a c-degree
bound. The degree-one bound is used later to identify it with the actual
induced blanket appearing in `AncestralLocalMarkov`.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) [DecidableEq (DistrictId G)]

def districtSide (i : Fin n) (x : Vertex (n := n) (ℓ := ℓ)) : Bool :=
  if districtOf G x = observedDistrict G i then false else true

theorem allowed_parent_district_iff (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (x : Vertex (n := n) (ℓ := ℓ))
    (hx : MoralAllowed G A (ancestralBlanket G A i) x)
    (c : Fin n) (hc : c ∈ A) (hp : FullParent G x c) :
    districtOf G x = observedDistrict G i ↔ observedDistrict G c = observedDistrict G i := by
  cases x with
  | inl j =>
    have hjA : j ∈ A := hx.1
    have hjB : j ∉ ancestralBlanket G A i := hx.2
    have hjd : observedDistrict G j ≠ observedDistrict G i := by
      intro he
      by_cases hji : j = i
      · exact hs.2 c hc (hji ▸ hp)
      · exact hjB (member_mem_ancestralBlanket G A i j hjA hji he)
    have hcd : observedDistrict G c ≠ observedDistrict G i := by
      intro he
      exact hjB (parent_mem_ancestralBlanket G A hA i c j hc he hp hjd)
    exact iff_of_false hjd hcd
  | inr u =>
    have he : districtOf G (.inr u) = observedDistrict G c :=
      (districtOf_eq_iff G _ _).mpr (connected_child G u c hp)
    rw [he]

theorem ancestral_blanket_moralCut (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) :
    MoralCut G A (ancestralBlanket G A i) (districtSide G i) := by
  intro x y hx hy hrel
  have heq : (districtOf G x = observedDistrict G i) ↔
      (districtOf G y = observedDistrict G i) := by
    rcases hrel with ⟨c, hc, hxc, hp⟩ | ⟨c, hc, hyc, hp⟩ | ⟨c, hc, hpx, hpy⟩
    · rw [hxc]
      exact (allowed_parent_district_iff G A hA i hs y hy c hc hp).symm
    · rw [hyc]
      exact allowed_parent_district_iff G A hA i hs x hx c hc hp
    · exact (allowed_parent_district_iff G A hA i hs x hx c hc hpx).trans
        (allowed_parent_district_iff G A hA i hs y hy c hc hpy).symm
  simp only [districtSide, propext heq]

omit [DecidableEq (DistrictId G)] in
theorem moralVertex_mono {A B : Finset (Fin n)} (hAB : A ⊆ B)
    (x : Vertex (n := n) (ℓ := ℓ)) (hx : MoralVertex G A x) : MoralVertex G B x := by
  cases x with
  | inl i => exact hAB hx
  | inr u => obtain ⟨i, hi, hiu⟩ := hx; exact ⟨i, hAB hi, hiu⟩

omit [DecidableEq (DistrictId G)] in
theorem moralRelated_mono {A B : Finset (Fin n)} (hAB : A ⊆ B)
    {x y : Vertex (n := n) (ℓ := ℓ)} (h : MoralRelated G A x y) : MoralRelated G B x y := by
  rcases h with ⟨c, hc, hx, hp⟩ | ⟨c, hc, hy, hp⟩ | ⟨c, hc, hpx, hpy⟩
  · exact Or.inl ⟨c, hAB hc, hx, hp⟩
  · exact Or.inr (Or.inl ⟨c, hAB hc, hy, hp⟩)
  · exact Or.inr (Or.inr ⟨c, hAB hc, hpx, hpy⟩)

omit [DecidableEq (DistrictId G)] in
theorem moralCut_mono {A B : Finset (Fin n)} (hAB : A ⊆ B) (Z : Finset (Fin n))
    (side : Vertex (n := n) (ℓ := ℓ) → Bool) (hcut : MoralCut G B Z side) : MoralCut G A Z side :=
  fun x y hx hy hxy => hcut x y ⟨moralVertex_mono G hAB x hx.1, hx.2⟩
    ⟨moralVertex_mono G hAB y hy.1, hy.2⟩ (moralRelated_mono G hAB hxy)

omit [DecidableEq (DistrictId G)] in
theorem observedAncestors_subset_ancestral (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (S : Finset (Fin n)) (hSA : S ⊆ A) : observedAncestors G S ⊆ A := by
  intro j hj
  obtain ⟨k, hk, hjk⟩ := (mem_observedAncestors G S j).mp hj
  exact hA k (hSA hk) j hjk

/-- Graphical local Markov separation, before any probability law is used. -/
theorem ancestral_sink_blanket_separated (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) :
    MoralSeparated G {i} ((A.erase i) \ ancestralBlanket G A i) (ancestralBlanket G A i) := by
  classical
  let B := ancestralBlanket G A i
  let Y := (A.erase i) \ B
  have hBA : B ⊆ A := fun j hj => (Finset.mem_erase.mp (ancestralBlanket_subset_erase G A i hj)).2
  have hYA : Y ⊆ A := fun j hj => (Finset.mem_erase.mp (Finset.mem_sdiff.mp hj).1).2
  have hSA : ({i} ∪ Y ∪ B) ⊆ A := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hjB
    · rcases Finset.mem_union.mp hj with hji | hjY
      · have he := Finset.mem_singleton.mp hji
        simpa only [he] using hs.1
      · exact hYA hjY
    · exact hBA hjB
  refine moralSeparated_of_cut G {i} Y B ?_ ?_ ?_ (districtSide G i) ?_ ?_ ?_
  · apply Finset.disjoint_left.mpr
    intro j hjI hjY
    have hji := Finset.mem_singleton.mp hjI
    have hne := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hjY).1).1
    exact hne hji
  · apply Finset.disjoint_left.mpr
    intro j hjI hjB
    exact (Finset.mem_erase.mp (ancestralBlanket_subset_erase G A i hjB)).1 (Finset.mem_singleton.mp hjI)
  · exact Finset.disjoint_left.mpr (fun j hjY hjB => (Finset.mem_sdiff.mp hjY).2 hjB)
  · intro j hj
    have he := Finset.mem_singleton.mp hj
    subst j
    simp [districtSide, observedDistrict]
  · intro j hj
    obtain ⟨hjR, hjB⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hjR
    have hjd : observedDistrict G j ≠ observedDistrict G i :=
      fun he => hjB (member_mem_ancestralBlanket G A i j hjA hji he)
    exact if_neg hjd
  · exact moralCut_mono G (observedAncestors_subset_ancestral G A hA _ hSA) B
      (districtSide G i) (ancestral_blanket_moralCut G A hA i hs)

end MeraConstraints.HiddenGraph
