import MeraConstraints.GlobalModel.AncestralKernels
import MeraConstraints.GlobalModel.KernelIdentification
import MeraConstraints.HiddenGraph.MoralSeparation
import MeraConstraints.Probability.CutFactorization

/-!
# The reconstructed distribution satisfies the conditional independencies

`GlobalMarkov` is the set of conditional independencies implied by the graph,
defined by separation in the ancestral moral graph of the hidden variables DAG:
`X` and `Y` are conditionally independent given `Z` whenever `Z` separates them.
This chapter shows that, at c-degree at most 1, the distribution `joint K` built
from kernels satisfying (N) and (O) satisfies `GlobalMarkov` (`joint_globalMarkov`).
This is the claim in Step 2 of the proof of Proposition 4 (`prop:nontrivial`) that the
constructed distribution satisfies the conditional independencies implied by `𝒢`.

The manuscript obtains it from the ordered local Markov property and a result of
Richardson (2003). Here it is proved directly from equation (`eqn:ancmargin`). A cut
of the moral graph puts each district factor on one side, because at c-degree at most
1 no district's family straddles the cut. Grouping the factors writes the margin as
`F(L, Z) * H(R, Z)`, and summing over assignments gives the independence.

The implication from the ordered local Markov property of an arbitrary distribution to
`GlobalMarkov` is not formalized; see the Scope chapter. Necessity of (N) and (O) for
distributions satisfying `GlobalMarkov` is in `GlobalModel.ObservableConstraints`.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

def cutSide (A Z : Finset (Fin n)) (side : Vertex (n := n) (ℓ := ℓ) → Bool)
    (b : Bool) : Finset (Fin n) := A.filter fun j => j ∉ Z ∧ side (.inl j) = b

theorem cutSide_disjoint (A Z : Finset (Fin n)) (side : Vertex (n := n) (ℓ := ℓ) → Bool) :
    Disjoint (cutSide A Z side false) (cutSide A Z side true) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  have hfalse := (Finset.mem_filter.mp hj).2.2
  have htrue := (Finset.mem_filter.mp hk).2.2
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

theorem cutSide_disjoint_conditioning (A Z : Finset (Fin n))
    (side : Vertex (n := n) (ℓ := ℓ) → Bool) (b : Bool) : Disjoint (cutSide A Z side b) Z := by
  apply Finset.disjoint_left.mpr
  intro j hj hjZ
  exact (Finset.mem_filter.mp hj).2.1 hjZ

theorem cutSide_cover (A Z : Finset (Fin n)) (hZA : Z ⊆ A)
    (side : Vertex (n := n) (ℓ := ℓ) → Bool) :
    cutSide A Z side false ∪ cutSide A Z side true ∪ Z = A := by
  ext j
  simp only [cutSide, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ((⟨hj, _⟩ | ⟨hj, _⟩) | hjZ)
    · exact hj
    · exact hj
    · exact hZA hjZ
  · intro hjA
    by_cases hjZ : j ∈ Z
    · exact Or.inr hjZ
    · cases hb : side (.inl j) with
      | false => exact Or.inl (Or.inl ⟨hjA, hjZ, rfl⟩)
      | true => exact Or.inl (Or.inr ⟨hjA, hjZ, rfl⟩)

/-- A cut of the moral graph splits the margin on `A` into `F * H`, where `F` depends
only on the left side of the cut and the conditioning set `Z`, and `H` only on the right
side and `Z`. -/
theorem ancestral_moral_cut_factorization (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hdegree : ∀ x, cDegree G x ≤ 1) (A Z : Finset (Fin n)) (hA : ObservedAncestral G A)
    (side : Vertex (n := n) (ℓ := ℓ) → Bool) (hcut : MoralCut G A Z side) :
    ∃ F H : FullAssign val → ℝ,
      (∀ w, mass (joint G val K) (assignmentEvent val w A) = F w * H w) ∧
      (∀ w v, (∀ j ∈ cutSide A Z side false ∪ Z, w j = v j) → F w = F v) ∧
      (∀ w v, (∀ j ∈ cutSide A Z side true ∪ Z, w j = v j) → H w = H v) := by
  classical
  let left : DistrictId G → Prop := fun d =>
    ∃ j, KernelFamily G A d j ∧ j ∉ Z ∧ side (.inl j) = false
  let F := fun w : FullAssign val => ∏ d ∈ Finset.univ.filter left, setMargin G val K d A w
  let H := fun w : FullAssign val => ∏ d ∈ Finset.univ.filter (fun d => ¬ left d), setMargin G val K d A w
  have hfamilyL (d : DistrictId G) (hd : left d) (j : Fin n) (hj : KernelFamily G A d j) :
      j ∈ cutSide A Z side false ∪ Z := by
    by_cases hjZ : j ∈ Z
    · exact Finset.mem_union_right _ hjZ
    · obtain ⟨k, hk, hkZ, hkSide⟩ := hd
      have hside := kernelFamily_same_side G A Z hA hdegree side hcut d k j hk hj hkZ hjZ
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨kernelFamily_mem_ancestral G A hA d j hj, hjZ, hside.symm.trans hkSide⟩)
  have hfamilyR (d : DistrictId G) (hd : ¬ left d) (j : Fin n) (hj : KernelFamily G A d j) :
      j ∈ cutSide A Z side true ∪ Z := by
    by_cases hjZ : j ∈ Z
    · exact Finset.mem_union_right _ hjZ
    · have hside : side (.inl j) = true := by
        cases hb : side (.inl j) with
        | false => exact (hd ⟨j, hj, hjZ, hb⟩).elim
        | true => rfl
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨kernelFamily_mem_ancestral G A hA d j hj, hjZ, hside⟩)
  refine ⟨F, H, ?_, ?_, ?_⟩
  · intro w
    rw [joint_ancestral_mass G val K hNO A hA]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ left
      (fun d => setMargin G val K d A w)).symm
  · intro w v hwv
    apply Finset.prod_congr rfl
    intro d hd
    have hd' : left d := (Finset.mem_filter.mp hd).2
    apply setMargin_congr G val K hNO d A hA w v
    · intro j hj hjd
      exact hwv j (hfamilyL d hd' j ⟨j, hj, hjd, Or.inl rfl⟩)
    · intro l hl hld j hjl _
      exact hwv j (hfamilyL d hd' j ⟨l, hl, hld, Or.inr hjl⟩)
  · intro w v hwv
    apply Finset.prod_congr rfl
    intro d hd
    have hd' : ¬ left d := (Finset.mem_filter.mp hd).2
    apply setMargin_congr G val K hNO d A hA w v
    · intro j hj hjd
      exact hwv j (hfamilyR d hd' j ⟨j, hj, hjd, Or.inl rfl⟩)
    · intro l hl hld j hjl _
      exact hwv j (hfamilyR d hd' j ⟨l, hl, hld, Or.inr hjl⟩)

/-- At c-degree at most 1, observed sets separated in the ancestral moral graph are
conditionally independent under `joint K`. -/
theorem joint_coordinateCI_of_moralSeparated (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hdegree : ∀ x, cDegree G x ≤ 1) (X Y Z : Finset (Fin n)) (hsep : MoralSeparated G X Y Z) :
    CoordinateCI val (joint G val K) X Y Z := by
  classical
  let A := observedAncestors G (X ∪ Y ∪ Z)
  have hA : ObservedAncestral G A := observedAncestors_ancestral G _
  have hX : X ⊆ A := fun j hj => subset_observedAncestors G _
    (Finset.mem_union_left _ (Finset.mem_union_left _ hj))
  have hY : Y ⊆ A := fun j hj => subset_observedAncestors G _
    (Finset.mem_union_left _ (Finset.mem_union_right _ hj))
  have hZ : Z ⊆ A := fun j hj => subset_observedAncestors G _ (Finset.mem_union_right _ hj)
  obtain ⟨side, hsX, hsY, hcut⟩ := moralSeparated_cut G X Y Z hsep
  obtain ⟨F, H, hfact, hF, hH⟩ := ancestral_moral_cut_factorization G val K hNO hdegree A Z hA side hcut
  apply coordinateCI_of_cut_factorization val (joint G val K)
    (cutSide A Z side false) (cutSide A Z side true) Z
    (cutSide_disjoint A Z side) (cutSide_disjoint_conditioning A Z side false)
    (cutSide_disjoint_conditioning A Z side true) F H
  · intro w
    rw [cutSide_cover A Z hZ side]
    exact hfact w
  · exact hF
  · exact hH
  · intro j hj
    exact Finset.mem_filter.mpr ⟨hX hj, fun hjZ => Finset.disjoint_left.mp hsep.2.1 hj hjZ, hsX j hj⟩
  · intro j hj
    exact Finset.mem_filter.mpr ⟨hY hj, fun hjZ => Finset.disjoint_left.mp hsep.2.2.1 hj hjZ, hsY j hj⟩

/-- The conditional independencies implied by the graph: whenever `Z` separates `X` and
`Y` in the ancestral moral graph, `X` and `Y` are conditionally independent given `Z`
under `p`. -/
def GlobalMarkov (p : FullAssign val → ℝ) : Prop :=
  ∀ X Y Z : Finset (Fin n), MoralSeparated G X Y Z → CoordinateCI val p X Y Z

theorem joint_globalMarkov (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hdegree : ∀ x, cDegree G x ≤ 1) : GlobalMarkov G val (joint G val K) :=
  joint_coordinateCI_of_moralSeparated G val K hNO hdegree

variable [∀ i, Nonempty (val i)]

/-- At c-degree at most 1, positive kernels satisfying (N) and (O) are the district
factors of a strictly positive distribution satisfying `GlobalMarkov`. -/
theorem reconstruct_positive_kernels_global (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (hdegree : ∀ x, cDegree G x ≤ 1) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      GlobalMarkov G val p ∧ ∀ d w,
        Reconstruction.districtFactor G.observed val (observedDistrict G) p d w =
          K d (CompactDistrict.project G.observed val (observedDistrict G) d w) :=
  ⟨joint G val K, joint_mem_stdSimplex G val K hNO hK, joint_pos G val K hK,
    joint_globalMarkov G val K hNO hdegree, joint_districtFactor G val K hNO hK⟩

end MeraConstraints.GlobalModel.KernelReconstruction
