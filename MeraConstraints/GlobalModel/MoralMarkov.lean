import MeraConstraints.GlobalModel.AncestralKernels
import MeraConstraints.GlobalModel.KernelIdentification
import MeraConstraints.HiddenGraph.MoralSeparation
import MeraConstraints.Probability.CutFactorization

/-!
# Global graphical independencies of the reconstructed law

For arbitrary observed sets `X`, `Y`, `Z`, separation in the original
hidden DAG's ancestral moral graph implies the literal random-vector
conditional-independence equations for the reconstructed joint law.

The proof uses the established ancestral margin factorization directly.
A cut obtained from graph reachability assigns every district factor to
one side: the degree-one graph theorem proves that its family cannot
straddle the cut. Grouping the factors gives `F(L,Z) * H(R,Z)`. Summing
assignment fibers then proves independence. Neither graphical separation
nor the global Markov predicate is defined by the desired kernel equations.

This establishes global Markov sufficiency for the constructed law under
the ancestral-moral specification. It does not prove equivalence between
arbitrary laws satisfying ancestral local equations and global separation,
nor necessity of (N)/(O) for arbitrary graph-compatible laws. Those are
separate directions needed by the equality-triviality argument.
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

/-- An actual cut factorization of the ancestral marginal, with the
dependence of both factors on their respective coordinate sets proved. -/
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

/-- The graph cut yields conditional independence of any observed sets
separated in the original DAG's ancestral moral graph. -/
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

/-- The global predicate quantifies over graph separation and literal
random-vector independence; it has no kernel or local-equation fields. -/
def MoralGlobalMarkov (p : FullAssign val → ℝ) : Prop :=
  ∀ X Y Z : Finset (Fin n), MoralSeparated G X Y Z → CoordinateCI val p X Y Z

theorem joint_moralGlobalMarkov (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hdegree : ∀ x, cDegree G x ≤ 1) : MoralGlobalMarkov G val (joint G val K) :=
  joint_coordinateCI_of_moralSeparated G val K hNO hdegree

variable [∀ i, Nonempty (val i)]

/-- Positive kernel reconstruction with all ancestral-moral graphical
independencies, normalized observed law, and the prescribed district factors. -/
theorem reconstruct_positive_kernels_global (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (hdegree : ∀ x, cDegree G x ≤ 1) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      MoralGlobalMarkov G val p ∧ ∀ d w,
        Reconstruction.observableFactor G.observed val (observedDistrict G) p d w =
          K d (CompactDistrict.project G.observed val (observedDistrict G) d w) :=
  ⟨joint G val K, joint_mem_stdSimplex G val K hNO hK, joint_pos G val K hK,
    joint_moralGlobalMarkov G val K hNO hdegree, joint_observableFactor G val K hNO hK⟩

end MeraConstraints.GlobalModel.KernelReconstruction
