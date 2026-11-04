import MeraConstraints.GlobalModel.KernelReconstruction
import MeraConstraints.HiddenGraph.AncestralSets
import MeraConstraints.Probability.AssignmentPartition

/-!
# The ancestral margin identity for arbitrary district kernels

This chapter proves Appendix equation `eqn:ancmargin`. For every observed
ancestral set `A`, the marginal mass of the explicitly reconstructed joint
law is the product of the ordinary kernel margins on `D ∩ A`.

The kernels satisfy the actual (N)/(O) matrices, not a presumed global
factorization or a response-profile feasibility condition. The proof works
even for signed kernels. Full observed ancestry ensures `D ∩ A` is closed
in the manuscript's sense, so (O) removes dependence on all unused external
parents. Removing an observed sink therefore changes only its own district
margin. Reverse elimination through `A ∪ prefix(k)` proves the identity for
every ancestral set, rather than only one chosen global prefix.

No graphical separation theorem is a hypothesis or conclusion here. The
conditional/local-Markov consequences of the identity are treated separately.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)]
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Matching exactly those members of a district retained in `A`. -/
def SetMatch (d : DistrictId G) (A : Finset (Fin n)) (w : FullAssign val)
    (out : Output G val d) : Prop :=
  ∀ j : CompactDistrict.Member (observedDistrict G) d, j.val ∈ A → out j = w j

/-- The literal margin of one compact kernel over `D \ A`. -/
noncomputable def setMargin (K : Kernels G val) (d : DistrictId G)
    (A : Finset (Fin n)) (w : FullAssign val) : ℝ := by
  classical
  exact ∑ out, if SetMatch G val d A w out then K d (out, fun j => w j) else 0

/-- The margin agrees with the concrete (O) margin on `D ∩ A`. -/
theorem setMargin_eq_closedMargin (K : Kernels G val) (d : DistrictId G)
    (A : Finset (Fin n)) (w : FullAssign val)
    (S : CompactDistrict.OrderingConstraints.ClosedSubset G d)
    (hS : S.val = A.filter (fun j => observedDistrict G j = d)) :
    setMargin G val K d A w = CompactDistrict.OrderingConstraints.margin G val d
      (K d) S (fun j => w j.val) (fun j => w j.val) := by
  classical
  have hm (out : Output G val d) : SetMatch G val d A w out ↔
      CompactDistrict.OrderingConstraints.restrictOutput G val d S out =
        (fun j : {j : Fin n // j ∈ S.val} => w j.val) := by
    constructor
    · intro h
      funext j
      have hjF : j.val ∈ A.filter (fun j => observedDistrict G j = d) := by
        rw [← hS]
        exact j.2
      have hjA : j.val ∈ A := (Finset.mem_filter.mp hjF).1
      exact h ⟨j, S.2.2.1 j j.2⟩ hjA
    · intro h j hjA
      have hjS : j.val ∈ S.val := by rw [hS]; exact Finset.mem_filter.mpr ⟨hjA, j.2⟩
      exact congrFun h ⟨j, hjS⟩
  simp only [setMargin, CompactDistrict.OrderingConstraints.margin,
    CompactDistrict.OrderingConstraints.marginIndicator, hm, ite_mul, one_mul, zero_mul]

/-- A district disjoint from `A` contributes its normalization, namely one. -/
theorem setMargin_eq_one_of_empty (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : DistrictId G) (A : Finset (Fin n)) (w : FullAssign val)
    (he : A.filter (fun j => observedDistrict G j = d) = ∅) : setMargin G val K d A w = 1 := by
  classical
  have hm (out : Output G val d) : SetMatch G val d A w out := by
    intro j hj
    have hmem : j.val ∈ A.filter (fun j => observedDistrict G j = d) :=
      Finset.mem_filter.mpr ⟨hj, j.2⟩
    rw [he] at hmem
    exact False.elim (Finset.notMem_empty _ hmem)
  simp only [setMargin, if_pos (hm _)]
  exact kernel_normalization G val K hNO d _

/-- Precise member/parent dependence supplied by (O) for an ancestral set. -/
theorem setMargin_congr (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : DistrictId G) (A : Finset (Fin n)) (hA : ObservedAncestral G A) (w v : FullAssign val)
    (hm : ∀ j ∈ A, observedDistrict G j = d → w j = v j)
    (hp : ∀ j ∈ A, observedDistrict G j = d →
      ∀ l ∈ G.observed.parents j, observedDistrict G l ≠ d → w l = v l) :
    setMargin G val K d A w = setMargin G val K d A v := by
  classical
  by_cases he : A.filter (fun j => observedDistrict G j = d) = ∅
  · rw [setMargin_eq_one_of_empty G val K hNO d A w he,
      setMargin_eq_one_of_empty G val K hNO d A v he]
  · let S : CompactDistrict.OrderingConstraints.ClosedSubset G d :=
      ⟨A.filter (fun j => observedDistrict G j = d), Finset.nonempty_iff_ne_empty.mpr he,
        ancestral_district_fullClosed G A hA d⟩
    rw [setMargin_eq_closedMargin G val K d A w S rfl,
      setMargin_eq_closedMargin G val K d A v S rfl]
    have ha : (fun j : {j : Fin n // j ∈ S.val} => w j.val) =
        (fun j : {j : Fin n // j ∈ S.val} => v j.val) := by
      funext j
      exact hm j (Finset.mem_filter.mp j.2).1 (Finset.mem_filter.mp j.2).2
    rw [ha]
    apply ((CompactDistrict.OrderingConstraints.feasible_iff G val d (K d)).mp (hNO d)).2
    intro l hl
    obtain ⟨j, hj, hlj⟩ := hl
    exact hp j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2 l hlj l.2.1

theorem setMargin_congr_on_ancestral (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : DistrictId G) (A : Finset (Fin n)) (hA : ObservedAncestral G A) (w v : FullAssign val)
    (hwv : ∀ j ∈ A, w j = v j) : setMargin G val K d A w = setMargin G val K d A v :=
  setMargin_congr G val K hNO d A hA w v (fun j hj _ => hwv j hj)
    (fun j hj _ l hlj _ => hwv l (hA j hj l (observedAncestor_of_parent G hlj)))

omit [∀ i, DecidableEq (val i)] in
theorem setMargin_erase_of_ne (K : Kernels G val) (d : DistrictId G)
    (A : Finset (Fin n)) (i : Fin n) (w : FullAssign val) (hd : d ≠ observedDistrict G i) :
    setMargin G val K d A w = setMargin G val K d (A.erase i) w := by
  classical
  have hm (out : Output G val d) : SetMatch G val d A w out ↔ SetMatch G val d (A.erase i) w out := by
    constructor
    · intro h j hj
      exact h j (Finset.mem_erase.mp hj).2
    · intro h j hj
      have hji : j.val ≠ i := fun he => hd (j.2.symm.trans (congrArg (observedDistrict G) he))
      exact h j (Finset.mem_erase.mpr ⟨hji, hj⟩)
  simp only [setMargin, hm]

/-- Summing the removed member in its own kernel gives the smaller margin. -/
theorem sum_setMargin_member (K : Kernels G val) (A : Finset (Fin n))
    (i : Fin n) (hi : i ∈ A) (w : FullAssign val) :
    (∑ a : val i, setMargin G val K (observedDistrict G i) A (Function.update w i a)) =
      setMargin G val K (observedDistrict G i) (A.erase i) w := by
  classical
  let d := observedDistrict G i
  have hext (a : val i) :
      (fun j : CompactDistrict.ExternalParent G.observed (observedDistrict G) d =>
        Function.update w i a j.val) =
      (fun j : CompactDistrict.ExternalParent G.observed (observedDistrict G) d => w j.val) := by
    funext j
    apply Function.update_of_ne
    exact fun hj => j.2.1 (congrArg (observedDistrict G) hj)
  have hm (a : val i) (out : Output G val d) : SetMatch G val d A (Function.update w i a) out ↔
      SetMatch G val d (A.erase i) w out ∧ out ⟨i, rfl⟩ = a := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro j hj
        obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
        simpa only [Function.update_of_ne hji] using h j hjA
      · simpa using h ⟨i, rfl⟩ hi
    · rintro ⟨h, ha⟩ j hj
      by_cases hji : j.val = i
      · have he : j = (⟨i, rfl⟩ : CompactDistrict.Member (observedDistrict G) d) := Subtype.ext hji
        subst j
        simpa using ha
      · rw [Function.update_of_ne hji]
        exact h j (Finset.mem_erase.mpr ⟨hji, hj⟩)
  change (∑ a : val i, setMargin G val K d A (Function.update w i a)) = _
  simp only [setMargin]
  simp_rw [hext, hm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun out _ => sum_indicator_and_eq _ (out ⟨i, rfl⟩) _

/-- Product of the literal district margins on `D ∩ A`. -/
noncomputable def setJoint (K : Kernels G val) (A : Finset (Fin n)) (w : FullAssign val) : ℝ :=
  ∏ d, setMargin G val K d A w

theorem setJoint_univ (K : Kernels G val) (w : FullAssign val) :
    setJoint G val K Finset.univ w = joint G val K w := by
  classical
  have hm (d : DistrictId G) (out : Output G val d) : SetMatch G val d Finset.univ w out ↔
      out = (fun j : CompactDistrict.Member (observedDistrict G) d => w j.val) := by
    exact ⟨fun h => funext (fun j => h j (Finset.mem_univ _)), fun h j _ => congrFun h j⟩
  simp only [setJoint, setMargin, hm, joint, CompactDistrict.project]
  simp

/-- The one-sink reverse-elimination identity used in `eqn:ancmargin`. -/
theorem sum_setJoint_sink (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (i : Fin n) (hs : ObservedSink G A i)
    (w : FullAssign val) :
    (∑ a : val i, setJoint G val K A (Function.update w i a)) = setJoint G val K (A.erase i) w := by
  classical
  let d := observedDistrict G i
  let rest := ∏ e ∈ Finset.univ.erase d, setMargin G val K e (A.erase i) w
  have hsplit (a : val i) : setJoint G val K A (Function.update w i a) =
      setMargin G val K d A (Function.update w i a) * rest := by
    rw [setJoint, ← Finset.mul_prod_erase Finset.univ
      (fun e => setMargin G val K e A (Function.update w i a)) (Finset.mem_univ d)]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    rw [setMargin_erase_of_ne G val K e A i _ (Finset.ne_of_mem_erase he)]
    apply setMargin_congr_on_ancestral G val K hNO e (A.erase i) (observedAncestral_erase G A hA i hs)
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  simp_rw [hsplit]
  rw [← Finset.sum_mul, sum_setMargin_member G val K A i hs.1]
  exact Finset.mul_prod_erase Finset.univ (fun e => setMargin G val K e (A.erase i) w)
    (Finset.mem_univ d)

/-- Appendix equation `eqn:ancmargin`, for every observed ancestral set.
Neither positivity nor a response-profile representation is required. -/
theorem joint_ancestral_mass (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (w : FullAssign val) :
    mass (joint G val K) (assignmentEvent val w A) = setJoint G val K A w := by
  classical
  have h : ∀ k ≤ n, ∀ w : FullAssign val,
      mass (joint G val K) (assignmentEvent val w (ancestralExtension A k)) =
        setJoint G val K (ancestralExtension A k) w := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      intro w
      rw [ancestralExtension_full, assignmentEvent_univ, mass, Finset.sum_singleton, setJoint_univ]
    | of_succ k hk ih =>
      intro w
      let i : Fin n := ⟨k, hk⟩
      by_cases hi : i ∈ A
      · have heq : ancestralExtension A (k + 1) = ancestralExtension A k := by
          rw [show k = i.val from rfl, ancestralExtension_succ,
            Finset.insert_eq_of_mem ((mem_ancestralExtension A i.val i).mpr (Or.inl hi))]
        rw [← heq]
        exact ih w
      · have hs := ancestralExtension_sink G A hA i hi
        have herase : (ancestralExtension A (k + 1)).erase i = ancestralExtension A k := by
          rw [show k = i.val from rfl, ancestralExtension_succ, Finset.erase_insert]
          have hnot : i ∉ ancestralExtension A i.val := by
            intro hm
            rcases (mem_ancestralExtension A i.val i).mp hm with hiA | hlt
            · exact hi hiA
            · exact (Nat.lt_irrefl _) hlt
          exact hnot
        calc
          _ = ∑ a : val i, mass (joint G val K)
              (assignmentEvent val (Function.update w i a) (ancestralExtension A (k + 1))) := by
            rw [← herase]
            exact mass_assignment_erase_eq_sum val _ _ i hs.1 w
          _ = ∑ a : val i, setJoint G val K (ancestralExtension A (k + 1))
              (Function.update w i a) := Finset.sum_congr rfl (fun a _ => ih _)
          _ = _ := by
            rw [sum_setJoint_sink G val K hNO _ (ancestralExtension_ancestral G A hA _) i hs w, herase]
  simpa only [ancestralExtension_zero] using h 0 (Nat.zero_le n) w

end MeraConstraints.GlobalModel.KernelReconstruction
