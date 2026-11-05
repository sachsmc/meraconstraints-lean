import MeraConstraints.GlobalModel.KernelReconstruction
import MeraConstraints.HiddenGraph.AncestralSets
import MeraConstraints.Probability.AssignmentPartition

/-!
# The ancestral margin identity

This chapter proves equation (`eqn:ancmargin`) in Step 2 of the proof of
Proposition 4 (`prop:nontrivial`). Let the kernels `K d` satisfy (N) and (O), and let
`A` be a set of observed variables that contains all observed ancestors of its
elements. Then the probability under `joint K` that the variables in `A` take the
values `w` is the product over districts of the margins of `K d` over the members of
`D ∩ A` (`joint_ancestral_mass`).

The proof removes the variables outside `A` one at a time, in reverse topological
order. A variable with no children in the current set appears only in the factor of
its own district, and summing that factor over the variable gives the factor for the
smaller set (`sum_setJoint_sink`). Because `A` contains all ancestors, `D ∩ A` is
closed (`FullClosed`), so (O) shows that the margin on `D ∩ A` depends only on its
members and their external parents (`setMargin_congr`). Neither positivity nor
membership in the district polytopes is needed, and the entries may have any sign.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)]
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The member values `out` of district `d` agree with `w` on the members that lie in
`A`. -/
def SetMatch (d : DistrictId G) (A : Finset (Fin n)) (w : FullAssign val)
    (out : Output G val d) : Prop :=
  ∀ j : CompactDistrict.Member (observedDistrict G) d, j.val ∈ A → out j = w j

/-- The margin of the kernel `K d` over the members outside `A`: the sum of `K d` over
the member values that agree with `w` on `D ∩ A`, with the external parents taken
from `w`. -/
noncomputable def setMargin (K : Kernels G val) (d : DistrictId G)
    (A : Finset (Fin n)) (w : FullAssign val) : ℝ := by
  classical
  exact ∑ out, if SetMatch G val d A w out then K d (out, fun j => w j) else 0

/-- `setMargin` is the margin that appears in (O) for the closed set `D ∩ A`. -/
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

/-- A district with no member in `A` has margin one, by (N). -/
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

/-- By (O), for a set `A` containing its ancestors, `setMargin` depends on `w` only
through the members of `D ∩ A` and their external parents. -/
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

/-- Summing the margin over the value of a member `V_i` in `A` gives the margin for `A`
without `V_i`. -/
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

/-- The product over districts of `setMargin`: the right side of (`eqn:ancmargin`). -/
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

/-- The inductive step for (`eqn:ancmargin`): summing `setJoint` over a variable `V_i`
with no children in `A` gives `setJoint` for `A` without `V_i`. -/
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

/-- Equation (`eqn:ancmargin`) in the proof of Proposition 4: for every set `A` of
observed variables containing its ancestors, the probability under `joint K` that the
variables in `A` take the values `w` is `setJoint K A w`. No positivity is needed. -/
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
