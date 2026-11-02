import MeraConstraints.CompactDistrict.OrderingConstraints
import MeraConstraints.GlobalModel.Prefix

/-!
# Reconstructing a joint law from arbitrary district kernels

Appendix Step 2 of Proposition `prop:nontrivial` starts with positive district
kernels obeying (N)/(O), not necessarily kernels in the district polytopes.
Consequently their normalization cannot be justified by choosing response
profile laws. This chapter begins the direct kernel argument.

`prefixMargin K d k w` is the ordinary margin of the arbitrary district
kernel over its members before global position `k`. These member sets are
fully closed in the original observed graph. The actual (O) equations prove
that their margins depend only on those members and their external parents,
which all precede `k`. Empty member prefixes use normalization (N) instead.

No profile representation, global factorization, or graphical separation
theorem is a hypothesis. The intended joint mass is defined explicitly as
the product of district kernels on compact projections of a full assignment.
The prefix dependence lemmas supply the reverse-elimination argument needed
to prove its normalization, rather than assuming the resulting product is a
probability law.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

abbrev Output (d : HiddenGraph.DistrictId G) :=
  CompactDistrict.MemberAssign val (HiddenGraph.observedDistrict G) d

abbrev Input (d : HiddenGraph.DistrictId G) :=
  CompactDistrict.ExternalAssign G.observed val (HiddenGraph.observedDistrict G) d

abbrev CompactRow (d : HiddenGraph.DistrictId G) :=
  CompactDistrict.Row G.observed val (HiddenGraph.observedDistrict G) d

abbrev Kernels := ∀ d : HiddenGraph.DistrictId G, CompactRow G val d → ℝ

def NormalizedOrdered (K : Kernels G val) : Prop :=
  ∀ d, EqualityConstraints.Feasible
    (CompactDistrict.OrderingConstraints.constraintsMatrix G val d)
    (CompactDistrict.OrderingConstraints.constraintsRhs G val d) (K d)

def Positive (K : Kernels G val) : Prop := ∀ d x, 0 < K d x

/-- Matching the observed values of the members before global position `k`. -/
def PrefixMatch (d : HiddenGraph.DistrictId G) (k : ℕ) (w : FullAssign val)
    (out : Output G val d) : Prop :=
  ∀ i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d,
    i.val.val < k → out i = w i

/-- A literal kernel margin, with external input taken from the full assignment. -/
noncomputable def prefixMargin (K : Kernels G val) (d : HiddenGraph.DistrictId G)
    (k : ℕ) (w : FullAssign val) : ℝ := by
  classical
  exact ∑ out, if PrefixMatch G val d k w out then K d (out, fun j => w j) else 0

theorem kernel_normalization (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : HiddenGraph.DistrictId G) (e : Input G val d) :
    (∑ out, K d (out, e)) = 1 :=
  ((CompactDistrict.OrderingConstraints.feasible_iff G val d (K d)).mp (hNO d)).1 e

theorem prefixMargin_zero (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : HiddenGraph.DistrictId G) (w : FullAssign val) :
    prefixMargin G val K d 0 w = 1 := by
  simpa only [prefixMargin, PrefixMatch, Nat.not_lt_zero, false_implies,
    implies_true, if_true] using kernel_normalization G val K hNO d (fun j => w j)

theorem prefixMargin_full (K : Kernels G val) (d : HiddenGraph.DistrictId G)
    (w : FullAssign val) :
    prefixMargin G val K d n w =
      K d (CompactDistrict.project G.observed val (HiddenGraph.observedDistrict G) d w) := by
  classical
  have hm (out : Output G val d) : PrefixMatch G val d n w out ↔ out = (fun i => w i) := by
    constructor
    · intro h
      funext i
      exact h i i.val.isLt
    · rintro rfl i _
      rfl
  simp only [prefixMargin, hm]
  simp [CompactDistrict.project]

theorem prefixMargin_pos (K : Kernels G val) (hK : Positive G val K)
    (d : HiddenGraph.DistrictId G) (k : ℕ) (w : FullAssign val) :
    0 < prefixMargin G val K d k w := by
  classical
  unfold prefixMargin
  apply Finset.sum_pos'
  · intro out _
    split
    · exact (hK d _).le
    · exact le_refl _
  · refine ⟨fun i => w i, Finset.mem_univ _, ?_⟩
    have hm : PrefixMatch G val d k w (fun i => w i) := fun _ _ => rfl
    simpa only [if_pos hm] using hK d ((fun i => w i), fun j => w j)

theorem prefixMargin_eq_closedMargin (K : Kernels G val) (d : HiddenGraph.DistrictId G)
    (k : ℕ) (w : FullAssign val)
    (S : CompactDistrict.OrderingConstraints.ClosedSubset G d)
    (hS : S.val = HiddenGraph.districtPrefix G d k) :
    prefixMargin G val K d k w = CompactDistrict.OrderingConstraints.margin G val d
      (K d) S (fun i => w i) (fun j => w j) := by
  classical
  have hm (out : Output G val d) : PrefixMatch G val d k w out ↔
      CompactDistrict.OrderingConstraints.restrictOutput G val d S out = (fun i => w i) := by
    constructor
    · intro h
      funext i
      have hi : i.val ∈ HiddenGraph.districtPrefix G d k := hS ▸ i.2
      exact h ⟨i, S.2.2.1 i i.2⟩ ((HiddenGraph.mem_districtPrefix G d k i).mp hi).2
    · intro h i hi
      have hiS : i.val ∈ S.val := by
        rw [hS]
        exact (HiddenGraph.mem_districtPrefix G d k i).mpr ⟨i.2, hi⟩
      exact congrFun h ⟨i, hiS⟩
  simp only [prefixMargin, CompactDistrict.OrderingConstraints.margin,
    CompactDistrict.OrderingConstraints.marginIndicator, hm, ite_mul, one_mul, zero_mul]

theorem prefixMargin_eq_one_of_empty (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : HiddenGraph.DistrictId G) (k : ℕ) (w : FullAssign val)
    (hempty : HiddenGraph.districtPrefix G d k = ∅) : prefixMargin G val K d k w = 1 := by
  classical
  have hm : ∀ out, PrefixMatch G val d k w out := by
    intro out i hi
    have hs : i.val ∈ HiddenGraph.districtPrefix G d k :=
      (HiddenGraph.mem_districtPrefix G d k i).mpr ⟨i.2, hi⟩
    rw [hempty] at hs
    exact False.elim (Finset.notMem_empty _ hs)
  simp only [prefixMargin, if_pos (hm _)]
  exact kernel_normalization G val K hNO d (fun j => w j)

/-- The actual (O) equations give prefix dependence for arbitrary kernels.
No assumption that the kernels belong to a district polytope is made. -/
theorem prefixMargin_congr_prefix (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : HiddenGraph.DistrictId G) (k : ℕ) (w v : FullAssign val)
    (hpre : ∀ j : Fin n, j.val < k → w j = v j) :
    prefixMargin G val K d k w = prefixMargin G val K d k v := by
  classical
  by_cases he : HiddenGraph.districtPrefix G d k = ∅
  · rw [prefixMargin_eq_one_of_empty G val K hNO d k w he,
      prefixMargin_eq_one_of_empty G val K hNO d k v he]
  · let S : CompactDistrict.OrderingConstraints.ClosedSubset G d :=
      ⟨HiddenGraph.districtPrefix G d k, Finset.nonempty_iff_ne_empty.mpr he,
        HiddenGraph.districtPrefix_fullClosed G d k⟩
    rw [prefixMargin_eq_closedMargin G val K d k w S rfl,
      prefixMargin_eq_closedMargin G val K d k v S rfl]
    have ha : (fun i : {i : Fin n // i ∈ S.val} => w i) = (fun i => v i) := by
      funext i
      exact hpre i ((HiddenGraph.mem_districtPrefix G d k i).mp i.2).2
    rw [ha]
    apply ((CompactDistrict.OrderingConstraints.feasible_iff G val d (K d)).mp (hNO d)).2
    intro j hj
    obtain ⟨i, hi, hji⟩ := hj
    exact hpre j (Nat.lt_trans (G.observed.parents_lt hji)
      ((HiddenGraph.mem_districtPrefix G d k i).mp hi).2)

/-- Candidate joint mass in the appendix's positive-kernel construction.
Normalization is a theorem to prove, not part of this definition. -/
noncomputable def joint (K : Kernels G val) (w : FullAssign val) : ℝ :=
  ∏ d, K d (CompactDistrict.project G.observed val (HiddenGraph.observedDistrict G) d w)

theorem joint_pos (K : Kernels G val) (hK : Positive G val K) (w : FullAssign val) :
    0 < joint G val K w := Finset.prod_pos fun d _ => hK d _

end MeraConstraints.GlobalModel.KernelReconstruction
