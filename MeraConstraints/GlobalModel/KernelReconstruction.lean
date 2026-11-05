import MeraConstraints.CompactDistrict.OrderingConstraints
import MeraConstraints.GlobalModel.Prefix
import MeraConstraints.Probability.PrefixPartition

/-!
# Reconstructing a distribution from candidate district factors

This chapter begins Step 2 of the proof of Proposition 4 (`prop:nontrivial`). A
"kernel" in `GlobalModel.KernelReconstruction` is any candidate vector `K d` for the
district factor of district `d` that satisfies (N) and (O). It need not come from a
distribution and need not lie in the district polytope; the theorems build the
distribution. Given positive kernels, `joint K` is the product over districts of
`K d` evaluated at the projection of a complete assignment onto the district's rows
`(v₁, v₂)`. We show that `joint K` is a strictly positive probability distribution
(`joint_mem_stdSimplex`). `GlobalModel.KernelIdentification` shows that its district
factors are the kernels.

Normalization is the case `A = ∅` of equation (`eqn:ancmargin`), proved here for
prefixes of the observed order. `prefixMargin K d k w` is the margin of `K d` over
the members of position `k` or later. The members before `k` form a closed set, so
(O) shows that this margin depends only on the earlier variables
(`prefixMargin_congr_prefix`); for an empty set of members (N) gives one. Summing
out the last variable one at a time then gives the probability of every prefix event
(`joint_prefix_mass`), and in particular total mass one (`joint_sum_eq_one`).
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

/-- The margin of the kernel `K d` over the members of position `k` or later: the sum of
`K d` over the member values that agree with `w` before `k`, with the external parents
taken from `w`. -/
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
  have hm (out : Output G val d) : PrefixMatch G val d n w out ↔
      out = (fun i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d => w i.val) := by
    constructor
    · intro h
      funext i
      exact h i i.val.isLt
    · rintro rfl i _
      rfl
  simp only [prefixMargin, hm]
  simp [CompactDistrict.project]

omit [∀ i, DecidableEq (val i)] in
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
  · refine ⟨fun i => w i.val, Finset.mem_univ _, ?_⟩
    have hm : PrefixMatch G val d k w (fun i => w i.val) := fun _ _ => rfl
    simpa only [if_pos hm] using hK d ((fun i => w i.val), fun j => w j)

theorem prefixMargin_eq_closedMargin (K : Kernels G val) (d : HiddenGraph.DistrictId G)
    (k : ℕ) (w : FullAssign val)
    (S : CompactDistrict.OrderingConstraints.ClosedSubset G d)
    (hS : S.val = HiddenGraph.districtPrefix G d k) :
    prefixMargin G val K d k w = CompactDistrict.OrderingConstraints.margin G val d
      (K d) S (fun i => w i.val) (fun j => w j) := by
  classical
  have hm (out : Output G val d) : PrefixMatch G val d k w out ↔
      CompactDistrict.OrderingConstraints.restrictOutput G val d S out =
        (fun i : {i : Fin n // i ∈ S.val} => w i.val) := by
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

/-- By (N) and (O), `prefixMargin` depends on `w` only through the variables before
position `k`. -/
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
    have ha : (fun i : {i : Fin n // i ∈ S.val} => w i.val) =
        (fun i : {i : Fin n // i ∈ S.val} => v i.val) := by
      funext i
      exact hpre i ((HiddenGraph.mem_districtPrefix G d k i).mp i.2).2
    rw [ha]
    apply ((CompactDistrict.OrderingConstraints.feasible_iff G val d (K d)).mp (hNO d)).2
    intro j hj
    obtain ⟨i, hi, hji⟩ := hj
    exact hpre j (Nat.lt_trans (G.observed.parents_lt hji)
      ((HiddenGraph.mem_districtPrefix G d k i).mp hi).2)

/-- The joint mass built in Step 2: the product over districts of the kernel `K d` at
the projection of `w` onto the district's rows. -/
noncomputable def joint (K : Kernels G val) (w : FullAssign val) : ℝ :=
  ∏ d, K d (CompactDistrict.project G.observed val (HiddenGraph.observedDistrict G) d w)

omit [DecidableEq (HiddenGraph.DistrictId G)] [∀ i, Fintype (val i)]
  [∀ i, DecidableEq (val i)] in
theorem joint_pos (K : Kernels G val) (hK : Positive G val K) (w : FullAssign val) :
    0 < joint G val K w := Finset.prod_pos fun d _ => hK d _

omit [DecidableEq (HiddenGraph.DistrictId G)] [∀ i, Fintype (val i)]
  [∀ i, DecidableEq (val i)] in
/-- Adding position `i` adds no matching condition for a district other than the
district of `V_i`. -/
theorem prefixMatch_succ_of_ne (d : HiddenGraph.DistrictId G) (i : Fin n)
    (w : FullAssign val) (out : Output G val d) (hne : d ≠ HiddenGraph.observedDistrict G i) :
    PrefixMatch G val d (i.val + 1) w out ↔ PrefixMatch G val d i.val w out := by
  constructor
  · intro h j hj
    exact h j (by omega)
  · intro h j hj
    by_cases hji : j.val.val < i.val
    · exact h j hji
    · have he : j.val = i := Fin.ext (by omega)
      exact (hne (j.2.symm.trans (congrArg (HiddenGraph.observedDistrict G) he))).elim

omit [∀ i, DecidableEq (val i)] in
theorem prefixMargin_succ_of_ne (K : Kernels G val) (d : HiddenGraph.DistrictId G)
    (i : Fin n) (w : FullAssign val) (hne : d ≠ HiddenGraph.observedDistrict G i) :
    prefixMargin G val K d (i.val + 1) w = prefixMargin G val K d i.val w := by
  classical
  unfold prefixMargin
  simp_rw [prefixMatch_succ_of_ne G val d i w _ hne]

/-- Changing the value at `i` does not change `prefixMargin` at position `i`. -/
theorem prefixMargin_update (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (d : HiddenGraph.DistrictId G) (i : Fin n) (w : FullAssign val) (a : val i) :
    prefixMargin G val K d i.val (Function.update w i a) = prefixMargin G val K d i.val w := by
  apply prefixMargin_congr_prefix G val K hNO
  intro j hj
  exact Function.update_of_ne (fun he => by subst j; omega) _ _

/-- Summing `prefixMargin` at position `i + 1` over the value of `V_i` gives
`prefixMargin` at position `i`, for the district of `V_i`. -/
theorem sum_prefixMargin_next (K : Kernels G val) (i : Fin n) (w : FullAssign val) :
    (∑ a : val i, prefixMargin G val K (HiddenGraph.observedDistrict G i)
      (i.val + 1) (Function.update w i a)) =
      prefixMargin G val K (HiddenGraph.observedDistrict G i) i.val w := by
  classical
  let d := HiddenGraph.observedDistrict G i
  have hext (a : val i) :
      (fun j : CompactDistrict.ExternalParent G.observed (HiddenGraph.observedDistrict G) d =>
        Function.update w i a j.val) =
      (fun j : CompactDistrict.ExternalParent G.observed (HiddenGraph.observedDistrict G) d => w j.val) := by
    funext j
    apply Function.update_of_ne
    intro hj
    exact j.2.1 (congrArg (HiddenGraph.observedDistrict G) hj)
  have hmatch (a : val i) (out : Output G val d) :
      PrefixMatch G val d (i.val + 1) (Function.update w i a) out ↔
        PrefixMatch G val d i.val w out ∧ out ⟨i, rfl⟩ = a := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro j hj
        have hji : j.val ≠ i := by
          intro he
          have hv := congrArg Fin.val he
          omega
        simpa only [Function.update_of_ne hji] using h j (by omega)
      · simpa using h ⟨i, rfl⟩ (Nat.lt_succ_self _)
    · rintro ⟨h, ha⟩ j hj
      by_cases hji : j.val = i
      · have he : j = (⟨i, rfl⟩ : CompactDistrict.Member (HiddenGraph.observedDistrict G) d) :=
          Subtype.ext hji
        subst j
        simpa using ha
      · rw [Function.update_of_ne hji]
        exact h j (by have hn : j.val.val ≠ i.val := fun he => hji (Fin.ext he); omega)
  change (∑ a : val i, prefixMargin G val K d (i.val + 1) (Function.update w i a)) = _
  simp only [prefixMargin]
  simp_rw [hext, hmatch]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro out _
  exact sum_indicator_and_eq _ (out ⟨i, rfl⟩) _

/-- The product over districts of `prefixMargin` at position `k`. -/
noncomputable def prefixJoint (K : Kernels G val) (k : ℕ) (w : FullAssign val) : ℝ :=
  ∏ d, prefixMargin G val K d k w

theorem prefixJoint_zero (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (w : FullAssign val) : prefixJoint G val K 0 w = 1 := by
  simp [prefixJoint, prefixMargin_zero G val K hNO]

theorem prefixJoint_full (K : Kernels G val) (w : FullAssign val) :
    prefixJoint G val K n w = joint G val K w := by
  simp only [prefixJoint, prefixMargin_full, joint]

/-- Summing `prefixJoint` at position `i + 1` over the value of `V_i` gives
`prefixJoint` at position `i`: only the district of `V_i` changes. -/
theorem sum_prefixJoint_next (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (i : Fin n) (w : FullAssign val) :
    (∑ a : val i, prefixJoint G val K (i.val + 1) (Function.update w i a)) =
      prefixJoint G val K i.val w := by
  classical
  let d := HiddenGraph.observedDistrict G i
  let rest := ∏ e ∈ Finset.univ.erase d, prefixMargin G val K e i.val w
  have hsplit (a : val i) : prefixJoint G val K (i.val + 1) (Function.update w i a) =
      prefixMargin G val K d (i.val + 1) (Function.update w i a) * rest := by
    rw [prefixJoint, ← Finset.mul_prod_erase Finset.univ
      (fun e => prefixMargin G val K e (i.val + 1) (Function.update w i a)) (Finset.mem_univ d)]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    rw [prefixMargin_succ_of_ne G val K e i _ (Finset.ne_of_mem_erase he),
      prefixMargin_update G val K hNO]
  simp_rw [hsplit]
  rw [← Finset.sum_mul, sum_prefixMargin_next]
  exact Finset.mul_prod_erase Finset.univ (fun e => prefixMargin G val K e i.val w)
    (Finset.mem_univ d)

/-- Under `joint K`, the probability that the first `k` variables take the values in
`w` is `prefixJoint K k w`. Proved by summing out the last variable one at a time,
starting from `k = n`. -/
theorem joint_prefix_mass (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (k : ℕ) (hk : k ≤ n) (w : FullAssign val) :
    mass (joint G val K) (prefixEvent val w k) = prefixJoint G val K k w := by
  have h : ∀ k ≤ n, ∀ w : FullAssign val,
      mass (joint G val K) (prefixEvent val w k) = prefixJoint G val K k w := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => intro w; rw [prefixEvent_full, mass, Finset.sum_singleton, prefixJoint_full]
    | of_succ k hk ih =>
      intro w
      let i : Fin n := ⟨k, hk⟩
      rw [show k = i.val from rfl, mass_prefix_eq_sum_next val _ w i]
      have ih' (v : FullAssign val) :
          mass (joint G val K) (prefixEvent val v (i.val + 1)) = prefixJoint G val K (i.val + 1) v := ih v
      simp_rw [ih']
      exact sum_prefixJoint_next G val K hNO i w
  exact h k hk w

variable [∀ i, Nonempty (val i)]

/-- The total mass of `joint K` is one whenever the kernels satisfy (N) and (O). The
entries may have any sign. -/
theorem joint_sum_eq_one (K : Kernels G val) (hNO : NormalizedOrdered G val K) :
    (∑ w, joint G val K w) = 1 := by
  classical
  let w : FullAssign val := fun i => Classical.choice (inferInstance : Nonempty (val i))
  have h := joint_prefix_mass G val K hNO 0 (Nat.zero_le n) w
  simpa [mass, prefixJoint_zero G val K hNO] using h

/-- Positive kernels satisfying (N) and (O) give a probability distribution `joint K`,
strictly positive by `joint_pos`. -/
theorem joint_mem_stdSimplex (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) : joint G val K ∈ stdSimplex ℝ (FullAssign val) :=
  ⟨fun w => (joint_pos G val K hK w).le, joint_sum_eq_one G val K hNO⟩

end MeraConstraints.GlobalModel.KernelReconstruction
