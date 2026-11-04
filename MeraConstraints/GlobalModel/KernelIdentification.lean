import MeraConstraints.GlobalModel.KernelReconstruction
import MeraConstraints.GlobalModel.OrderedMarkov

/-!
# Recovering arbitrary positive kernels from the reconstructed law

This completes the fixed-order part of Appendix Step 2 for Proposition
`prop:nontrivial`. The inputs are arbitrary positive compact kernels obeying
the actual normalization and full-ancestry ordering equations (N)/(O).
They need not belong to any district polytope.

Reverse elimination has already proved that their product is a probability
law and identified its prefix masses. We cancel the other district margins,
use (O) to reduce each ratio to the manuscript's cumulative `C_i`, and
telescope to recover each supplied kernel as an observable district factor.
The required fixed-order Markov equations are conclusions of this construction.

This is not an original-SCM realization: incompatible kernels are allowed.
Nor is it a theorem enumerating all graphical d-separation statements. The
full ordering-invariance/all-ancestral-set argument remains separate when
using this construction for the manuscript's exact equality-triviality domain.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)]
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The current district's margins depend only on `C_i` and the current
value, by the actual (O) equations on the corresponding fully closed set. -/
theorem prefixMargin_congr_conditioning (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (w v : FullAssign val) (i : Fin n) (k : ℕ) (hk : k ≤ i.val + 1)
    (hC : ∀ j ∈ Reconstruction.conditioningVariables G.observed
      (HiddenGraph.observedDistrict G) i, w j = v j) (hi : w i = v i) :
    prefixMargin G val K (HiddenGraph.observedDistrict G i) k w =
      prefixMargin G val K (HiddenGraph.observedDistrict G i) k v := by
  classical
  let d := HiddenGraph.observedDistrict G i
  by_cases he : HiddenGraph.districtPrefix G d k = ∅
  · rw [prefixMargin_eq_one_of_empty G val K hNO d k w he,
      prefixMargin_eq_one_of_empty G val K hNO d k v he]
  · let S : CompactDistrict.OrderingConstraints.ClosedSubset G d :=
      ⟨HiddenGraph.districtPrefix G d k, Finset.nonempty_iff_ne_empty.mpr he,
        HiddenGraph.districtPrefix_fullClosed G d k⟩
    rw [prefixMargin_eq_closedMargin G val K d k w S rfl,
      prefixMargin_eq_closedMargin G val K d k v S rfl]
    have ha : (fun j : {j : Fin n // j ∈ S.val} => w j.val) =
        (fun j : {j : Fin n // j ∈ S.val} => v j.val) := by
      funext j
      obtain ⟨hjd, hjk⟩ := (HiddenGraph.mem_districtPrefix G d k j).mp j.2
      by_cases hji : j.val = i
      · rw [hji]
        exact hi
      · apply hC j
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, Or.inl ⟨by
          change j.val.val < i.val
          have hn : j.val.val ≠ i.val := fun heq => hji (Fin.ext heq)
          omega, hjd⟩⟩
    rw [ha]
    apply ((CompactDistrict.OrderingConstraints.feasible_iff G val d (K d)).mp (hNO d)).2
    intro j hj
    obtain ⟨l, hl, hjl⟩ := hj
    obtain ⟨hld, hlk⟩ := (HiddenGraph.mem_districtPrefix G d k l).mp hl
    apply hC j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inr ⟨l, ?_, hld, hjl, j.2.1⟩⟩
    change l.val ≤ i.val
    omega

private theorem ratio_products (f g : HiddenGraph.DistrictId G → ℝ)
    (d : HiddenGraph.DistrictId G) (hg : (∏ e, g e) ≠ 0)
    (heq : ∀ e, e ≠ d → f e = g e) :
    (∏ e, f e) / (∏ e, g e) = f d / g d := by
  classical
  have hgd : g d ≠ 0 := (Finset.prod_ne_zero_iff.mp hg) d (Finset.mem_univ d)
  have hrest : (∏ e ∈ Finset.univ.erase d, f e) = ∏ e ∈ Finset.univ.erase d, g e :=
    Finset.prod_congr rfl fun e he => heq e (Finset.ne_of_mem_erase he)
  apply (div_eq_div_iff hg hgd).2
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ d),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ d), hrest]
  ring

/-- A prefix conditional is the ratio of the two margins of its own
district; all other district factors cancel. -/
theorem joint_prefixConditional (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (w : FullAssign val) (i : Fin n) :
    prefixConditional val (joint G val K) w i =
      prefixMargin G val K (HiddenGraph.observedDistrict G i) (i.val + 1) w /
        prefixMargin G val K (HiddenGraph.observedDistrict G i) i.val w := by
  rw [prefixConditional_eq_ratio,
    joint_prefix_mass G val K hNO _ (by omega), joint_prefix_mass G val K hNO _ (by omega)]
  apply ratio_products G _ _ _
  · exact Finset.prod_ne_zero_iff.mpr fun d _ => (prefixMargin_pos G val K hK d _ w).ne'
  · intro d hd
    exact prefixMargin_succ_of_ne G val K d i w hd

theorem joint_prefixConditional_congr_conditioning (K : Kernels G val)
    (hNO : NormalizedOrdered G val K) (hK : Positive G val K)
    (w v : FullAssign val) (i : Fin n)
    (hC : ∀ j ∈ Reconstruction.conditioningVariables G.observed
      (HiddenGraph.observedDistrict G) i, w j = v j) (hi : w i = v i) :
    prefixConditional val (joint G val K) w i = prefixConditional val (joint G val K) v i := by
  rw [joint_prefixConditional G val K hNO hK, joint_prefixConditional G val K hNO hK,
    prefixMargin_congr_conditioning G val K hNO w v i (i.val + 1) le_rfl hC hi,
    prefixMargin_congr_conditioning G val K hNO w v i i.val (Nat.le_succ _) hC hi]

/-- Cumulative-condition identification is obtained by finite averaging,
using the proved ratio dependence rather than a presumed Markov property. -/
theorem joint_prefixConditional_eq_conditioning (K : Kernels G val)
    (hNO : NormalizedOrdered G val K) (hK : Positive G val K) (w : FullAssign val) (i : Fin n) :
    prefixConditional val (joint G val K) w i =
      conditional (joint G val K) (valueEvent val w i)
        (Reconstruction.conditioningEvent G.observed val (HiddenGraph.observedDistrict G) w i) :=
  GlobalModel.prefixConditional_eq_conditioning_of_congr G.observed val
    (HiddenGraph.observedDistrict G) _ (joint_pos G val K hK)
    (joint_prefixConditional_congr_conditioning G val K hNO hK) w i

theorem joint_orderedMarkov (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) :
    Reconstruction.OrderedMarkov G.observed val (HiddenGraph.observedDistrict G) (joint G val K) := by
  intro w i
  let p := joint G val K
  let A := valueEvent val w i
  let B := prefixEvent val w i.val
  let C := Reconstruction.conditioningEvent G.observed val (HiddenGraph.observedDistrict G) w i
  have hB : mass p B ≠ 0 := (prefix_mass_pos val _ (joint_pos G val K hK) w i.val).ne'
  have hC : mass p C ≠ 0 := (mass_pos_of_mem (joint_pos G val K hK)
    (Reconstruction.self_mem_conditioningEvent G.observed val (HiddenGraph.observedDistrict G) w i)).ne'
  have hBC : B ∩ C = B := Finset.inter_eq_left.mpr
    (Reconstruction.prefixEvent_subset_conditioningEvent G.observed val (HiddenGraph.observedDistrict G) w i)
  have h := joint_prefixConditional_eq_conditioning G val K hNO hK w i
  change mass p (A ∩ B) / mass p B = mass p (A ∩ C) / mass p C at h
  change mass p ((A ∩ B) ∩ C) * mass p C = mass p (A ∩ C) * mass p (B ∩ C)
  rw [Finset.inter_assoc, hBC]
  exact (div_eq_div_iff hB hC).mp h

/-- Telescoping the successive ratios in one district recovers exactly
the supplied compact kernel, including its external input. -/
theorem joint_observableFactor (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (d : HiddenGraph.DistrictId G) (w : FullAssign val) :
    Reconstruction.observableFactor G.observed val (HiddenGraph.observedDistrict G) (joint G val K) d w =
      K d (CompactDistrict.project G.observed val (HiddenGraph.observedDistrict G) d w) := by
  classical
  rw [Reconstruction.observableFactor]
  simp_rw [← joint_prefixConditional_eq_conditioning G val K hNO hK]
  rw [← Finset.prod_subtype (Finset.univ.filter (fun i : Fin n => HiddenGraph.observedDistrict G i = d))
    (by intro i; simp) (fun i : Fin n => prefixConditional val (joint G val K) w i)]
  have hterm : ∀ i : Fin n,
      (if HiddenGraph.observedDistrict G i = d then prefixConditional val (joint G val K) w i else 1) =
        prefixMargin G val K d (i.val + 1) w / prefixMargin G val K d i.val w := by
    intro i
    by_cases hid : HiddenGraph.observedDistrict G i = d
    · rw [if_pos hid, joint_prefixConditional G val K hNO hK, hid]
    · rw [if_neg hid, prefixMargin_succ_of_ne G val K d i w (Ne.symm hid),
        div_self (prefixMargin_pos G val K hK d i.val w).ne']
  rw [Finset.prod_filter]
  simp_rw [hterm]
  rw [Fin.prod_univ_eq_prod_range
    (fun k => prefixMargin G val K d (k + 1) w / prefixMargin G val K d k w) n,
    prod_successive_ratios _ n (prefixMargin_zero G val K hNO d w)
      (fun k _ => (prefixMargin_pos G val K hK d k w).ne'), prefixMargin_full]

variable [∀ i, Nonempty (val i)]

/-- Fixed-order positive-kernel reconstruction: the explicit product is a
strictly positive probability law satisfying the ordered equations and
recovering every specified district kernel as its observable factor. -/
theorem reconstruct_positive_kernels (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      Reconstruction.OrderedMarkov G.observed val (HiddenGraph.observedDistrict G) p ∧
      ∀ d w, Reconstruction.observableFactor G.observed val (HiddenGraph.observedDistrict G) p d w =
        K d (CompactDistrict.project G.observed val (HiddenGraph.observedDistrict G) d w) :=
  ⟨joint G val K, joint_mem_stdSimplex G val K hNO hK, joint_pos G val K hK,
    joint_orderedMarkov G val K hNO hK, joint_observableFactor G val K hNO hK⟩

end MeraConstraints.GlobalModel.KernelReconstruction
