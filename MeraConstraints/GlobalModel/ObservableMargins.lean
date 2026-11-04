import MeraConstraints.GlobalModel.AncestralProducts
import MeraConstraints.GlobalModel.AncestralKernels

/-!
# Literal margins of an arbitrary graph-compatible observed factor

This is the converse direction to kernel reconstruction. Starting from an
arbitrary positive globally Markov observed law, its compact observable
district factors have ancestral margins equal to the retained conditional
products. The argument uses the already proved ordering invariance and
one-coordinate summation, never polytope membership or presumed (N)/(O).

Reverse elimination through `A ∪ prefix(k)` reaches every ancestral set,
including ancestors of fully closed subsets which are not fixed-order prefixes.
-/

namespace MeraConstraints.GlobalModel.OrderingInvariance

open FiniteProbability HiddenGraph
open GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)]

noncomputable def observableKernels (p : FullAssign val → ℝ) : Kernels G val :=
  fun d => CompactDistrict.observableFactor G.observed val (observedDistrict G) d p

theorem observable_setMargin_univ (p : FullAssign val → ℝ) (d : DistrictId G)
    (w : FullAssign val) :
    setMargin G val (observableKernels G val p) d Finset.univ w =
      Reconstruction.observableFactor G.observed val (observedDistrict G) p d w := by
  classical
  have hm (out : Output G val d) : SetMatch G val d Finset.univ w out ↔
      out = (fun j : CompactDistrict.Member (observedDistrict G) d => w j.val) :=
    ⟨fun h => funext (fun j => h j (Finset.mem_univ _)), fun h j _ => congrFun h j⟩
  simp only [setMargin, hm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact CompactDistrict.observableFactor_project G.observed val (observedDistrict G) d p w

/-- Every ancestral district margin is its literal retained conditional product. -/
theorem observable_setMargin_eq_ancestralProduct (p : FullAssign val → ℝ)
    (hpos : ∀ w, 0 < p w) (hGlobal : MoralGlobalMarkov G val p)
    (d : DistrictId G) (A : Finset (Fin n)) (hA : ObservedAncestral G A) (w : FullAssign val) :
    setMargin G val (observableKernels G val p) d A w = ancestralProduct G val p d A w := by
  classical
  have h : ∀ k ≤ n, ∀ w : FullAssign val,
      setMargin G val (observableKernels G val p) d (ancestralExtension A k) w =
        ancestralProduct G val p d (ancestralExtension A k) w := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      intro w
      rw [ancestralExtension_full, observable_setMargin_univ,
        ancestralProduct_univ G val p hpos hGlobal]
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
          simpa only [mem_ancestralExtension, lt_self_iff_false, or_false] using hi
        have hAnc := ancestralExtension_ancestral G A hA (k + 1)
        by_cases hid : observedDistrict G i = d
        · calc
            _ = ∑ a : val i, setMargin G val (observableKernels G val p) d
                (ancestralExtension A (k + 1)) (Function.update w i a) := by
              rw [← herase, ← hid]
              exact (sum_setMargin_member G val _ _ i hs.1 w).symm
            _ = ∑ a : val i, ancestralProduct G val p d
                (ancestralExtension A (k + 1)) (Function.update w i a) :=
              Finset.sum_congr rfl (fun a _ => ih _)
            _ = _ := by
              rw [← hid, sum_ancestralProduct_sink G val p hpos hGlobal _ hAnc i hs w, herase]
        · calc
            _ = setMargin G val (observableKernels G val p) d
                (ancestralExtension A (k + 1)) w := by
              rw [← herase]
              exact (setMargin_erase_of_ne G val _ d _ i w (Ne.symm hid)).symm
            _ = ancestralProduct G val p d (ancestralExtension A (k + 1)) w := ih w
            _ = _ := by
              rw [ancestralProduct_remove G val p hpos hGlobal d _ hAnc i hs,
                blanketWeight, if_neg hid, one_mul, herase]
  simpa only [ancestralExtension_zero] using h 0 (Nat.zero_le n) w

end MeraConstraints.GlobalModel.OrderingInvariance
