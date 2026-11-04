import MeraConstraints.GlobalModel.OrderingInvariance
import MeraConstraints.HiddenGraph.CanonicalOrder
import MeraConstraints.CompactDistrict.Observable

/-!
# The invariant order product is the manuscript's observable factor

The numeric order used by the implementation is a checked valid reverse
topological order. At its removal of vertex `i`, the remaining ancestral
set is the global prefix through `i`, whose blanket was proved to equal
the manuscript's cumulative `C_i`.

Thus its district product equals the existing `Reconstruction.observableFactor`
literally, and every other valid order has that same value. The final bridge
uses exactly the compact member/external-parent row coordinates. This avoids
proving invariance only for an unrelated auxiliary product.
-/

namespace MeraConstraints.GlobalModel.OrderingInvariance

open FiniteProbability HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem before_eq_observedUpto (i : Fin n) :
    EliminationOrder.before (i.val + 1) = observedUpto i := by
  ext j
  simp only [EliminationOrder.before, mem_ancestralExtension, Finset.notMem_empty, false_or,
    observedUpto, Finset.mem_filter, Finset.mem_univ, true_and]
  change j.val < i.val + 1 ↔ j.val ≤ i.val
  exact Nat.lt_succ_iff

/-- The canonical reverse order gives precisely the original cumulative
conditional product, without needing a Markov or positivity hypothesis. -/
theorem canonicalProduct_eq_observableFactor (p : FullAssign val → ℝ) (d : DistrictId G)
    (w : FullAssign val) :
    EliminationOrder.product (blanketWeight G val p d w) Finset.univ
        (EliminationOrder.prefixOrder n (Nat.le_refl n)) =
      Reconstruction.observableFactor G.observed val (observedDistrict G) p d w := by
  classical
  rw [EliminationOrder.fullOrder_product]
  have hterm (i : Fin n) : blanketWeight G val p d w (EliminationOrder.before (i.val + 1)) i =
      if observedDistrict G i = d then conditional p (valueEvent val w i)
        (Reconstruction.conditioningEvent G.observed val (observedDistrict G) w i) else 1 := by
    rw [blanketWeight, before_eq_observedUpto, observedUpto_blanket]
    rfl
  simp_rw [hterm]
  rw [← Finset.prod_filter]
  exact Finset.prod_subtype _ (by intro i; simp) (fun i : Fin n => conditional p (valueEvent val w i)
    (Reconstruction.conditioningEvent G.observed val (observedDistrict G) w i))

/-- Ordering invariance for the actual observed district factor used by
the manuscript and all previously checked identification/completeness results. -/
theorem orderProduct_eq_observableFactor (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalModel.KernelReconstruction.MoralGlobalMarkov G val p)
    (d : DistrictId G) (w : FullAssign val) (s : List (Fin n))
    (hs : EliminationOrder.Valid G Finset.univ s) :
    EliminationOrder.product (blanketWeight G val p d w) Finset.univ s =
      Reconstruction.observableFactor G.observed val (observedDistrict G) p d w := by
  rw [← canonicalProduct_eq_observableFactor G val p d w]
  exact blanketProduct_order_invariant G val p hpos hGlobal d w Finset.univ
    (observedAncestral_univ G) s _ hs (EliminationOrder.fullOrder_valid G)

variable [∀ i, Nonempty (val i)]

/-- Exact compact manuscript-row form of the invariant order product. -/
theorem orderProduct_eq_compact_observableFactor (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalModel.KernelReconstruction.MoralGlobalMarkov G val p)
    (d : DistrictId G) (w : FullAssign val) (s : List (Fin n))
    (hs : EliminationOrder.Valid G Finset.univ s) :
    EliminationOrder.product (blanketWeight G val p d w) Finset.univ s =
      CompactDistrict.observableFactor G.observed val (observedDistrict G) d p
        (CompactDistrict.project G.observed val (observedDistrict G) d w) := by
  rw [orderProduct_eq_observableFactor G val p hpos hGlobal d w s hs]
  exact (CompactDistrict.observableFactor_project G.observed val (observedDistrict G) d p w).symm

end MeraConstraints.GlobalModel.OrderingInvariance
