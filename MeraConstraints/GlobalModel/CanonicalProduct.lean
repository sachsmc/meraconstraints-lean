import MeraConstraints.GlobalModel.OrderingInvariance
import MeraConstraints.HiddenGraph.CanonicalOrder
import MeraConstraints.CompactDistrict.Observable

/-!
# The order product is the district factor

Removing the observed variables in reverse numeric order is a valid removal order.
When `V_i` is removed, the remaining set is the variables up to `V_i`, and the
blanket of `V_i` in it is `C_i` (`HiddenGraph.observedUpto_blanket`). So the product
of the district's conditionals for this order is `Reconstruction.districtFactor`, the
product in Proposition 1 (`prop:ident`) (`canonicalProduct_eq_districtFactor`).

Every other valid removal order gives the same value for a strictly positive
distribution satisfying the conditional independencies implied by the graph
(`orderProduct_eq_districtFactor`). This is the ordering independence used in the
proof of Proposition 3 (`prop:complete`), via Step 1 of the proof of Proposition 4.
`orderProduct_eq_compact_districtFactor` states it with the rows `(v₁, v₂)` of the
matrix `B`.
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

/-- Removing the variables in reverse numeric order gives
`Reconstruction.districtFactor`, the product in Proposition 1 (`prop:ident`). No
hypothesis on `p` is needed. -/
theorem canonicalProduct_eq_districtFactor (p : FullAssign val → ℝ) (d : DistrictId G)
    (w : FullAssign val) :
    EliminationOrder.product (blanketWeight G val p d w) Finset.univ
        (EliminationOrder.prefixOrder n (Nat.le_refl n)) =
      Reconstruction.districtFactor G.observed val (observedDistrict G) p d w := by
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

/-- For a strictly positive distribution satisfying `GlobalMarkov`, every valid
removal order gives the district factor. -/
theorem orderProduct_eq_districtFactor (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalModel.KernelReconstruction.GlobalMarkov G val p)
    (d : DistrictId G) (w : FullAssign val) (s : List (Fin n))
    (hs : EliminationOrder.Valid G Finset.univ s) :
    EliminationOrder.product (blanketWeight G val p d w) Finset.univ s =
      Reconstruction.districtFactor G.observed val (observedDistrict G) p d w := by
  rw [← canonicalProduct_eq_districtFactor G val p d w]
  exact blanketProduct_order_invariant G val p hpos hGlobal d w Finset.univ
    (observedAncestral_univ G) s _ hs (EliminationOrder.fullOrder_valid G)

variable [∀ i, Nonempty (val i)]

/-- The same, with the district factor indexed by the rows `(v₁, v₂)` of the matrix `B`. -/
theorem orderProduct_eq_compact_districtFactor (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalModel.KernelReconstruction.GlobalMarkov G val p)
    (d : DistrictId G) (w : FullAssign val) (s : List (Fin n))
    (hs : EliminationOrder.Valid G Finset.univ s) :
    EliminationOrder.product (blanketWeight G val p d w) Finset.univ s =
      CompactDistrict.districtFactor G.observed val (observedDistrict G) d p
        (CompactDistrict.project G.observed val (observedDistrict G) d w) := by
  rw [orderProduct_eq_districtFactor G val p hpos hGlobal d w s hs]
  exact (CompactDistrict.districtFactor_project G.observed val (observedDistrict G) d p w).symm

end MeraConstraints.GlobalModel.OrderingInvariance
