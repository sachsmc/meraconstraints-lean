import MeraConstraints.GlobalModel.CanonicalProduct
import MeraConstraints.HiddenGraph.SelectedOrder

/-!
# Retained district products

Let `A` be a set of observed variables that contains its ancestors, and `d` a
district. `ancestralProduct p d A w` is the product, over the variables of `A` in a
valid removal order, of the conditionals of the members of `d`, each given its
blanket in the set remaining when it is removed. For `A` the set of all variables it
is the district factor (`ancestralProduct_univ`). It depends only on the members of
`d` in `A` and their external parents (`ancestralProduct_congr`).

Removing a variable `V` with no children in `A` multiplies in its conditional when
`V` belongs to `d` (`ancestralProduct_remove`), and summing over `V` removes that
factor (`sum_ancestralProduct_sink`). This is the computation in Step 1 of the proof
of Proposition 4 (`prop:nontrivial`), where summing over the last members of a
district leaves the product over the earlier ones. The results assume a strictly
positive distribution satisfying the conditional independencies implied by the graph
(`GlobalMarkov`), and nothing else.
-/

namespace MeraConstraints.GlobalModel.OrderingInvariance

open FiniteProbability HiddenGraph
open GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- For any valid removal order, the retained product of district `d` over `A` depends
only on the members of `d` in `A` and their external parents. -/
theorem blanketProduct_congr (p : FullAssign val → ℝ) (d : DistrictId G)
    (A : Finset (Fin n)) (s : List (Fin n)) (hs : EliminationOrder.Valid G A s)
    (w v : FullAssign val)
    (hm : ∀ j ∈ A, observedDistrict G j = d → w j = v j)
    (hp : ∀ j ∈ A, observedDistrict G j = d →
      ∀ l ∈ G.observed.parents j, observedDistrict G l ≠ d → w l = v l) :
    EliminationOrder.product (blanketWeight G val p d w) A s =
      EliminationOrder.product (blanketWeight G val p d v) A s := by
  induction s generalizing A with
  | nil => rfl
  | cons i s ih =>
    rw [EliminationOrder.product, EliminationOrder.product]
    congr 1
    · by_cases hid : observedDistrict G i = d
      · simp only [blanketWeight, if_pos hid]
        have hiEq := hm i hs.1.1 hid
        have hb : assignmentEvent val w (ancestralBlanket G A i) =
            assignmentEvent val v (ancestralBlanket G A i) := by
          apply assignmentEvent_congr_values
          intro j hj
          obtain ⟨hjA, h | ⟨hne, l, hl, hld, hjl⟩⟩ := Finset.mem_filter.mp hj
          · exact hm j hjA (h.2.trans hid)
          · exact hp l hl (hld.trans hid) j hjl (by simpa [← hid] using hne)
        simp only [valueEvent, hiEq, hb]
      · simp only [blanketWeight, if_neg hid]
    · exact ih (A.erase i) hs.2
        (fun j hj => hm j (Finset.mem_erase.mp hj).2)
        (fun j hj => hp j (Finset.mem_erase.mp hj).2)

noncomputable def ancestralProduct (p : FullAssign val → ℝ) (d : DistrictId G)
    (A : Finset (Fin n)) (w : FullAssign val) : ℝ :=
  EliminationOrder.product (blanketWeight G val p d w) A (EliminationOrder.selectedOrder G A)

theorem ancestralProduct_empty (p : FullAssign val → ℝ) (d : DistrictId G) (w : FullAssign val) :
    ancestralProduct G val p d ∅ w = 1 :=
  EliminationOrder.product_empty G _ _ (EliminationOrder.selectedOrder_valid G ∅)

theorem ancestralProduct_congr (p : FullAssign val → ℝ) (d : DistrictId G)
    (A : Finset (Fin n)) (w v : FullAssign val)
    (hm : ∀ j ∈ A, observedDistrict G j = d → w j = v j)
    (hp : ∀ j ∈ A, observedDistrict G j = d →
      ∀ l ∈ G.observed.parents j, observedDistrict G l ≠ d → w l = v l) :
    ancestralProduct G val p d A w = ancestralProduct G val p d A v :=
  blanketProduct_congr G val p d A _ (EliminationOrder.selectedOrder_valid G A) w v hm hp

theorem ancestralProduct_remove (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (d : DistrictId G)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (i : Fin n)
    (hi : ObservedSink G A i) (w : FullAssign val) :
    ancestralProduct G val p d A w = blanketWeight G val p d w A i *
      ancestralProduct G val p d (A.erase i) w := by
  exact blanketProduct_order_invariant G val p hpos hGlobal d w A hA _
    (i :: EliminationOrder.selectedOrder G (A.erase i))
    (EliminationOrder.selectedOrder_valid G A)
    ⟨hi, EliminationOrder.selectedOrder_valid G (A.erase i)⟩

theorem ancestralProduct_univ (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val) :
    ancestralProduct G val p d Finset.univ w =
      Reconstruction.districtFactor G.observed val (observedDistrict G) p d w :=
  orderProduct_eq_districtFactor G val p hpos hGlobal d w _
    (EliminationOrder.selectedOrder_valid G Finset.univ)

/-- Changing the value of a variable `V_i` with no children in `A` does not change
the product over `A` without `V_i`. -/
theorem ancestralProduct_update_sink (p : FullAssign val → ℝ) (d : DistrictId G)
    (A : Finset (Fin n)) (i : Fin n) (hi : ObservedSink G A i)
    (w : FullAssign val) (a : val i) :
    ancestralProduct G val p d (A.erase i) (Function.update w i a) =
      ancestralProduct G val p d (A.erase i) w := by
  apply ancestralProduct_congr
  · intro j hj _
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  · intro j hj _ l hlj _
    have hli : l ≠ i := by
      intro he
      subst l
      exact hi.2 j (Finset.mem_erase.mp hj).2 hlj
    exact Function.update_of_ne hli _ _

theorem sum_conditional_remove (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A) (w : FullAssign val) :
    (∑ a : val i, conditional p (valueEvent val (Function.update w i a) i)
      (assignmentEvent val (Function.update w i a) (A.erase i))) = 1 := by
  have he (a : val i) : assignmentEvent val (Function.update w i a) (A.erase i) =
      assignmentEvent val w (A.erase i) :=
    assignmentEvent_congr_values val _ _ _ (fun j hj =>
      Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _)
  simp_rw [conditional_remove_ratio val p _ A i hi, he]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← mass_assignment_erase_eq_sum val p A i hi w]
  exact mul_inv_cancel₀ (mass_pos_of_mem hpos (self_mem_assignmentEvent val w _)).ne'

/-- Summing over a member `V_i` of `d` with no children in `A` removes its factor from
the retained product of its own district. -/
theorem sum_ancestralProduct_sink (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hi : ObservedSink G A i) (w : FullAssign val) :
    (∑ a : val i, ancestralProduct G val p (observedDistrict G i) A (Function.update w i a)) =
      ancestralProduct G val p (observedDistrict G i) (A.erase i) w := by
  simp_rw [ancestralProduct_remove G val p hpos hGlobal _ A hA i hi,
    ancestralProduct_update_sink G val p _ A i hi w]
  simp only [blanketWeight, ite_true]
  simp_rw [← conditional_eq_blanket G val p hpos hGlobal A hA i hi]
  rw [← Finset.sum_mul, sum_conditional_remove val p hpos A i hi.1 w, one_mul]

end MeraConstraints.GlobalModel.OrderingInvariance
