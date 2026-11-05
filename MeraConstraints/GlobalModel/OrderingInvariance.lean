import MeraConstraints.HiddenGraph.EliminationOrder
import MeraConstraints.GlobalModel.GlobalToLocal
import MeraConstraints.Probability.RemovalConditionals

/-!
# The district factor does not depend on the ordering

The district factor is defined with an ordering of the district's members. For a
strictly positive distribution satisfying the conditional independencies implied by the
graph (`GlobalMarkov`), the factor is the same for every valid ordering. This is the
claim in Step 1 of the proof of Proposition 4 (`prop:nontrivial`) that `p^σ` is the same
for every `σ`, which the proof of Proposition 3 (`prop:complete`) uses. The distribution is not assumed to be in the
marginal model or to satisfy any district polytope constraint.

The manuscript swaps adjacent members. Here a valid order removes, one at a time, a
variable with no children in the current ancestral set, and the district product keeps
the conditional of a removed variable only if it belongs to the district. Swapping two
removals has three cases. Two members of the district commute by the chain rule. Two
variables outside it contribute one. If exactly one is in the district, the
conditional independencies show that the other is neither a member nor an external
parent of the district, so it can be dropped from the conditioning set. A graph and
algebra theorem (`EliminationOrder.products_eq`) then gives equal products for all valid
orders (`blanketProduct_order_invariant`).

Each conditional can be replaced by the conditional given its blanket in the current
set (`conditional_eq_blanket`). In forward order the blanket is the set `C_i` of
Proposition 1 (`prop:ident`).
-/

namespace MeraConstraints.GlobalModel.OrderingInvariance

open FiniteProbability HiddenGraph
open GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem conditional_eq_blanket (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hi : ObservedSink G A i) (w : FullAssign val) :
    conditional p (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      conditional p (valueEvent val w i) (assignmentEvent val w (ancestralBlanket G A i)) :=
  conditional_eq_of_subset_independent p _ _ _
    (assignmentEvent_antitone val w (ancestralBlanket_subset_erase G A i))
    (globalMarkov_ancestral_equation G val p hGlobal A hA i hi w)
    (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (A.erase i))).ne'
    (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (ancestralBlanket G A i))).ne'

/-- Let `V_i` and `V_j` both have no children in `A`, in different districts. Then `V_j`
can be dropped from the variables conditioned on in the conditional of `V_i`. -/
theorem conditional_remove_other_sink (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i j : Fin n) (hi : ObservedSink G A i) (hj : ObservedSink G A j)
    (hD : observedDistrict G i ≠ observedDistrict G j) (w : FullAssign val) :
    conditional p (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      conditional p (valueEvent val w i) (assignmentEvent val w ((A.erase i).erase j)) := by
  classical
  have hjB : j ∉ ancestralBlanket G A i := by
    intro hmem
    obtain ⟨_, h | ⟨_, l, hl, _, hjl⟩⟩ := Finset.mem_filter.mp hmem
    · exact hD h.2.symm
    · exact hj.2 l hl hjl
  have hBT : ancestralBlanket G A i ⊆ (A.erase i).erase j := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun hkj => hjB (hkj ▸ hk), ancestralBlanket_subset_erase G A i hk⟩
  apply conditional_assignment_eq_of_congr val p hpos _ _ (Finset.erase_subset _ _) i (Finset.notMem_erase _ _)
  intro v z hvz hiEq
  rw [conditional_eq_blanket G val p hpos hGlobal A hA i hi v,
    conditional_eq_blanket G val p hpos hGlobal A hA i hi z]
  have hE : valueEvent val v i = valueEvent val z i := by simp only [valueEvent, hiEq]
  rw [hE, assignmentEvent_congr_values val v z _ (fun k hk => hvz k (hBT hk))]

noncomputable def chainWeight (p : FullAssign val → ℝ) (d : DistrictId G) (w : FullAssign val)
    (A : Finset (Fin n)) (i : Fin n) : ℝ :=
  if observedDistrict G i = d then conditional p (valueEvent val w i) (assignmentEvent val w (A.erase i)) else 1

noncomputable def blanketWeight (p : FullAssign val → ℝ) (d : DistrictId G) (w : FullAssign val)
    (A : Finset (Fin n)) (i : Fin n) : ℝ :=
  if observedDistrict G i = d then conditional p (valueEvent val w i) (assignmentEvent val w (ancestralBlanket G A i)) else 1

/-- Removing two variables with no children in either order gives the same product of
weights (`EliminationOrder.Diamonds`). -/
theorem chainWeight_diamonds (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val) :
    EliminationOrder.Diamonds G (chainWeight G val p d w) := by
  intro A hA i j hi hj hne
  by_cases hid : observedDistrict G i = d <;> by_cases hjd : observedDistrict G j = d
  · simp only [chainWeight, if_pos hid, if_pos hjd]
    exact conditional_remove_pair_comm val p hpos w A i j hi.1 hj.1 hne
  · simp only [chainWeight, if_pos hid, if_neg hjd, mul_one, one_mul]
    have hD : observedDistrict G i ≠ observedDistrict G j := fun he => hjd (he.symm.trans hid)
    simpa only [EliminationOrder.erase_twice_comm] using conditional_remove_other_sink G val p hpos hGlobal A hA i j hi hj hD w
  · simp only [chainWeight, if_neg hid, if_pos hjd, mul_one, one_mul]
    have hD : observedDistrict G j ≠ observedDistrict G i := fun he => hid (he.symm.trans hjd)
    simpa only [EliminationOrder.erase_twice_comm] using (conditional_remove_other_sink G val p hpos hGlobal A hA j i hj hi hD w).symm
  · simp only [chainWeight, if_neg hid, if_neg hjd, mul_one]

theorem chainProduct_eq_blanketProduct (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (s : List (Fin n)) (hs : EliminationOrder.Valid G A s) :
    EliminationOrder.product (chainWeight G val p d w) A s =
      EliminationOrder.product (blanketWeight G val p d w) A s := by
  induction s generalizing A with
  | nil => rfl
  | cons i s ih =>
    rw [EliminationOrder.product, EliminationOrder.product]
    congr 1
    · by_cases hid : observedDistrict G i = d
      · simp only [chainWeight, blanketWeight, if_pos hid]
        exact conditional_eq_blanket G val p hpos hGlobal A hA i hs.1 w
      · simp only [chainWeight, blanketWeight, if_neg hid]
    · exact ih (A.erase i) (observedAncestral_erase G A hA i hs.1) hs.2

/-- The retained product of district `d` over an ancestral set `A` is the same for
every valid removal order of `A`. -/
theorem blanketProduct_order_invariant (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : GlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (s t : List (Fin n))
    (hs : EliminationOrder.Valid G A s) (ht : EliminationOrder.Valid G A t) :
    EliminationOrder.product (blanketWeight G val p d w) A s =
      EliminationOrder.product (blanketWeight G val p d w) A t := by
  rw [← chainProduct_eq_blanketProduct G val p hpos hGlobal d w A hA s hs,
    ← chainProduct_eq_blanketProduct G val p hpos hGlobal d w A hA t ht]
  exact EliminationOrder.products_eq G _ (chainWeight_diamonds G val p hpos hGlobal d w) A hA s t hs ht

end MeraConstraints.GlobalModel.OrderingInvariance
