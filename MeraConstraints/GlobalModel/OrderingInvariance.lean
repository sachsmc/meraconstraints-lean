import MeraConstraints.HiddenGraph.EliminationOrder
import MeraConstraints.GlobalModel.GlobalToLocal
import MeraConstraints.Probability.RemovalConditionals

/-!
# Ordering invariance from graphical independencies

An observed law here is arbitrary and strictly positive, with the actual
global graphical Markov predicate. It is not assumed to be an original SCM
law or to satisfy any district polytope constraints.

Each reverse topological order successively removes ancestral sinks. Its
district product retains the conditional factor only when that sink belongs
to the specified district. The key two-step diamond has three cases. Two
members of that district commute by the ordinary chain rule. Two vertices
outside it contribute one. If exactly one belongs, the global Markov property
removes the other sink from its conditioning set: it is neither a member nor
an external parent of the retained district. The graph/algebra order theorem
then proves equality for all valid elimination orders.

Replacing each conditional by its ancestral blanket is proved from global
Markov, on positive support. In forward order this blanket is precisely the
earlier district members and their cumulative external parents, as in the
manuscript's `C_i`. No ordering-invariance conclusion is a hypothesis.
-/

namespace MeraConstraints.GlobalModel.OrderingInvariance

open FiniteProbability HiddenGraph
open GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem conditional_eq_blanket (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hi : ObservedSink G A i) (w : FullAssign val) :
    conditional p (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      conditional p (valueEvent val w i) (assignmentEvent val w (ancestralBlanket G A i)) :=
  conditional_eq_of_subset_independent p _ _ _
    (assignmentEvent_antitone val w (ancestralBlanket_subset_erase G A i))
    (moralGlobalMarkov_ancestral_equation G val p hGlobal A hA i hi w)
    (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (A.erase i))).ne'
    (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (ancestralBlanket G A i))).ne'

/-- A sink in another district can be dropped from the current sink's
conditioning set. Finite averaging proves the reduction on positive support. -/
theorem conditional_remove_other_sink (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
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

/-- The district's conditional weights satisfy every available-sink diamond. -/
theorem chainWeight_diamonds (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val) :
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
    (hGlobal : MoralGlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val)
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

/-- The manuscript's cumulative-conditioning product is invariant under
every valid reverse topological order of the same ancestral vertex set. -/
theorem blanketProduct_order_invariant (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (d : DistrictId G) (w : FullAssign val)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (s t : List (Fin n))
    (hs : EliminationOrder.Valid G A s) (ht : EliminationOrder.Valid G A t) :
    EliminationOrder.product (blanketWeight G val p d w) A s =
      EliminationOrder.product (blanketWeight G val p d w) A t := by
  rw [← chainProduct_eq_blanketProduct G val p hpos hGlobal d w A hA s hs,
    ← chainProduct_eq_blanketProduct G val p hpos hGlobal d w A hA t ht]
  exact EliminationOrder.products_eq G _ (chainWeight_diamonds G val p hpos hGlobal d w) A hA s t hs ht

end MeraConstraints.GlobalModel.OrderingInvariance
