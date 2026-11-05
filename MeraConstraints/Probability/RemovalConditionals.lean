import MeraConstraints.Probability.CoordinateJoin
import MeraConstraints.Probability.AssignmentPartition
import Mathlib.Data.Finset.Erase

/-!
# Removing observed variables one at a time

For a set `A` of observed variables and `i ∈ A`, the conditional probability of
`V_i` given the variables in `A \ {i}` is the ratio of the mass of the event
fixing `A` to that of the event fixing `A \ {i}` (`conditional_remove_ratio`).
Removing two distinct variables `i` and `j` from `A` gives the same product of
conditional probabilities in either order (`conditional_remove_pair_comm`). This
is the chain rule and does not use the graph. Positivity is used only to cancel
the mass of the intermediate event.

These are used in `GlobalModel.OrderingInvariance`, to show that the district
factor does not depend on the topological ordering used to compute it.
-/

namespace MeraConstraints.FiniteProbability

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem assignmentEvent_congr_values (w v : FullAssign val) (S : Finset (Fin n))
    (h : ∀ j ∈ S, w j = v j) : assignmentEvent val w S = assignmentEvent val v S := by
  ext z
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz j hj
    exact (hz j hj).trans (h j hj)
  · intro hz j hj
    exact (hz j hj).trans (h j hj).symm

theorem conditional_remove_ratio (p : FullAssign val → ℝ) (w : FullAssign val)
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A) :
    conditional p (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      mass p (assignmentEvent val w A) / mass p (assignmentEvent val w (A.erase i)) := by
  rw [conditional, ← assignmentEvent_insert, Finset.insert_erase hi]

theorem conditional_remove_pair_comm (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (w : FullAssign val) (A : Finset (Fin n)) (i j : Fin n) (hi : i ∈ A) (hj : j ∈ A) (hne : i ≠ j) :
    conditional p (valueEvent val w i) (assignmentEvent val w (A.erase i)) *
        conditional p (valueEvent val w j) (assignmentEvent val w ((A.erase i).erase j)) =
      conditional p (valueEvent val w j) (assignmentEvent val w (A.erase j)) *
        conditional p (valueEvent val w i) (assignmentEvent val w ((A.erase j).erase i)) := by
  have hj' : j ∈ A.erase i := Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩
  have hi' : i ∈ A.erase j := Finset.mem_erase.mpr ⟨hne, hi⟩
  have hcomm : (A.erase i).erase j = (A.erase j).erase i := by
    ext k
    simp [Finset.mem_erase, and_left_comm]
  rw [conditional_remove_ratio val p w A i hi,
    conditional_remove_ratio val p w (A.erase i) j hj',
    conditional_remove_ratio val p w A j hj,
    conditional_remove_ratio val p w (A.erase j) i hi']
  rw [div_mul_div_cancel₀ (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (A.erase i))).ne',
    div_mul_div_cancel₀ (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (A.erase j))).ne',
    hcomm]

end MeraConstraints.FiniteProbability
