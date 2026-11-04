import MeraConstraints.Probability.CoordinateJoin
import MeraConstraints.Probability.AssignmentPartition
import Mathlib.Data.Finset.Erase

/-!
# Conditional ratios along vertex removals

Removing a coordinate from an assignment event gives its conditional ratio.
Removing two distinct coordinates in either order has the same product by
the chain rule. This elementary identity does not assume graphical Markov;
positivity is used only to cancel the intermediate event masses.
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
