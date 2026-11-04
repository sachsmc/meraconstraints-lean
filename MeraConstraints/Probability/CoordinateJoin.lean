import MeraConstraints.Probability.CutFactorization

/-!
# Recombining conditioned coordinate events

A graph separation states independence from coordinates outside a blanket.
The local Markov equation assigns all other retained coordinates, including
that blanket. Adding the conditioning coordinates to the assigned event
preserves the same cross-product equation, with no support assumption.
-/

namespace MeraConstraints.FiniteProbability

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem assignmentEvent_union (w : FullAssign val) (S T : Finset (Fin n)) :
    assignmentEvent val w (S ∪ T) = assignmentEvent val w S ∩ assignmentEvent val w T := by
  ext z
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_union_left _ hj), fun j hj => h j (Finset.mem_union_right _ hj)⟩
  · rintro ⟨hS, hT⟩ j hj
    rcases Finset.mem_union.mp hj with hjS | hjT
    · exact hS j hjS
    · exact hT j hjT

@[simp] theorem assignmentEvent_singleton (w : FullAssign val) (i : Fin n) :
    assignmentEvent val w {i} = valueEvent val w i := by
  ext z
  simp [assignmentEvent, valueEvent]

theorem coordinateCI_join_conditioning (p : FullAssign val → ℝ) (X Y Z : Finset (Fin n))
    (h : CoordinateCI val p X Y Z) : CoordinateCI val p X (Y ∪ Z) Z := by
  intro w
  rw [assignmentEvent_union]
  simpa only [CondIndependent, Finset.inter_assoc, Finset.inter_self] using h w

end MeraConstraints.FiniteProbability
