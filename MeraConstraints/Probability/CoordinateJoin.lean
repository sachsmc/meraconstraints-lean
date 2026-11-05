import MeraConstraints.Probability.CutFactorization

/-!
# Adding the conditioning set to a conditional independence

If `X` is conditionally independent of `Y` given `Z`, then `X` is conditionally
independent of `Y ∪ Z` given `Z` (`coordinateCI_join_conditioning`). This holds
for any real mass function. It is used in `GlobalModel.GlobalToLocal`: a
separation statement leaves out the conditioning variables, while the local
Markov equation includes them in the second event.
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
