import MeraConstraints.Probability.PrefixPartition

/-!
# Summing out one variable of an assignment event

For a set `A` of observed variables and `i ∈ A`, the mass of the event fixing the
variables in `A \ {i}` is the sum, over the values `a` of `V_i`, of the mass of
the event fixing `A` with `V_i = a` (`mass_assignment_erase_eq_sum`). This holds
for any real mass function. It is used to marginalize in
`GlobalModel.AncestralKernels` and `GlobalModel.AncestralProducts`.
-/

namespace MeraConstraints.FiniteProbability

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

@[simp] theorem assignmentEvent_univ (w : FullAssign val) :
    assignmentEvent val w Finset.univ = {w} := by
  ext z
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => funext (fun i => h i trivial), fun h i _ => congrFun h i⟩

@[simp] theorem assignmentEvent_empty (w : FullAssign val) :
    assignmentEvent val w ∅ = Finset.univ := by
  simp [assignmentEvent]

theorem assignmentEvent_insert (w : FullAssign val) (S : Finset (Fin n)) (i : Fin n) :
    assignmentEvent val w (insert i S) = valueEvent val w i ∩ assignmentEvent val w S := by
  ext z
  simp only [assignmentEvent, valueEvent, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter, Finset.mem_insert]
  constructor
  · intro h
    exact ⟨h i (Or.inl rfl), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨hi, hS⟩ j (hji | hj)
    · subst j
      exact hi
    · exact hS j hj

theorem mem_assignmentEvent_update (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A)
    (w z : FullAssign val) (a : val i) :
    z ∈ assignmentEvent val (Function.update w i a) A ↔
      z ∈ assignmentEvent val w (A.erase i) ∧ z i = a := by
  classical
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
      simpa only [Function.update_of_ne hji] using h j hjA
    · simpa using h i hi
  · rintro ⟨h, ha⟩ j hj
    by_cases hji : j = i
    · subst j
      simpa using ha
    · rw [Function.update_of_ne hji]
      exact h j (Finset.mem_erase.mpr ⟨hji, hj⟩)

theorem mass_assignment_erase_eq_sum (p : FullAssign val → ℝ)
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A) (w : FullAssign val) :
    mass p (assignmentEvent val w (A.erase i)) =
      ∑ a : val i, mass p (assignmentEvent val (Function.update w i a) A) := by
  classical
  simp only [mass, assignmentEvent, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hm (a : val i) := mem_assignmentEvent_update val A i hi w z a
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  simp_rw [hm]
  exact (sum_indicator_and_eq _ (z i) (p z)).symm

end MeraConstraints.FiniteProbability
