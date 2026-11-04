import MeraConstraints.Probability.Conditional

/-!
# Partitioning a prefix by the next observed value

The next-value events form a disjoint partition of a fixed observed prefix.
The resulting summation identity holds for arbitrary real masses, without
normalization, positivity or a probabilistic factorization assumption.
-/

namespace MeraConstraints.FiniteProbability

/-- Summing an indicator over the singled-out value preserves its other condition. -/
theorem sum_indicator_and_eq {α : Type*} [Fintype α] [DecidableEq α]
    (P : Prop) [Decidable P] (a : α) (r : ℝ) :
    (∑ b : α, if P ∧ a = b then r else 0) = if P then r else 0 := by
  classical
  by_cases h : P <;> simp [h]

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

theorem mem_prefixEvent_update_succ (w z : FullAssign val) (i : Fin n) (a : val i) :
    z ∈ prefixEvent val (Function.update w i a) (i.val + 1) ↔
      z ∈ prefixEvent val w i.val ∧ z i = a := by
  classical
  simp only [prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := fun he => by subst j; omega
      simpa only [Function.update_of_ne hji] using h j (by omega)
    · simpa using h i (Nat.lt_succ_self _)
  · rintro ⟨h, ha⟩ j hj
    by_cases hji : j = i
    · subst j
      simpa using ha
    · rw [Function.update_of_ne hji]
      exact h j (by have hn : j.val ≠ i.val := fun he => hji (Fin.ext he); omega)

/-- Sum over all possible next values, with no support requirement. -/
theorem mass_prefix_eq_sum_next (p : FullAssign val → ℝ) (w : FullAssign val) (i : Fin n) :
    mass p (prefixEvent val w i.val) =
      ∑ a : val i, mass p (prefixEvent val (Function.update w i a) (i.val + 1)) := by
  classical
  simp only [mass, prefixEvent, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hm (a : val i) := mem_prefixEvent_update_succ val w z i a
  simp only [prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  simp_rw [hm]
  exact (sum_indicator_and_eq _ (z i) (p z)).symm

end MeraConstraints.FiniteProbability
