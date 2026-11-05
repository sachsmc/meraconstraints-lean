import MeraConstraints.Probability.Conditional

/-!
# Summing over the next observed value

The mass of the event that the variables before `V_i` take given values is the
sum, over the values `a` of `V_i`, of the mass of the event that the variables up
to and including `V_i` take those values with `V_i = a`
(`mass_prefix_eq_sum_next`). This holds for any real mass function. It is used
in `GlobalModel.KernelReconstruction`.
-/

namespace MeraConstraints.FiniteProbability

/-- Summing the indicator of `P ∧ a = b` over `b` leaves the indicator of `P`. -/
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

/-- The mass of the prefix event before `V_i` is the sum over the values of `V_i`
of the masses of the prefix events through `V_i`. -/
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
