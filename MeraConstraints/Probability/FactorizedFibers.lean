import MeraConstraints.Probability.Pushforward

/-!
# Conditional independence from a factorization over fibers

Let `L` and `R` be finite-valued maps and `C` an event. Suppose the mass of `C`
on each joint fiber `{L = a, R = b}` is a product `f a * g b`. Then the mass of
`C` on any rectangle `{L ∈ S, R ∈ T}` is `(∑ f over S) * (∑ g over T)`, and this
gives the cross-product equation for conditional independence of `L` and `R`
given `C` (`condIndependent_of_factorized_fibers`). The argument is finite
algebra and needs no normalization or positivity.

It is used in `CutFactorization`, where the factorization comes from a cut of
the graph.
-/

namespace MeraConstraints.FiniteProbability

variable {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def rectangleEvent (L : Ω → α) (R : Ω → β) (S : Finset α) (T : Finset β) : Finset Ω :=
  Finset.univ.filter fun z => L z ∈ S ∧ R z ∈ T

omit [Fintype α] [Fintype β] in
/-- A rectangle event contains either all of a joint fiber or none of it. -/
theorem rectangle_inter_fiber (C : Finset Ω) (L : Ω → α) (R : Ω → β)
    (S : Finset α) (T : Finset β) (a : α) (b : β) :
    (C ∩ rectangleEvent L R S T) ∩ fiber (fun z => (L z, R z)) (a, b) =
      if a ∈ S ∧ b ∈ T then C ∩ fiber (fun z => (L z, R z)) (a, b) else ∅ := by
  classical
  by_cases h : a ∈ S ∧ b ∈ T
  · rw [if_pos h]
    ext z
    simp only [rectangleEvent, fiber, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hzC, _⟩, hz⟩
      exact ⟨hzC, hz⟩
    · rintro ⟨hzC, hz⟩
      have hL : L z = a := congrArg Prod.fst hz
      have hR : R z = b := congrArg Prod.snd hz
      exact ⟨⟨hzC, by rw [hL, hR]; exact h⟩, hz⟩
  · rw [if_neg h]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzRect, hfiber⟩ := Finset.mem_inter.mp hz
    have hrect := (Finset.mem_inter.mp hzRect).2
    have hab : (L z, R z) = (a, b) := (Finset.mem_filter.mp hfiber).2
    have hL : L z = a := congrArg Prod.fst hab
    have hR : R z = b := congrArg Prod.snd hab
    have hmem := (Finset.mem_filter.mp hrect).2
    rw [hL, hR] at hmem
    exact h hmem

theorem mass_rectangle_of_factorized_fibers (p : Ω → ℝ) (C : Finset Ω)
    (L : Ω → α) (R : Ω → β) (f : α → ℝ) (g : β → ℝ)
    (hfact : ∀ a b, mass p (C ∩ fiber (fun z => (L z, R z)) (a, b)) = f a * g b)
    (S : Finset α) (T : Finset β) :
    mass p (C ∩ rectangleEvent L R S T) = (∑ a ∈ S, f a) * (∑ b ∈ T, g b) := by
  classical
  rw [mass_eq_sum_fibers p _ (fun z => (L z, R z)), Fintype.sum_prod_type]
  simp_rw [rectangle_inter_fiber]
  have hm (a : α) (b : β) :
      mass p (if a ∈ S ∧ b ∈ T then C ∩ fiber (fun z => (L z, R z)) (a, b) else ∅) =
        (if a ∈ S then f a else 0) * (if b ∈ T then g b else 0) := by
    by_cases h : a ∈ S ∧ b ∈ T
    · rw [if_pos h, if_pos h.1, if_pos h.2]
      exact hfact a b
    · rw [if_neg h]
      have hz : mass p ∅ = 0 := by simp [mass]
      rw [hz]
      by_cases ha : a ∈ S
      · have hb : b ∉ T := fun hb => h ⟨ha, hb⟩
        rw [if_neg hb, mul_zero]
      · rw [if_neg ha, zero_mul]
  simp_rw [hm]
  rw [← Finset.sum_mul_sum]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- If the mass of `C` on each joint fiber of `L` and `R` is `f a * g b`, then any
event determined by `L` and any event determined by `R` are conditionally
independent given `C`. -/
theorem condIndependent_of_factorized_fibers (p : Ω → ℝ) (C : Finset Ω)
    (L : Ω → α) (R : Ω → β) (f : α → ℝ) (g : β → ℝ)
    (hfact : ∀ a b, mass p (C ∩ fiber (fun z => (L z, R z)) (a, b)) = f a * g b)
    (S : Finset α) (T : Finset β) :
    CondIndependent p (preimage L S) (preimage R T) C := by
  classical
  have hAB : (preimage L S ∩ preimage R T) ∩ C = C ∩ rectangleEvent L R S T := by
    ext z
    simp [preimage, rectangleEvent, and_left_comm, and_comm]
  have hA : preimage L S ∩ C = C ∩ rectangleEvent L R S Finset.univ := by
    ext z
    simp [preimage, rectangleEvent, and_comm]
  have hB : preimage R T ∩ C = C ∩ rectangleEvent L R Finset.univ T := by
    ext z
    simp [preimage, rectangleEvent, and_comm]
  have hC : C = C ∩ rectangleEvent L R Finset.univ Finset.univ := by
    ext z
    simp [rectangleEvent]
  change mass p ((preimage L S ∩ preimage R T) ∩ C) * mass p C =
    mass p (preimage L S ∩ C) * mass p (preimage R T ∩ C)
  rw [hAB, hA, hB]
  conv_lhs => rhs; rw [hC]
  simp_rw [mass_rectangle_of_factorized_fibers p C L R f g hfact]
  ring

end MeraConstraints.FiniteProbability
