import MeraConstraints.Probability.Conditional

/-!
# Marginalization, event pullbacks, and averaging over finite fibers

A structural model's observable law is the pushforward of its latent law
along recursive evaluation. To identify a supported observable conditional,
one therefore needs the probabilities of entire assignment events, not only
the atomic formula `p = B r`. `mass_pushforward` transports any finite observed
event back to the corresponding latent event. `pushforward_comp` shows that
observing a coordinate margin can be done before or after evaluation.

The second part provides literal observed-coordinate marginals. Their
normalization follows from the existing finite pushforward theorem, and
their values agree with `assignmentEvent` probabilities from the conditional
chapter. These are probability identities; no graph Markov assertion is
included in their hypotheses or conclusions.

Finally, `conditional_eq_of_fiberwise_mass` proves the elementary averaging
step used when extra predecessors are summed out: if each fiber contributes
the same conditional ratio, their union contributes that ratio. The premise
is an equation of masses even on zero-mass fibers, so there is no implicit
division by zero in the boundary case.
-/

namespace MeraConstraints.FiniteProbability

variable {α β γ : Type*} [Fintype α] [DecidableEq β]

/-- Pull back a finite observed event to the finite latent state space. -/
def preimage (f : α → β) (A : Finset β) : Finset α :=
  Finset.univ.filter fun x => f x ∈ A

@[simp] theorem mem_preimage (f : α → β) (A : Finset β) (x : α) :
    x ∈ preimage f A ↔ f x ∈ A := by simp [preimage]

/-- The probability of an observed event is the probability of its latent
preimage. This holds for any mass vector, without positivity assumptions. -/
theorem mass_pushforward (f : α → β) (q : α → ℝ) (A : Finset β) :
    mass (pushforward f q) A = mass q (preimage f A) := by
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ A f q

/-- Conditional event formulas transport along the same observation map.
For statistical interpretation, a nonzero denominator is still needed on
either side; `mass_pushforward` proves those support conditions equivalent. -/
theorem conditional_pushforward [DecidableEq α] (f : α → β) (q : α → ℝ)
    (A C : Finset β) :
    conditional (pushforward f q) A C = conditional q (preimage f A) (preimage f C) := by
  unfold conditional
  rw [mass_pushforward, mass_pushforward]
  congr 1
  congr 1
  ext x
  simp

variable [Fintype β] [DecidableEq γ]

/-- Pushforwards compose: evaluation followed by marginalization is the
pushforward along the composite observation map. -/
theorem pushforward_comp (f : α → β) (g : β → γ) (q : α → ℝ) :
    pushforward g (pushforward f q) = pushforward (g ∘ f) q := by
  funext c
  change mass (pushforward f q) (Finset.univ.filter fun b => g b = c) = _
  rw [mass_pushforward]
  simp [mass, preimage, pushforward]

section Marginals

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Observable marginal distribution on a named set of observed coordinates. -/
def marginal (p : FullAssign val → ℝ) (S : Finset (Fin n)) :
    (∀ i : {i // i ∈ S}, val i) → ℝ :=
  pushforward (fun w => fun i => w i) p

theorem marginal_mem_stdSimplex (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (S : Finset (Fin n)) :
    marginal val p S ∈ stdSimplex ℝ (∀ i : {i // i ∈ S}, val i) :=
  pushforward_mem_stdSimplex _ p hp

/-- A marginal value is the probability of specifying those coordinates. -/
theorem marginal_eq_mass_assignmentEvent (p : FullAssign val → ℝ)
    (w : FullAssign val) (S : Finset (Fin n)) :
    marginal val p S (fun i => w i) = mass p (assignmentEvent val w S) := by
  simp [marginal, pushforward, mass, assignmentEvent, funext_iff, Subtype.forall]

end Marginals

section FiberAveraging

variable {Ω B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype B] [DecidableEq B]

/-- Assignment event of a finite-valued random variable. -/
def fiber (Z : Ω → B) (b : B) : Finset Ω :=
  Finset.univ.filter fun x => Z x = b

/-- Decompose an event mass into the disjoint fibers of a finite variable. -/
theorem mass_eq_sum_fibers (p : Ω → ℝ) (A : Finset Ω) (Z : Ω → B) :
    mass p A = ∑ b, mass p (A ∩ fiber Z b) := by
  symm
  simpa only [mass, fiber, Finset.inter_filter, Finset.inter_univ] using
    Finset.sum_fiberwise A Z p

/-- Summing equal conditional ratios over a fiber partition preserves the
ratio. Only the final conditioning event must have nonzero mass. -/
theorem conditional_eq_of_fiberwise_mass (p : Ω → ℝ) (A C : Finset Ω)
    (Z : Ω → B) (t : ℝ) (hC : mass p C ≠ 0)
    (hf : ∀ b, mass p ((A ∩ C) ∩ fiber Z b) = t * mass p (C ∩ fiber Z b)) :
    conditional p A C = t := by
  apply (div_eq_iff hC).2
  calc
    mass p (A ∩ C) = ∑ b, mass p ((A ∩ C) ∩ fiber Z b) := mass_eq_sum_fibers p _ Z
    _ = ∑ b, t * mass p (C ∩ fiber Z b) := Finset.sum_congr rfl fun b _ => hf b
    _ = t * ∑ b, mass p (C ∩ fiber Z b) := (Finset.mul_sum _ _ _).symm
    _ = t * mass p C := by rw [← mass_eq_sum_fibers p C Z]

end FiberAveraging
end MeraConstraints.FiniteProbability
