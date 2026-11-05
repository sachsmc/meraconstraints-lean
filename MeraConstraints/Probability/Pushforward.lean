import MeraConstraints.Probability.Conditional

/-!
# Events under a pushforward, marginals, and averaging over fibers

The observed distribution of a model is the pushforward of the distribution of
the response function variables along the recursive evaluation map. The
probability of an observed event is then the probability of its preimage
(`mass_pushforward`), and likewise for conditional probabilities
(`conditional_pushforward`). `pushforward_comp` shows that taking a marginal
after evaluation is the pushforward along the composite map.

`marginal` is the distribution of a subset of the observed variables, and
`marginal_eq_mass_assignmentEvent` identifies its values with probabilities of
assignment events.

`conditional_eq_of_fiberwise_mass` is the averaging step used when extra
conditioning variables are summed out: if the event `A ∩ C` has mass `t` times
the mass of `C` on every fiber of a finite variable `Z`, then the conditional
probability of `A` given `C` is `t`. The hypothesis is an equation of masses on
each fiber, including fibers of mass zero.
-/

namespace MeraConstraints.FiniteProbability

variable {α β γ : Type*} [Fintype α] [DecidableEq β]

/-- The preimage of an event `A` under `f`: the points that `f` sends into `A`. -/
def preimage (f : α → β) (A : Finset β) : Finset α :=
  Finset.univ.filter fun x => f x ∈ A

@[simp] theorem mem_preimage (f : α → β) (A : Finset β) (x : α) :
    x ∈ preimage f A ↔ f x ∈ A := by simp [preimage]

/-- The probability of an event under the pushforward is the probability of its
preimage. This holds for any real mass vector. -/
theorem mass_pushforward (f : α → β) (q : α → ℝ) (A : Finset β) :
    mass (pushforward f q) A = mass q (preimage f A) := by
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ A f q

/-- Conditional probabilities under the pushforward are conditional probabilities
of the preimages. By `mass_pushforward`, the denominator is nonzero on one side
if and only if it is on the other. -/
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

/-- Pushforwards compose: pushing forward along `f` and then `g` is the pushforward
along `g ∘ f`. -/
theorem pushforward_comp (f : α → β) (g : β → γ) (q : α → ℝ) :
    pushforward g (pushforward f q) = pushforward (g ∘ f) q := by
  funext c
  change mass (pushforward f q) (Finset.univ.filter fun b => g b = c) = _
  rw [mass_pushforward]
  simp [mass, preimage, pushforward]

section Marginals

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The marginal distribution of the observed variables in `S`. -/
def marginal (p : FullAssign val → ℝ) (S : Finset (Fin n)) :
    (∀ i : {i // i ∈ S}, val i) → ℝ :=
  pushforward (fun w => fun i => w i) p

theorem marginal_mem_stdSimplex (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (S : Finset (Fin n)) :
    marginal val p S ∈ stdSimplex ℝ (∀ i : {i // i ∈ S}, val i) :=
  pushforward_mem_stdSimplex _ p hp

/-- A value of the marginal is the probability of the event fixing those
variables. -/
theorem marginal_eq_mass_assignmentEvent (p : FullAssign val → ℝ)
    (w : FullAssign val) (S : Finset (Fin n)) :
    marginal val p S (fun i => w i) = mass p (assignmentEvent val w S) := by
  simp [marginal, pushforward, mass, assignmentEvent, funext_iff, Subtype.forall]

end Marginals

section FiberAveraging

variable {Ω B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype B] [DecidableEq B]

/-- The fiber of `Z` over `b`: the event `Z = b`. -/
def fiber (Z : Ω → B) (b : B) : Finset Ω :=
  Finset.univ.filter fun x => Z x = b

/-- The mass of an event is the sum of its masses on the fibers of a finite
variable. -/
theorem mass_eq_sum_fibers (p : Ω → ℝ) (A : Finset Ω) (Z : Ω → B) :
    mass p A = ∑ b, mass p (A ∩ fiber Z b) := by
  symm
  simpa only [mass, fiber, Finset.inter_filter, Finset.inter_univ] using
    Finset.sum_fiberwise A Z p

/-- If on every fiber the mass of `A ∩ C` is `t` times the mass of `C`, then the
conditional probability of `A` given `C` is `t`. Only `C` needs nonzero mass. -/
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
