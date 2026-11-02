import MeraConstraints.Probability.Finite
import MeraConstraints.SCM.Basic
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Observable probabilities, conditioning, and the ordered chain rule

The manuscript assumes strict positivity in its Notation subsection. Thus
its conditional probabilities in Proposition `prop:ident` have positive
denominators. This chapter makes that assumption visible rather than using
Lean's totalized division by zero to give unsupported conditionals a meaning.

`mass` and `conditional` are the ordinary finite event formulas. Conditional
independence is expressed by the cross-product equation, which itself makes
sense even at zero probability. The factor-replacement theorem explicitly
requires the relevant conditioning events to have nonzero probability.

For an observed assignment indexed by `Fin n`, `prefixEvent w k` records
the first `k` values. The ordered chain rule proves, from finite probability
algebra, that the full assignment mass is the product of its successive
conditional factors. The final factor-replacement theorem allows precisely
the step in Appendix C where `pre(V)` is replaced by the smaller cumulative
external-parent conditioning set `C_V`. Graph separation and the claim that
a model entails that independence are separate proof obligations.
-/

namespace MeraConstraints.FiniteProbability

variable {Ω : Type*} [DecidableEq Ω]

/-- Probability of a finite event under a probability-mass vector. -/
def mass (p : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ x ∈ A, p x

/-- The standing strict-positivity assumption concerns every complete
observed assignment, not every latent state or every response profile. -/
def StrictlyPositive (p : Ω → ℝ) : Prop := ∀ x, 0 < p x

/-- Atomic support of a finite probability-mass vector. -/
noncomputable def support [Fintype Ω] (p : Ω → ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun x => p x ≠ 0

omit [DecidableEq Ω] in
@[simp] theorem mem_support [Fintype Ω] (p : Ω → ℝ) (x : Ω) :
    x ∈ support p ↔ p x ≠ 0 := by
  classical
  simp [support]

/-- Ordinary finite conditional probability. Theorems interpreting this as
an observed conditional always state a nonzero conditioning-mass hypothesis. -/
noncomputable def conditional (p : Ω → ℝ) (A B : Finset Ω) : ℝ :=
  mass p (A ∩ B) / mass p B

omit [DecidableEq Ω] in
@[simp] theorem mass_univ [Fintype Ω] (p : Ω → ℝ) : mass p Finset.univ = ∑ x, p x := rfl

omit [DecidableEq Ω] in
@[simp] theorem mass_singleton (p : Ω → ℝ) (x : Ω) : mass p {x} = p x := by
  simp [mass]

omit [DecidableEq Ω] in
theorem mass_nonneg {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x) (A : Finset Ω) :
    0 ≤ mass p A := Finset.sum_nonneg fun x _ => hp x

theorem conditional_nonneg {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x) (A B : Finset Ω) :
    0 ≤ conditional p A B := div_nonneg (mass_nonneg hp _) (mass_nonneg hp _)

/-- Event chain rule on the support of its conditioning event. -/
theorem conditional_mul_mass (p : Ω → ℝ) (A B : Finset Ω)
    (hB : mass p B ≠ 0) : conditional p A B * mass p B = mass p (A ∩ B) :=
  div_mul_cancel₀ _ hB

omit [DecidableEq Ω] in
theorem mass_pos_of_mem {p : Ω → ℝ} (hp : ∀ x, 0 < p x)
    {A : Finset Ω} {x : Ω} (hx : x ∈ A) : 0 < mass p A := by
  exact Finset.sum_pos' (fun y _ => (hp y).le) ⟨x, hx, hp x⟩

/-- Event form of `A` conditionally independent of `B` given `C`.
The cross-product form avoids division, including on boundary strata. -/
def CondIndependent (p : Ω → ℝ) (A B C : Finset Ω) : Prop :=
  mass p ((A ∩ B) ∩ C) * mass p C =
    mass p (A ∩ C) * mass p (B ∩ C)

/-- Independence removes the extra conditioning event `B` on its support. -/
theorem conditional_eq_of_independent (p : Ω → ℝ) (A B C : Finset Ω)
    (h : CondIndependent p A B C)
    (hBC : mass p (B ∩ C) ≠ 0) (hC : mass p C ≠ 0) :
    conditional p A (B ∩ C) = conditional p A C := by
  apply (div_eq_div_iff hBC hC).2
  simpa only [CondIndependent, Finset.inter_assoc] using h

/-- The form used by the appendix: the assignment event for `pre(V)` is
contained in the assignment event for the smaller variable set `C`. A local
Markov equation then makes both supported conditional factors equal. -/
theorem conditional_eq_of_subset_independent (p : Ω → ℝ) (A S C : Finset Ω)
    (hSC : S ⊆ C) (h : CondIndependent p A S C)
    (hS : mass p S ≠ 0) (hC : mass p C ≠ 0) :
    conditional p A S = conditional p A C := by
  have hSC' : S ∩ C = S := Finset.inter_eq_left.mpr hSC
  have h' := conditional_eq_of_independent p A S C h (by simpa [hSC'] using hS) hC
  simpa [hSC'] using h'

/-- A ratio product telescopes whenever all denominators are nonzero.
This isolates the arithmetic step in the ordered probability chain rule. -/
theorem prod_successive_ratios (a : ℕ → ℝ) (n : ℕ) (ha0 : a 0 = 1)
    (ha : ∀ k < n, a k ≠ 0) :
    (∏ k ∈ Finset.range n, a (k + 1) / a k) = a n := by
  induction n with
  | zero => simpa using ha0.symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun k hk => ha k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
    exact mul_div_cancel₀ _ (ha n (Nat.lt_succ_self n))

section Assignments

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Assignment event for a named set of observed coordinates. It can be used
for the cumulative external-parent sets `C_i` of Proposition `prop:ident`. -/
def assignmentEvent (w : FullAssign val) (S : Finset (Fin n)) :
    Finset (FullAssign val) :=
  Finset.univ.filter fun z => ∀ i ∈ S, z i = w i

@[simp] theorem self_mem_assignmentEvent (w : FullAssign val) (S : Finset (Fin n)) :
    w ∈ assignmentEvent val w S := by simp [assignmentEvent]

/-- Enlarging the set of specified variables restricts its assignment event. -/
theorem assignmentEvent_antitone (w : FullAssign val) {S T : Finset (Fin n)}
    (hST : S ⊆ T) : assignmentEvent val w T ⊆ assignmentEvent val w S := by
  intro z hz
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact fun i hi => hz i (hST hi)

/-- Event that every observed coordinate before position `k` agrees with `w`. -/
def prefixEvent (w : FullAssign val) (k : ℕ) : Finset (FullAssign val) :=
  Finset.univ.filter fun z => ∀ i : Fin n, i.val < k → z i = w i

theorem prefixEvent_eq_assignmentEvent (w : FullAssign val) (k : ℕ) :
    prefixEvent val w k = assignmentEvent val w (Finset.univ.filter fun i => i.val < k) := by
  ext z
  simp [prefixEvent, assignmentEvent]

theorem prefixEvent_subset_assignmentEvent (w : FullAssign val) (k : ℕ)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < k) :
    prefixEvent val w k ⊆ assignmentEvent val w S := by
  intro z hz
  simp only [prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi => hz i (hS i hi)

/-- Event specifying the value of one observed coordinate. -/
def valueEvent (w : FullAssign val) (i : Fin n) : Finset (FullAssign val) :=
  Finset.univ.filter fun z => z i = w i

@[simp] theorem self_mem_prefixEvent (w : FullAssign val) (k : ℕ) :
    w ∈ prefixEvent val w k := by simp [prefixEvent]

@[simp] theorem prefixEvent_zero (w : FullAssign val) :
    prefixEvent val w 0 = Finset.univ := by ext z; simp [prefixEvent]

@[simp] theorem prefixEvent_full (w : FullAssign val) :
    prefixEvent val w n = {w} := by
  ext z
  simp only [prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hz
    funext i
    exact hz i i.isLt
  · rintro rfl
    simp

/-- Adding the next coordinate to a prefix is an event intersection. -/
theorem prefixEvent_succ (w : FullAssign val) (i : Fin n) :
    prefixEvent val w (i.val + 1) = valueEvent val w i ∩ prefixEvent val w i.val := by
  ext z
  simp only [prefixEvent, valueEvent, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter]
  constructor
  · intro hz
    exact ⟨hz i (Nat.lt_succ_self _), fun j hj => hz j (Nat.lt_trans hj (Nat.lt_succ_self _))⟩
  · rintro ⟨hi, hz⟩ j hj
    by_cases hji : j = i
    · subst j
      exact hi
    · apply hz j
      have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega

/-- Observable factor `P(V_i=w_i | pre(V_i)=w_pre)` in the chosen order. -/
noncomputable def prefixConditional (p : FullAssign val → ℝ) (w : FullAssign val)
    (i : Fin n) : ℝ :=
  conditional p (valueEvent val w i) (prefixEvent val w i.val)

theorem prefixConditional_eq_ratio (p : FullAssign val → ℝ) (w : FullAssign val)
    (i : Fin n) : prefixConditional val p w i =
      mass p (prefixEvent val w (i.val + 1)) / mass p (prefixEvent val w i.val) := by
  rw [prefixConditional, conditional, prefixEvent_succ]

/-- Every prefix is on the support when the observed assignment law is
strictly positive, exactly the standing hypothesis of the manuscript. -/
theorem prefix_mass_pos (p : FullAssign val → ℝ) (hp : ∀ z, 0 < p z)
    (w : FullAssign val) (k : ℕ) : 0 < mass p (prefixEvent val w k) :=
  mass_pos_of_mem hp (self_mem_prefixEvent val w k)

/-- Finite ordered chain rule for a literal observed assignment.
No causal or graph assumption is used in this probability identity. -/
theorem assignment_eq_prod_prefixConditional (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ z, 0 < p z)
    (w : FullAssign val) : p w = ∏ i : Fin n, prefixConditional val p w i := by
  simp_rw [prefixConditional_eq_ratio]
  rw [Fin.prod_univ_eq_prod_range
    (fun k => mass p (prefixEvent val w (k + 1)) / mass p (prefixEvent val w k)) n]
  have h0 : mass p (prefixEvent val w 0) = 1 := by simpa using hp.2
  rw [prod_successive_ratios _ n h0 (fun k _ => (prefix_mass_pos val p hpos w k).ne')]
  simp

/-- Replacing the chain-rule conditioning events by supported smaller
events is enough to reconstruct the observed law. Each independence equation
is an explicit input: it must later be derived from the graph's Markov property. -/
theorem assignment_eq_prod_replaced (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ z, 0 < p z)
    (w : FullAssign val) (C : Fin n → Finset (FullAssign val))
    (hC : ∀ i, prefixEvent val w i.val ⊆ C i)
    (hsupport : ∀ i, mass p (C i) ≠ 0)
    (hCI : ∀ i, CondIndependent p (valueEvent val w i)
      (prefixEvent val w i.val) (C i)) :
    p w = ∏ i, conditional p (valueEvent val w i) (C i) := by
  rw [assignment_eq_prod_prefixConditional val p hp hpos w]
  apply Finset.prod_congr rfl
  intro i _
  exact conditional_eq_of_subset_independent p _ _ _ (hC i) (hCI i)
    (prefix_mass_pos val p hpos w i.val).ne' (hsupport i)

/-- Set-of-variables version of factor replacement, ready for the manuscript's
`C_i`. The only order requirement is that every variable in `C_i` precedes `i`.
Strict positivity supplies the support of its assignment event automatically. -/
theorem assignment_eq_prod_conditioningSets (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ z, 0 < p z)
    (w : FullAssign val) (C : Fin n → Finset (Fin n))
    (hC : ∀ i, ∀ j ∈ C i, j.val < i.val)
    (hCI : ∀ i, CondIndependent p (valueEvent val w i)
      (prefixEvent val w i.val) (assignmentEvent val w (C i))) :
    p w = ∏ i, conditional p (valueEvent val w i) (assignmentEvent val w (C i)) := by
  apply assignment_eq_prod_replaced val p hp hpos w (fun i => assignmentEvent val w (C i))
  · exact fun i => prefixEvent_subset_assignmentEvent val w i.val (C i) (hC i)
  · exact fun i => (mass_pos_of_mem hpos (self_mem_assignmentEvent val w (C i))).ne'
  · exact hCI

end Assignments
end MeraConstraints.FiniteProbability
