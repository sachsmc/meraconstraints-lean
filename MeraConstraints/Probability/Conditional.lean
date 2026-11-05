import MeraConstraints.Probability.Finite
import MeraConstraints.SCM.Basic
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Probabilities of events, conditioning, and the ordered chain rule

The manuscript assumes that the observed distribution is strictly positive
(Notation), so the conditional probabilities in Proposition 1 (`prop:ident`)
have positive denominators. `mass` is the probability of a set of complete
assignments and `conditional` is the ratio of masses. Lean divides by zero to get
0, so theorems that read `conditional` as a conditional probability assume the
conditioning event has nonzero mass. Conditional independence is stated by the
cross-product equation, which needs no division.

The observed variables are numbered `0, …, n - 1` in a topological order.
`prefixEvent w k` is the event that the first `k` variables take the values in
`w`, so `prefixConditional` is the factor `Pr(V_i = w_i ∣ pre(V_i) = w_pre)` of
the chain rule. `assignment_eq_prod_prefixConditional` shows that the probability
of a complete assignment is the product of these factors.
`assignment_eq_prod_conditioningSets` is the step in the proofs of Proposition 1
and Proposition 3 (`prop:complete`) that replaces `pre(V)` by the smaller set
`C_V` of the manuscript, given a conditional independence for each variable. That
the conditional independence holds is proved elsewhere, from the graph.
-/

namespace MeraConstraints.FiniteProbability

variable {Ω : Type*} [DecidableEq Ω]

/-- Probability of a finite event under a probability-mass vector. -/
def mass (p : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ x ∈ A, p x

/-- Strict positivity of an observed distribution: every complete assignment of
the observed variables has positive probability. -/
def StrictlyPositive (p : Ω → ℝ) : Prop := ∀ x, 0 < p x

/-- The values with nonzero probability. -/
noncomputable def support [Fintype Ω] (p : Ω → ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun x => p x ≠ 0

omit [DecidableEq Ω] in
@[simp] theorem mem_support [Fintype Ω] (p : Ω → ℝ) (x : Ω) :
    x ∈ support p ↔ p x ≠ 0 := by
  classical
  simp [support]

/-- The conditional probability `mass p (A ∩ B) / mass p B`. It is 0 when
`mass p B = 0`, so statements that use it as a conditional probability assume
`mass p B ≠ 0`. -/
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

/-- The events `A` and `B` are conditionally independent given `C`, in
cross-product form: `P(A ∩ B ∩ C) P(C) = P(A ∩ C) P(B ∩ C)`. This needs no
division, so it is defined when `C` has probability zero. -/
def CondIndependent (p : Ω → ℝ) (A B C : Finset Ω) : Prop :=
  mass p ((A ∩ B) ∩ C) * mass p C =
    mass p (A ∩ C) * mass p (B ∩ C)

/-- If `A` and `B` are conditionally independent given `C`, conditioning on `B`
as well as `C` does not change the conditional probability of `A`. -/
theorem conditional_eq_of_independent (p : Ω → ℝ) (A B C : Finset Ω)
    (h : CondIndependent p A B C)
    (hBC : mass p (B ∩ C) ≠ 0) (hC : mass p C ≠ 0) :
    conditional p A (B ∩ C) = conditional p A C := by
  apply (div_eq_div_iff hBC hC).2
  simpa only [CondIndependent, Finset.inter_assoc] using h

/-- The form used in the Supplementary Materials: the event `S` (for `pre(V)`)
is contained in the event `C` (for the smaller conditioning set), and `A` is
conditionally independent of `S` given `C`. Then the two conditional
probabilities of `A` agree. -/
theorem conditional_eq_of_subset_independent (p : Ω → ℝ) (A S C : Finset Ω)
    (hSC : S ⊆ C) (h : CondIndependent p A S C)
    (hS : mass p S ≠ 0) (hC : mass p C ≠ 0) :
    conditional p A S = conditional p A C := by
  have hSC' : S ∩ C = S := Finset.inter_eq_left.mpr hSC
  have h' := conditional_eq_of_independent p A S C h (by simpa [hSC'] using hS) hC
  simpa [hSC'] using h'

/-- A product of successive ratios telescopes when all denominators are nonzero.
This is the arithmetic step of the chain rule. -/
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

/-- The event that the observed variables in `S` take the values given by `w`.
It is used for the conditioning sets `C_i` of Proposition 1 (`prop:ident`). -/
def assignmentEvent (w : FullAssign val) (S : Finset (Fin n)) :
    Finset (FullAssign val) :=
  Finset.univ.filter fun z => ∀ i ∈ S, z i = w i

@[simp] theorem self_mem_assignmentEvent (w : FullAssign val) (S : Finset (Fin n)) :
    w ∈ assignmentEvent val w S := by simp [assignmentEvent]

/-- Fixing more variables gives a smaller event. -/
theorem assignmentEvent_antitone (w : FullAssign val) {S T : Finset (Fin n)}
    (hST : S ⊆ T) : assignmentEvent val w T ⊆ assignmentEvent val w S := by
  intro z hz
  simp only [assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact fun i hi => hz i (hST hi)

/-- The event that the first `k` observed variables take the values in `w`. -/
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

/-- The event that the observed variable `V_i` takes the value `w i`. -/
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

/-- Extending a prefix by the next variable intersects its event with the event
for that variable. -/
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

/-- The factor `Pr(V_i = w_i ∣ pre(V_i) = w_pre)` of the chain rule, where
`pre(V_i)` is the set of variables before `V_i` in the topological order. -/
noncomputable def prefixConditional (p : FullAssign val → ℝ) (w : FullAssign val)
    (i : Fin n) : ℝ :=
  conditional p (valueEvent val w i) (prefixEvent val w i.val)

theorem prefixConditional_eq_ratio (p : FullAssign val → ℝ) (w : FullAssign val)
    (i : Fin n) : prefixConditional val p w i =
      mass p (prefixEvent val w (i.val + 1)) / mass p (prefixEvent val w i.val) := by
  rw [prefixConditional, conditional, prefixEvent_succ]

/-- If the observed distribution is strictly positive, every prefix event has
positive probability. -/
theorem prefix_mass_pos (p : FullAssign val → ℝ) (hp : ∀ z, 0 < p z)
    (w : FullAssign val) (k : ℕ) : 0 < mass p (prefixEvent val w k) :=
  mass_pos_of_mem hp (self_mem_prefixEvent val w k)

/-- The chain rule: for a strictly positive observed distribution, the probability
of a complete assignment is the product of the factors `prefixConditional`. It
does not use the graph. -/
theorem assignment_eq_prod_prefixConditional (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ z, 0 < p z)
    (w : FullAssign val) : p w = ∏ i : Fin n, prefixConditional val p w i := by
  simp_rw [prefixConditional_eq_ratio]
  rw [Fin.prod_univ_eq_prod_range
    (fun k => mass p (prefixEvent val w (k + 1)) / mass p (prefixEvent val w k)) n]
  have h0 : mass p (prefixEvent val w 0) = 1 := by simpa using hp.2
  rw [prod_successive_ratios _ n h0 (fun k _ => (prefix_mass_pos val p hpos w k).ne')]
  simp

/-- The chain rule with each conditioning event `pre(V_i)` replaced by a smaller
event `C i`. The hypothesis `hCI` says that each variable is conditionally
independent of `pre(V_i)` given `C i`; it is derived from the graph elsewhere. -/
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

/-- The previous theorem with `C i` a set of variables, as for the manuscript's
`C_i`. Each variable in `C i` must precede `i` in the order. -/
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
