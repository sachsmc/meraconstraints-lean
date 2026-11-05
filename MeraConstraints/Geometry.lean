import MeraConstraints.Polytope

/-!
# Averages of columns and moving past a facet

General facts used in Step 4 of the proof of Proposition 4 (`prop:nontrivial`),
the proof of part (ii). Let `x` be the average of the columns of `B` on a facet
and `b` the average of all columns. For small `ε > 0`, the vector

  `q = (1 + ε) x - ε b`

has all entries positive, satisfies every affine equation that `x` and `b` share
and every other inequality strictly, and violates the inequality of the facet.
Here `slack h c p = c - hᵀp` is the slack of the inequality `hᵀp ≤ c`. The
"small enough `ε`" of the manuscript is justified by a continuity argument over
finitely many strict inequalities (`exists_pos_step`).

The theorem `exists_positive_violator` takes `x` and `b` and their slacks as
hypotheses. The lemmas about averages of columns give those hypotheses from the
columns on the facet. The same perturbation is used in
`EqualityConstraints` for Step 3.
-/

namespace MeraConstraints.Geometry

/-- The average of the columns of `B` indexed by `s`. In the proof of Proposition 4,
`s` is the set of columns on the chosen facet, or all columns. -/
noncomputable def average {Row Col : Type*} (s : Finset Col)
    (B : Matrix Row Col ℝ) : Row → ℝ :=
  fun i => (s.card : ℝ)⁻¹ * ∑ j ∈ s, B i j

/-- An entry of the average of nonnegative columns is positive exactly when some
column in `s` has that entry positive. -/
theorem average_pos_iff {Row Col : Type*} (s : Finset Col) (hs : s.Nonempty)
    (B : Matrix Row Col ℝ) (i : Row) (hnonneg : ∀ j ∈ s, 0 ≤ B i j) :
    0 < average s B i ↔ ∃ j ∈ s, 0 < B i j := by
  have hcard : 0 < (s.card : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
  exact (mul_pos_iff_of_pos_left hcard).trans (Finset.sum_pos_iff_of_nonneg hnonneg)

/-- If no entry vanishes at every column in `s`, the average of those columns is
strictly positive. -/
theorem average_pos_of_no_zero_coordinate {Row Col : Type*}
    (s : Finset Col) (hs : s.Nonempty) (B : Matrix Row Col ℝ)
    (hnonneg : ∀ i j, j ∈ s → 0 ≤ B i j)
    (hno : ¬ ∃ i, ∀ j ∈ s, B i j = 0) :
    ∀ i, 0 < average s B i := by
  classical
  intro i
  apply (average_pos_iff s hs B i (hnonneg i)).mpr
  by_contra h
  push Not at h
  apply hno
  refine ⟨i, ?_⟩
  intro j hj
  exact le_antisymm (h j hj) (hnonneg i j hj)

/-- Finitely many strict inequalities `0 < a i` remain strict for `a i + ε * d i`
when `ε > 0` is small enough. -/
theorem exists_pos_step {I : Type*} [Finite I] (a d : I → ℝ)
    (ha : ∀ i, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 < a i + ε * d i := by
  let U : Set ℝ := {ε | ∀ i, 0 < a i + ε * d i}
  have hU : IsOpen U := by
    dsimp [U]
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.add (continuous_id.mul continuous_const))
  have hzero : (0 : ℝ) ∈ U := by simpa [U] using ha
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  refine ⟨δ / 2, by linarith, hball ?_⟩
  change dist (δ / 2) 0 < δ
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < δ / 2)]
  linarith

variable {Row : Type*} [Fintype Row]

/-- The slack `c - hᵀp` of the inequality `hᵀp ≤ c`; the inequality holds exactly
when the slack is nonnegative. -/
def slack (h : Row → ℝ) (c : ℝ) (p : Row → ℝ) : ℝ :=
  c - ∑ i, h i * p i

/-- The slack of the average of columns is the average of their slacks. -/
theorem slack_average {Col : Type*} (s : Finset Col) (hs : s.Nonempty)
    (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) :
    slack h c (average s B) =
      (s.card : ℝ)⁻¹ * ∑ j ∈ s, slack h c (fun i => B i j) := by
  have hsum : (∑ i, h i * average s B i) =
      (s.card : ℝ)⁻¹ * ∑ j ∈ s, ∑ i, h i * B i j := by
    simp only [average, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hunit : (s.card : ℝ)⁻¹ * (s.card : ℝ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs))
  simp only [slack]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_sub, ← mul_assoc, hunit, one_mul]

/-- If the slack is zero at every column in `s`, it is zero at their average. -/
theorem slack_average_eq_zero {Col : Type*} (s : Finset Col) (hs : s.Nonempty)
    (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ)
    (hz : ∀ j ∈ s, slack h c (fun i => B i j) = 0) :
    slack h c (average s B) = 0 := by
  rw [slack_average s hs B h c]
  simp only [Finset.sum_eq_zero hz, mul_zero]

/-- If the inequality holds at every column in `s`, it is strict at their average
exactly when it is strict at some column in `s`. -/
theorem slack_average_pos_iff {Col : Type*} (s : Finset Col) (hs : s.Nonempty)
    (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ)
    (hn : ∀ j ∈ s, 0 ≤ slack h c (fun i => B i j)) :
    0 < slack h c (average s B) ↔ ∃ j ∈ s, 0 < slack h c (fun i => B i j) := by
  rw [slack_average s hs B h c]
  have hcard : 0 < (s.card : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
  exact (mul_pos_iff_of_pos_left hcard).trans (Finset.sum_pos_iff_of_nonneg hn)

/-- The point `(1 + ε) x - ε b` on the line from `b` through `x`, beyond `x`. -/
def perturb (x b : Row → ℝ) (ε : ℝ) : Row → ℝ :=
  fun i => (1 + ε) * x i - ε * b i

theorem slack_perturb (h : Row → ℝ) (c : ℝ) (x b : Row → ℝ) (ε : ℝ) :
    slack h c (perturb x b ε) =
      (1 + ε) * slack h c x - ε * slack h c b := by
  have hs : (∑ i, h i * perturb x b ε i) =
      (1 + ε) * (∑ i, h i * x i) - ε * (∑ i, h i * b i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [perturb]
    ring
  unfold slack
  rw [hs]
  ring

/-- The point `(1 + ε) x - ε b` satisfies every affine equation that `x` and `b`
both satisfy. -/
theorem perturb_preserves_equation (h : Row → ℝ) (c : ℝ) (x b : Row → ℝ)
    (hx : ∑ i, h i * x i = c) (hb : ∑ i, h i * b i = c) (ε : ℝ) :
    (∑ i, h i * perturb x b ε i) = c := by
  have he := slack_perturb h c x b ε
  simp only [slack, hx, hb, sub_self, mul_zero] at he
  linarith

/-- The vector `q` of Step 4 of the proof of Proposition 4: positive, satisfying
the equations, strictly satisfying the other inequalities and violating the
inequality of the facet. There are finitely many other inequalities; the number
of equations is arbitrary. -/
theorem exists_positive_violator {Other Eqn : Type*} [Finite Other]
    (x b : Row → ℝ) (h : Row → ℝ) (c : ℝ)
    (g : Other → Row → ℝ) (upper : Other → ℝ)
    (A : Eqn → Row → ℝ) (rhs : Eqn → ℝ)
    (hx : ∀ i, 0 < x i)
    (hfacet : slack h c x = 0) (hb : 0 < slack h c b)
    (hother : ∀ j, 0 < slack (g j) (upper j) x)
    (hex : ∀ e, ∑ i, A e i * x i = rhs e)
    (heb : ∀ e, ∑ i, A e i * b i = rhs e) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i, 0 < perturb x b ε i) ∧
      (∀ j, 0 < slack (g j) (upper j) (perturb x b ε)) ∧
      (∀ e, ∑ i, A e i * perturb x b ε i = rhs e) ∧
      slack h c (perturb x b ε) < 0 := by
  let a : Row ⊕ Other → ℝ := Sum.elim x (fun j => slack (g j) (upper j) x)
  let d : Row ⊕ Other → ℝ :=
    Sum.elim (fun i => x i - b i)
      (fun j => slack (g j) (upper j) x - slack (g j) (upper j) b)
  have ha : ∀ k, 0 < a k := by
    intro k
    cases k with
    | inl i => exact hx i
    | inr j => exact hother j
  obtain ⟨ε, hε, hstep⟩ := exists_pos_step a d ha
  refine ⟨ε, hε, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := hstep (Sum.inl i)
    change 0 < x i + ε * (x i - b i) at hi
    dsimp [perturb]
    nlinarith
  · intro j
    have hj := hstep (Sum.inr j)
    change 0 < slack (g j) (upper j) x +
      ε * (slack (g j) (upper j) x - slack (g j) (upper j) b) at hj
    rw [slack_perturb]
    nlinarith
  · intro e
    exact perturb_preserves_equation (A e) (rhs e) x b (hex e) (heb e) ε
  · rw [slack_perturb, hfacet]
    nlinarith

end MeraConstraints.Geometry
