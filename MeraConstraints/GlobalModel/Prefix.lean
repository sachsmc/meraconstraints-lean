import MeraConstraints.GlobalModel
import MeraConstraints.Probability.Pushforward

/-!
# Prefix probabilities from independent block mechanisms

The observable district product is built from conditionals in one global
topological order. This chapter proves the structural identity needed to
analyze those conditionals directly. A partial observed configuration up to
position `k` occurs exactly when each block's profiles satisfy the structural
equations for that block's members before `k`.

The reverse implication uses topological induction: every observed parent
of a member before `k` is itself before `k`. Thus the event is rectangular
in the independent block profiles, and its mass factors into a product of
block prefix masses. Neither the ordered Markov property nor observable
identification is assumed in this argument.

Adding one observed member changes only its own block's prefix constraint.
The other block factors remain equal, even if edges between blocks form a
cycle after the blocks are contracted. This is why the proof works with the
original vertex order rather than an assumed ordering of the districts.
-/

namespace MeraConstraints.GlobalModel

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)

/-- Solving only the equations before `k` determines those observed outputs.
The input `h` is a literal family of structural equations; no Markov property is assumed. -/
theorem eval_prefix_eq_apply (r : RespAssign G val) (w : FullAssign val) (k : ℕ)
    (h : ∀ i : Fin n, i.val < k → r i (PaAssign.restrict w i) = w i)
    (i : Fin n) (hi : i.val < k) : evalR r i = w i := by
  calc
    evalR r i = r i (PaAssign.restrict (evalR r) i) := evalR_eq r i
    _ = r i (PaAssign.restrict w i) := by
      congr 1
      funext j
      exact eval_prefix_eq_apply r w k h j (Nat.lt_trans (G.parents_lt j.2) hi)
    _ = w i := h i hi
termination_by i.val
decreasing_by exact G.parents_lt j.2

/-- Matching a prefix and satisfying its structural equations are equivalent. -/
theorem eval_prefix_eq_iff (r : RespAssign G val) (w : FullAssign val) (k : ℕ) :
    (∀ i : Fin n, i.val < k → evalR r i = w i) ↔
      ∀ i : Fin n, i.val < k → r i (PaAssign.restrict w i) = w i := by
  constructor
  · intro h i hi
    have hpa : PaAssign.restrict (G := G) (evalR r) i = PaAssign.restrict (G := G) w i := by
      funext j
      exact h j (Nat.lt_trans (G.parents_lt j.2) hi)
    have heq := evalR_eq r i
    rw [hpa, h i hi] at heq
    exact heq.symm
  · intro h i hi
    exact eval_prefix_eq_apply G val r w k h i hi

variable {D : Type*} [Fintype D] [DecidableEq D] (block : Fin n → D)

/-- The profile satisfies its block's equations for members before `k`. -/
def PrefixCompatible (d : D) (k : ℕ) (w : FullAssign val)
    (r : Profile G val block d) : Prop :=
  ∀ i : {i : Fin n // block i = d}, i.1.val < k →
    r i (PaAssign.restrict w i) = w i

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [Fintype D] [DecidableEq D] in
/-- Recursive evaluation belongs to an observed prefix event precisely when
all its independent block profiles satisfy their corresponding prefix equations. -/
theorem eval_mem_prefixEvent_iff (r : ∀ d, Profile G val block d)
    (w : FullAssign val) (k : ℕ) :
    evalR (assemble G val block r) ∈ FiniteProbability.prefixEvent val w k ↔
      ∀ d, PrefixCompatible G val block d k w (r d) := by
  simp only [FiniteProbability.prefixEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [eval_prefix_eq_iff]
  constructor
  · intro h d i hi
    rcases i with ⟨i, hid⟩
    subst d
    exact h i hi
  · intro h i hi
    exact h (block i) ⟨i, rfl⟩ hi

/-- Block prefix mass as a linear function of the block's profile law. -/
noncomputable def prefixFactor (q : ∀ d, Profile G val block d → ℝ)
    (d : D) (k : ℕ) (w : FullAssign val) : ℝ := by
  classical
  exact ∑ r, if PrefixCompatible G val block d k w r then q d r else 0

/-- The observable prefix-event probability factors over independent blocks.
This identity includes zero-probability prefixes and unnormalized mass vectors. -/
theorem prefix_mass_eq_prod_prefixFactor (q : ∀ d, Profile G val block d → ℝ)
    (w : FullAssign val) (k : ℕ) :
    FiniteProbability.mass (observed G val block q) (FiniteProbability.prefixEvent val w k) =
      ∏ d, prefixFactor G val block q d k w := by
  classical
  rw [observed, FiniteProbability.mass_pushforward]
  simp only [FiniteProbability.mass, FiniteProbability.preimage, Finset.sum_filter]
  simp_rw [eval_mem_prefixEvent_iff]
  exact Independent.rectangular_mass q (fun d r => PrefixCompatible G val block d k w r)

omit [Fintype D] [DecidableEq D] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
/-- At an observation from a different block, this block's prefix constraints
are unchanged. No assumption on edges between blocks is required. -/
theorem prefixCompatible_succ_of_ne (d : D) (i : Fin n) (w : FullAssign val)
    (r : Profile G val block d) (hdi : d ≠ block i) :
    PrefixCompatible G val block d (i.val + 1) w r ↔
      PrefixCompatible G val block d i.val w r := by
  constructor
  · intro h j hj
    exact h j (Nat.lt_trans hj (Nat.lt_succ_self _))
  · intro h j hj
    by_cases hji : j.1.val < i.val
    · exact h j hji
    · have heq : j.1 = i := Fin.ext (by omega)
      exact (hdi (j.2.symm.trans (congrArg block heq))).elim

omit [Fintype D] in
theorem prefixFactor_succ_of_ne (q : ∀ d, Profile G val block d → ℝ)
    (d : D) (i : Fin n) (w : FullAssign val) (hdi : d ≠ block i) :
    prefixFactor G val block q d (i.val + 1) w = prefixFactor G val block q d i.val w := by
  classical
  unfold prefixFactor
  apply Finset.sum_congr rfl
  intro r _
  rw [prefixCompatible_succ_of_ne G val block d i w r hdi]

omit [Fintype D] in
/-- With no observed coordinates specified, a block contributes its total mass. -/
theorem prefixFactor_zero (q : ∀ d, Profile G val block d → ℝ)
    (d : D) (w : FullAssign val) : prefixFactor G val block q d 0 w = ∑ r, q d r := by
  simp [prefixFactor, PrefixCompatible]

omit [Fintype D] [DecidableEq D] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem prefixCompatible_full (d : D) (w : FullAssign val) (r : Profile G val block d) :
    PrefixCompatible G val block d n w r ↔ Compatible G val block d w r := by
  constructor
  · intro h i
    exact h i i.1.isLt
  · intro h i _
    exact h i

omit [Fintype D] in
/-- Specifying the full observed configuration recovers the district factor. -/
theorem prefixFactor_full (q : ∀ d, Profile G val block d → ℝ)
    (d : D) (w : FullAssign val) :
    prefixFactor G val block q d n w = factor G val block q d w := by
  classical
  simp only [prefixFactor, factor, prefixCompatible_full]

private theorem ratio_products_of_eq_off (f g : D → ℝ) (a : D)
    (hprod : (∏ d, g d) ≠ 0) (hfg : ∀ d, d ≠ a → f d = g d) :
    (∏ d, f d) / (∏ d, g d) = f a / g a := by
  have hga : g a ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) a (Finset.mem_univ a)
  have hrest : (∏ d ∈ Finset.univ.erase a, f d) = ∏ d ∈ Finset.univ.erase a, g d := by
    apply Finset.prod_congr rfl
    intro d hd
    exact hfg d (Finset.ne_of_mem_erase hd)
  apply (div_eq_div_iff hprod hga).2
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ a), hrest]
  ring

/-- A supported observed prefix conditional is the ratio of its own block's
two prefix masses. Every other block cancels because its equations are unchanged.
This is derived from structural recursion and independent profile laws. -/
theorem prefixConditional_eq_prefixFactor_ratio (q : ∀ d, Profile G val block d → ℝ)
    (w : FullAssign val) (i : Fin n)
    (hpre : FiniteProbability.mass (observed G val block q)
      (FiniteProbability.prefixEvent val w i.val) ≠ 0) :
    FiniteProbability.prefixConditional val (observed G val block q) w i =
      prefixFactor G val block q (block i) (i.val + 1) w /
        prefixFactor G val block q (block i) i.val w := by
  have hprod : (∏ d, prefixFactor G val block q d i.val w) ≠ 0 := by
    simpa only [prefix_mass_eq_prod_prefixFactor] using hpre
  rw [FiniteProbability.prefixConditional_eq_ratio,
    prefix_mass_eq_prod_prefixFactor, prefix_mass_eq_prod_prefixFactor]
  apply ratio_products_of_eq_off _ _ _ hprod
  intro d hd
  exact prefixFactor_succ_of_ne G val block q d i w hd

/-- Ordered observational district product equals the structural district
factor. The conditionals here use all global predecessors, as in `Q[D]` in
the appendix. Replacing them by the cumulative `C_i` still requires the
corresponding conditional-independence argument, and is not claimed here. -/
theorem factor_eq_prod_prefixConditional (q : ∀ d, Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (Profile G val block d))
    (hpos : ∀ w, 0 < observed G val block q w) (d : D) (w : FullAssign val) :
    factor G val block q d w =
      ∏ i ∈ Finset.univ.filter (fun i => block i = d),
        FiniteProbability.prefixConditional val (observed G val block q) w i := by
  classical
  have hnonzero : ∀ k, prefixFactor G val block q d k w ≠ 0 := by
    intro k
    have hp : (∏ e, prefixFactor G val block q e k w) ≠ 0 := by
      rw [← prefix_mass_eq_prod_prefixFactor]
      exact (FiniteProbability.prefix_mass_pos val _ hpos w k).ne'
    exact (Finset.prod_ne_zero_iff.mp hp) d (Finset.mem_univ d)
  have hzero : prefixFactor G val block q d 0 w = 1 := by
    rw [prefixFactor_zero]
    exact (hq d).2
  rw [Finset.prod_filter]
  have hterm : ∀ i : Fin n,
      (if block i = d then FiniteProbability.prefixConditional val (observed G val block q) w i
        else 1) = prefixFactor G val block q d (i.val + 1) w /
          prefixFactor G val block q d i.val w := by
    intro i
    by_cases hid : block i = d
    · rw [if_pos hid, prefixConditional_eq_prefixFactor_ratio G val block q w i
        (FiniteProbability.prefix_mass_pos val _ hpos w i.val).ne', hid]
    · rw [if_neg hid, prefixFactor_succ_of_ne G val block q d i w (Ne.symm hid),
        div_self (hnonzero i.val)]
  simp_rw [hterm]
  rw [Fin.prod_univ_eq_prod_range
    (fun k => prefixFactor G val block q d (k + 1) w / prefixFactor G val block q d k w) n]
  rw [FiniteProbability.prod_successive_ratios _ n hzero (fun k _ => hnonzero k), prefixFactor_full]

end MeraConstraints.GlobalModel
