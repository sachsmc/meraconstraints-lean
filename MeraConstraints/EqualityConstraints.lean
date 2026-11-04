import MeraConstraints.Geometry
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Affine consequences of the equality constraints

Step 3 of Proposition `prop:nontrivial` (i), `appendix.tex:302--304`, uses
two finite-dimensional facts. First, an affine equation holding on every
strictly positive point of a nonempty affine solution set holds on the whole
solution set, provided the solution set contains a strictly positive point.
Second, every such equation is a linear combination of the defining
equations, including their right-hand sides.

This chapter proves both statements for an arbitrary real system `A p = b`.
The first proof moves a small distance from the positive feasible point in
the direction away from an arbitrary feasible point; the result remains
positive and feasible, and affine linearity recovers the arbitrary point.
For the second, feasible translations show that the proposed linear form
annihilates the kernel of `A`. If its coefficient vector were outside the row
span, linear separation would produce a null direction on which it does not
vanish. This proves row-span membership, rather than assuming it.

The application to the manuscript's *trivial* equality constraints is proved
in `CompactDistrict.EqualityTriviality`. It uses the checked equivalence
between positive (N)/(O) kernels and observable factors of globally Markov
observed laws. That graphical identification is separate from this generic
linear-algebra bridge; the semantic rank count is in `CompactDistrict.EqualityRank`.
-/

namespace MeraConstraints.EqualityConstraints

variable {Row E : Type*} [Fintype Row] [Fintype E]

/-- The linear form `gᵀp`, separated from its affine right-hand side. -/
def score (g p : Row → ℝ) : ℝ := ∑ j, g j * p j

/-- The full affine solution set, allowing coordinates of either sign. -/
def Feasible (A : Matrix E Row ℝ) (b : E → ℝ) (p : Row → ℝ) : Prop :=
  ∀ e, score (A e) p = b e

def Consequence (A : Matrix E Row ℝ) (b : E → ℝ) (g : Row → ℝ) (c : ℝ) : Prop :=
  ∀ p, Feasible A b p → score g p = c

def PositiveConsequence (A : Matrix E Row ℝ) (b : E → ℝ) (g : Row → ℝ) (c : ℝ) : Prop :=
  ∀ p, (∀ j, 0 < p j) → Feasible A b p → score g p = c

/-- Both coefficients and constants must be combined with the same weights. -/
def RowCombination (A : Matrix E Row ℝ) (b : E → ℝ) (g : Row → ℝ) (c : ℝ) : Prop :=
  ∃ weights : E → ℝ,
    (∀ j, g j = ∑ e, weights e * A e j) ∧ c = ∑ e, weights e * b e

omit [Fintype E] in
/-- A positive feasible point lets affine identities extend from the positive
part of the solution set to every feasible point. -/
theorem positive_consequence_iff_consequence (A : Matrix E Row ℝ) (b : E → ℝ)
    (g : Row → ℝ) (c : ℝ) (x₀ : Row → ℝ)
    (hx₀ : Feasible A b x₀) (hpos : ∀ j, 0 < x₀ j) :
    PositiveConsequence A b g c ↔ Consequence A b g c := by
  constructor
  · intro h p hp
    obtain ⟨ε, hε, hstep⟩ := Geometry.exists_pos_step x₀ (fun j => x₀ j - p j) hpos
    have hqpos : ∀ j, 0 < Geometry.perturb x₀ p ε j := by
      intro j
      have hj := hstep j
      dsimp [Geometry.perturb]
      nlinarith
    have hq : Feasible A b (Geometry.perturb x₀ p ε) := by
      intro e
      exact Geometry.perturb_preserves_equation (A e) (b e) x₀ p (hx₀ e) (hp e) ε
    have hg₀ := h x₀ hpos hx₀
    have hgq := h (Geometry.perturb x₀ p ε) hqpos hq
    have hline := Geometry.slack_perturb g c x₀ p ε
    change c - score g (Geometry.perturb x₀ p ε) =
      (1 + ε) * (c - score g x₀) - ε * (c - score g p) at hline
    rw [hg₀, hgq] at hline
    have hprod : ε * (score g p - c) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (ne_of_gt hε))
  · intro h p _ hp
    exact h p hp

theorem score_add (g p v : Row → ℝ) : score g (p + v) = score g p + score g v := by
  simp only [score, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype E] in
/-- Any affine consequence annihilates every homogeneous solution direction. -/
theorem score_eq_zero_of_homogeneous (A : Matrix E Row ℝ) (b : E → ℝ)
    (g : Row → ℝ) (c : ℝ) (x₀ : Row → ℝ) (hx₀ : Feasible A b x₀)
    (h : Consequence A b g c) (v : Row → ℝ) (hv : ∀ e, score (A e) v = 0) :
    score g v = 0 := by
  have hfeas : Feasible A b (x₀ + v) := by
    intro e
    rw [score_add, hx₀ e, hv e, add_zero]
  have h₀ := h x₀ hx₀
  have h₁ := h (x₀ + v) hfeas
  rw [score_add] at h₁
  linarith

/-- A linear functional on finitely many coordinates has dot-product form. -/
theorem score_represents_linearMap [DecidableEq Row]
    (f : (Row → ℝ) →ₗ[ℝ] ℝ) (p : Row → ℝ) :
    score p (fun j => f (Pi.single j 1)) = f p := by
  classical
  have h := congrArg f (pi_eq_sum_univ' p)
  simpa only [score, map_sum, map_smul, smul_eq_mul] using h.symm

omit [Fintype E] in
/-- Kernel annihilation forces membership in the span of the defining rows.
The separating functional would otherwise provide a contradictory null vector. -/
theorem mem_rowSpan_of_consequence (A : Matrix E Row ℝ) (b : E → ℝ)
    (g : Row → ℝ) (c : ℝ) (x₀ : Row → ℝ) (hx₀ : Feasible A b x₀)
    (h : Consequence A b g c) :
    g ∈ Submodule.span ℝ (Set.range fun e => A e) := by
  classical
  by_contra hg
  obtain ⟨f, hfg, hker⟩ := Submodule.exists_le_ker_of_notMem hg
  let v : Row → ℝ := fun j => f (Pi.single j 1)
  have hv : ∀ e, score (A e) v = 0 := by
    intro e
    rw [score_represents_linearMap]
    exact LinearMap.mem_ker.mp (hker (Submodule.subset_span ⟨e, rfl⟩))
  have hz := score_eq_zero_of_homogeneous A b g c x₀ hx₀ h v hv
  exact hfg ((score_represents_linearMap f g).symm.trans hz)

/-- Distributing a row combination through a linear form. -/
theorem score_rowCombination (A : Matrix E Row ℝ) (weights : E → ℝ) (p : Row → ℝ) :
    score (fun j => ∑ e, weights e * A e j) p = ∑ e, weights e * score (A e) p := by
  simp only [score, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Affine consequences are exactly linear combinations of the equations.
Only nonemptiness of the affine solution set is required for this statement. -/
theorem consequence_iff_rowCombination (A : Matrix E Row ℝ) (b : E → ℝ)
    (g : Row → ℝ) (c : ℝ) (x₀ : Row → ℝ) (hx₀ : Feasible A b x₀) :
    Consequence A b g c ↔ RowCombination A b g c := by
  constructor
  · intro h
    obtain ⟨weights, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (mem_rowSpan_of_consequence A b g c x₀ hx₀ h)
    have hcoeff : ∀ j, g j = ∑ e, weights e * A e j := by
      intro j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (congrFun hw j).symm
    refine ⟨weights, hcoeff, ?_⟩
    calc
      c = score g x₀ := (h x₀ hx₀).symm
      _ = score (fun j => ∑ e, weights e * A e j) x₀ :=
        congrArg (fun z => score z x₀) (funext hcoeff)
      _ = ∑ e, weights e * score (A e) x₀ := score_rowCombination A weights x₀
      _ = ∑ e, weights e * b e := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hx₀ e]
  · rintro ⟨weights, hcoeff, hc⟩ p hp
    calc
      score g p = score (fun j => ∑ e, weights e * A e j) p :=
        congrArg (fun z => score z p) (funext hcoeff)
      _ = ∑ e, weights e * score (A e) p := score_rowCombination A weights p
      _ = c := by
        calc
          _ = ∑ e, weights e * b e := by
            apply Finset.sum_congr rfl
            intro e _
            rw [hp e]
          _ = c := hc.symm

/-- The complete generic linear-algebra bridge used in Appendix Step 3.
The paper-specific identification with observed graphical independence
factors is supplied separately in `CompactDistrict.EqualityTriviality`. -/
theorem positive_consequence_iff_rowCombination (A : Matrix E Row ℝ) (b : E → ℝ)
    (g : Row → ℝ) (c : ℝ) (x₀ : Row → ℝ)
    (hx₀ : Feasible A b x₀) (hpos : ∀ j, 0 < x₀ j) :
    PositiveConsequence A b g c ↔ RowCombination A b g c :=
  (positive_consequence_iff_consequence A b g c x₀ hx₀ hpos).trans
    (consequence_iff_rowCombination A b g c x₀ hx₀)

end MeraConstraints.EqualityConstraints
