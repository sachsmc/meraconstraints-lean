import MeraConstraints.EqualityConstraints
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Counting equations modulo a subspace of equations

General linear algebra for Step 3 of the proof of Proposition 4
(`prop:nontrivial`), the proof of part (i). The number of independent nontrivial
equality constraints is

  `rank (N; O; Hₑ) - rank (N; O)`.

It is the dimension of the space of coefficient rows of all equations, modulo the
subspace of rows of the trivial equations. Here `Modulo W₀ W₁` is that quotient.
Its dimension is the difference of the dimensions of `W₁` and `W₀` when `W₀` is
contained in `W₁`, which holds for the row spaces of `A` and of the stacked
matrix `(A; B)`, giving `rank (A; B) - rank A`.

Ranks of coefficient rows describe the equations when the systems have a common
solution `x₀`: then the right-hand side of an equation with coefficient row `g` is
`gᵀx₀`. So if two systems have a common solution and their coefficient rows have
the same span, they have the same solutions. This is why selected rows of `H_e`
that extend a basis of the trivial rows suffice.

The identification of the trivial equations with the row space of (N) and (O) is
in `CompactDistrict.EqualityTriviality`, and the rank count for the manuscript's
spaces is in `CompactDistrict.EqualityRank`.
-/

namespace MeraConstraints.EqualityConstraints

variable {Row : Type*} [Fintype Row]

/-- Coefficient-row span of a finite real equation matrix. -/
def rowSpace {E : Type*} (A : Matrix E Row ℝ) : Submodule ℝ (Row → ℝ) :=
  Submodule.span ℝ (Set.range A.row)

/-- The coefficient rows in `W₁` modulo those in `W₀`. -/
abbrev Modulo (W₀ W₁ : Submodule ℝ (Row → ℝ)) :=
  W₁ ⧸ Submodule.comap W₁.subtype W₀

theorem finrank_modulo (W₀ W₁ : Submodule ℝ (Row → ℝ)) (hle : W₀ ≤ W₁) :
    Module.finrank ℝ (Modulo W₀ W₁) =
      Module.finrank ℝ W₁ - Module.finrank ℝ W₀ := by
  have hdim := (Submodule.comap W₁.subtype W₀).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hdim
  exact Nat.eq_sub_of_add_eq hdim

theorem finrank_rowSpace_eq_rank {E : Type*} [Finite E] (A : Matrix E Row ℝ) :
    Module.finrank ℝ (rowSpace A) = A.rank :=
  A.rank_eq_finrank_span_row.symm

omit [Fintype Row] in
/-- The row space of stacked matrices is the sum of their row spaces. -/
theorem rowSpace_fromRows {E F : Type*} (A : Matrix E Row ℝ) (B : Matrix F Row ℝ) :
    rowSpace (Matrix.fromRows A B) = rowSpace A ⊔ rowSpace B := by
  unfold rowSpace
  have hrange : Set.range (Matrix.fromRows A B).row = Set.range A.row ∪ Set.range B.row := by
    ext g
    constructor
    · rintro ⟨e, rfl⟩
      cases e with
      | inl e => exact Or.inl ⟨e, rfl⟩
      | inr f => exact Or.inr ⟨f, rfl⟩
    · rintro (⟨e, rfl⟩ | ⟨f, rfl⟩)
      · exact ⟨Sum.inl e, rfl⟩
      · exact ⟨Sum.inr f, rfl⟩
  rw [hrange, Submodule.span_union]

omit [Fintype Row] in
theorem rowSpace_le_fromRows {E F : Type*} (A : Matrix E Row ℝ) (B : Matrix F Row ℝ) :
    rowSpace A ≤ rowSpace (Matrix.fromRows A B) := by
  rw [rowSpace_fromRows]
  exact le_sup_left

/-- The number of independent rows of `B` beyond those of `A` is
`rank (A; B) - rank A`. -/
theorem matrix_rank_count {E F : Type*} [Finite E] [Finite F]
    (A : Matrix E Row ℝ) (B : Matrix F Row ℝ) :
    Module.finrank ℝ (Modulo (rowSpace A) (rowSpace (Matrix.fromRows A B))) =
      (Matrix.fromRows A B).rank - A.rank := by
  rw [finrank_modulo _ _ (rowSpace_le_fromRows A B),
    finrank_rowSpace_eq_rank, finrank_rowSpace_eq_rank]

/-- The expression `rank (N; O; Hₑ) - rank (N; O)` of Proposition 4
(`prop:nontrivial`) (i) is the dimension of the rows of `(N; O; Hₑ)` modulo the
rows of `(N; O)`. -/
theorem normalization_ordering_rank_count {N O H : Type*} [Finite N] [Finite O] [Finite H]
    (normalization : Matrix N Row ℝ) (ordering : Matrix O Row ℝ)
    (equalities : Matrix H Row ℝ) :
    Module.finrank ℝ
      (Modulo (rowSpace (Matrix.fromRows normalization ordering))
        (rowSpace (Matrix.fromRows (Matrix.fromRows normalization ordering) equalities))) =
      (Matrix.fromRows (Matrix.fromRows normalization ordering) equalities).rank -
        (Matrix.fromRows normalization ordering).rank :=
  matrix_rank_count (Matrix.fromRows normalization ordering) equalities

variable {E F : Type*} [Fintype E] [Fintype F]

omit [Fintype F] in
/-- If `A p = a` and `B p = b` have a common solution and the rows of `B` are in
the span of the rows of `A`, every solution of `A p = a` solves `B p = b`. This can
fail without a common solution. -/
theorem feasible_of_rowSpace_le (A : Matrix E Row ℝ) (a : E → ℝ)
    (B : Matrix F Row ℝ) (b : F → ℝ) (x₀ : Row → ℝ)
    (hA₀ : Feasible A a x₀) (hB₀ : Feasible B b x₀)
    (hle : rowSpace B ≤ rowSpace A) (p : Row → ℝ) (hp : Feasible A a p) :
    Feasible B b p := by
  intro f
  have hmem : B.row f ∈ rowSpace A := hle (Submodule.subset_span ⟨f, rfl⟩)
  obtain ⟨weights, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hcoeff : ∀ j, B f j = ∑ e, weights e * A e j := by
    intro j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using
      (congrFun hw j).symm
  have hconstant : b f = ∑ e, weights e * a e := by
    calc
      b f = score (B f) x₀ := (hB₀ f).symm
      _ = score (fun j => ∑ e, weights e * A e j) x₀ :=
        congrArg (fun g => score g x₀) (funext hcoeff)
      _ = ∑ e, weights e * score (A e) x₀ := score_rowCombination A weights x₀
      _ = ∑ e, weights e * a e := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hA₀ e]
  exact ((consequence_iff_rowCombination A a (B f) (b f) x₀ hA₀).mpr
    ⟨weights, hcoeff, hconstant⟩) p hp

/-- If two systems have a common solution and their rows have the same span, they
have the same solutions. This is applied to the trivial rows together with
selected rows of `H_e` that extend a basis of the trivial rows. -/
theorem feasible_iff_of_rowSpace_eq (A : Matrix E Row ℝ) (a : E → ℝ)
    (B : Matrix F Row ℝ) (b : F → ℝ) (x₀ : Row → ℝ)
    (hA₀ : Feasible A a x₀) (hB₀ : Feasible B b x₀)
    (hspace : rowSpace A = rowSpace B) (p : Row → ℝ) :
    Feasible A a p ↔ Feasible B b p :=
  ⟨feasible_of_rowSpace_le A a B b x₀ hA₀ hB₀ hspace.ge p,
    feasible_of_rowSpace_le B b A a x₀ hB₀ hA₀ hspace.le p⟩

end MeraConstraints.EqualityConstraints
