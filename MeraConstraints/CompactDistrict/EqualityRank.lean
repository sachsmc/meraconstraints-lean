import MeraConstraints.CompactDistrict.EqualityTriviality
import MeraConstraints.CompactDistrict.FacetCriterion

/-!
# The number of nontrivial equality constraints

This chapter proves the second and third claims of Proposition 4
(`prop:nontrivial`) (i). The equality constraints of the district are the equations
`gᵀp = c` that hold at every column of the matrix `B`, and hence on the whole
district polytope. Their coefficient vectors form `districtEqualitySpace`. The
trivial ones form `graphTrivialSpace`, which is the row space of (N) and (O) by the
first claim. When the rows of `H_e` define the affine hull of the district polytope,
`districtEqualitySpace` is the row space of `(N; O; H_e)`. The number of linearly
independent nontrivial equality constraints is the dimension of the quotient, which
is `rank(N; O; H_e) - rank(N; O)`.

The last theorem is the third claim: rows of `H_e` that, together with (N) and (O),
span the row space of `(N; O; H_e)` imply, with the conditional independencies, all
equality constraints of the district. A basis extension is one such choice.
-/

namespace MeraConstraints.CompactDistrict

open HiddenGraph EqualityConstraints OrderingConstraints
open GlobalModel.KernelReconstruction GlobalModel.OrderingInvariance

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] (d : DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (observedDistrict G) d
local notation "C" => matrix G.observed val (observedDistrict G) d
local notation "NO" => constraintsMatrix G val d
local notation "rhs" => constraintsRhs G val d

/-- The coefficient vectors `g` of the equality constraints of the district:
`gᵀp` takes the same value at every column of `B`. -/
def districtEqualitySpace : Submodule ℝ (Rows → ℝ) where
  carrier := {g | ∃ c, ∀ r : Profiles, score g (fun x => C x r) = c}
  zero_mem' := ⟨0, by intro r; simp [score]⟩
  add_mem' := by
    rintro g h ⟨c, hc⟩ ⟨b, hb⟩
    refine ⟨c + b, ?_⟩
    intro r
    simpa only [score, Pi.add_apply, add_mul, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hc r) (hb r)
  smul_mem' := by
    rintro a g ⟨c, hc⟩
    refine ⟨a * c, ?_⟩
    intro r
    simpa only [score, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] using
      congrArg (a * ·) (hc r)

omit [∀ i, Nonempty (val i)] in
/-- An equation that holds at every column of `B` holds on the district polytope. -/
theorem equation_of_columns (g : Rows → ℝ) (c : ℝ)
    (hcol : ∀ r : Profiles, score g (fun x => C x r) = c)
    (q : Rows → ℝ) (hq : q ∈ Polytope.mixture C) : score g q = c := by
  obtain ⟨weights, hw, rfl⟩ := hq
  rw [score, Polytope.score_mulVec]
  change (∑ r, weights r * score g (fun x => C x r)) = c
  simp_rw [hcol]
  rw [← Finset.sum_mul, hw.2, one_mul]

omit [∀ i, Nonempty (val i)] in
theorem constraints_column (r : Profiles) : Feasible NO rhs (fun x => C x r) := by
  intro index
  cases index with
  | inl e => exact normalization_column G val d r e
  | inr o => exact ordering_column G val d r o

omit [∀ i, Nonempty (val i)] in
theorem constraints_rowSpace_le_districtEqualitySpace :
    rowSpace NO ≤ districtEqualitySpace G val d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨index, rfl⟩
  exact ⟨rhs index, fun r => constraints_column G val d r index⟩

variable {E : Type*} [Fintype E]

omit [∀ i, DecidableEq (val i)] in
/-- If the rows of `H_e` define the affine hull of the district polytope, the
coefficient vectors of the equality constraints are the row space of `H_e`. -/
theorem districtEqualitySpace_eq_rowSpace (A : Matrix E Rows ℝ) (b : E → ℝ)
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b q) :
    districtEqualitySpace G val d = rowSpace A := by
  classical
  let r₀ : Profiles := Classical.choice inferInstance
  have hA₀ : Feasible A b (fun x => C x r₀) :=
    (hhull _).mp (mem_affineSpan ℝ ⟨r₀, rfl⟩)
  ext g
  constructor
  · rintro ⟨c, hc⟩
    apply mem_rowSpan_of_consequence A b g c _ hA₀
    intro q hq
    apply MeraConstraints.FacetCriterion.equation_on_affineSpan
      (Set.range fun r : Profiles => fun x : Rows => C x r) g c
    · rintro _ ⟨r, rfl⟩
      exact hc r
    · exact (hhull q).mpr hq
  · intro hg
    obtain ⟨weights, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
    have hcoeff : g = fun j => ∑ e, weights e * A e j := by
      funext j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using
        (congrFun hw j).symm
    refine ⟨∑ e, weights e * b e, ?_⟩
    intro r
    have hr : Feasible A b (fun x => C x r) := (hhull _).mp (mem_affineSpan ℝ ⟨r, rfl⟩)
    rw [hcoeff, score_rowCombination]
    exact Finset.sum_congr rfl fun e _ => congrArg (weights e * ·) (hr e)

theorem districtEqualitySpace_eq_stacked_rowSpace (A : Matrix E Rows ℝ) (b : E → ℝ)
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b q) :
    districtEqualitySpace G val d = rowSpace (Matrix.fromRows NO A) := by
  rw [rowSpace_fromRows]
  have hle := constraints_rowSpace_le_districtEqualitySpace G val d
  rw [districtEqualitySpace_eq_rowSpace G val d A b hhull] at hle ⊢
  exact (sup_eq_right.mpr hle).symm

/-- The trivial coefficient vectors are among those of the equality constraints. -/
theorem graphTrivialSpace_le_districtEqualitySpace (hdegree : ∀ x, cDegree G x ≤ 1) :
    graphTrivialSpace G val d ≤ districtEqualitySpace G val d := by
  rw [graphTrivialSpace_eq_rowSpace G val d hdegree]
  exact constraints_rowSpace_le_districtEqualitySpace G val d

/-- Proposition 4 (`prop:nontrivial`) (i), second claim: the number of linearly
independent nontrivial equality constraints is `rank(N; O; H_e) - rank(N; O)`. The
left side is the dimension of the equality constraints modulo the trivial ones,
neither defined from these matrices. The hypothesis `hhull` says the rows of `H_e`
define the affine hull. -/
theorem nontrivialEquality_rank_count (hdegree : ∀ x, cDegree G x ≤ 1)
    (A : Matrix E Rows ℝ) (b : E → ℝ)
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b q) :
    Module.finrank ℝ (Modulo (graphTrivialSpace G val d) (districtEqualitySpace G val d)) =
      (Matrix.fromRows NO A).rank - (constraintsMatrix G val d).rank := by
  rw [graphTrivialSpace_eq_rowSpace G val d hdegree,
    districtEqualitySpace_eq_stacked_rowSpace G val d A b hhull]
  exact matrix_rank_count NO A

omit [Fintype E] in
/-- Proposition 4 (`prop:nontrivial`) (i), third claim: selected rows of `H_e` that
together with (N) and (O) span the row space of `(N; O; H_e)` imply all rows of
`H_e`: a strictly positive distribution that satisfies the conditional independencies
and the selected rows satisfies `H_e p = b_e`.
The manuscript chooses rows that extend a basis; any spanning choice is allowed
here. The proof does not use the proposition's c-degree hypothesis, so the statement
omits it, but it should be read in that setting. -/
theorem selected_equalities_imply_all {F : Type*} [Fintype F]
    (A : Matrix E Rows ℝ) (b : E → ℝ) (pick : F → E)
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b q)
    (hspan : rowSpace (Matrix.fromRows NO (fun f => A (pick f))) =
      rowSpace (Matrix.fromRows NO A))
    (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w) (hGlobal : GlobalMarkov G val p)
    (hselected : ∀ f, score (A (pick f)) (districtFactor G.observed val (observedDistrict G) d p) =
      b (pick f)) :
    Feasible A b (districtFactor G.observed val (observedDistrict G) d p) := by
  classical
  let r₀ : Profiles := Classical.choice inferInstance
  have hA₀ : Feasible A b (fun x => C x r₀) := (hhull _).mp (mem_affineSpan ℝ ⟨r₀, rfl⟩)
  let B := Matrix.fromRows NO (fun f => A (pick f))
  let brhs := Sum.elim rhs (fun f => b (pick f))
  have hB₀ : Feasible B brhs (fun x => C x r₀) := by
    intro index
    cases index with
    | inl e => exact constraints_column G val d r₀ e
    | inr f => exact hA₀ (pick f)
  apply feasible_of_rowSpace_le B brhs A b _ hB₀ hA₀
  · change rowSpace A ≤ rowSpace (Matrix.fromRows NO (fun f => A (pick f)))
    rw [hspan, rowSpace_fromRows]
    exact le_sup_right
  · intro index
    cases index with
    | inl e => exact observable_constraints G val p hpos hGlobal d e
    | inr f => exact hselected f

end MeraConstraints.CompactDistrict
