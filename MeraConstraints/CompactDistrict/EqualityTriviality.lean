import MeraConstraints.GlobalModel.SingleKernel
import MeraConstraints.EqualityConstraints.Rank

/-!
# Trivial equality constraints

This chapter proves the first claim of Proposition 4 (`prop:nontrivial`) (i): an
equality constraint `gᵀp = c` is trivial if and only if it is a linear combination
of equations (N) and (O), with the same weights for the coefficients and the
right-hand sides. `EqualityTrivial` is Definition 4 (trivial constraints) for
equalities. It holds for every strictly positive distribution of the observed
variables that satisfies the conditional independencies implied by the graph.

The proof follows Steps 1 to 3 of the proof in the Supplementary Materials. Every such
distribution has a district factor that solves (N) and (O)
(`GlobalModel.ObservableConstraints`, Step 1). Conversely, with c-degree at most 1,
every strictly positive solution of (N) and (O) is the district factor of such a
distribution (`realize_single_positive_kernel`, Step 2). So an equation is trivial if
and only if it holds at every strictly positive solution of (N) and (O), and the
affine-consequence theorem for the uniform point turns this into a linear
combination (Step 3).
-/

namespace MeraConstraints.CompactDistrict

open HiddenGraph EqualityConstraints OrderingConstraints
open GlobalModel.KernelReconstruction GlobalModel.OrderingInvariance

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] (d : DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (observedDistrict G) d

/-- Definition 4 for equalities: `gᵀp = c` holds for the district factor `p` of
every strictly positive observed distribution that satisfies the conditional
independencies implied by the graph. -/
def EqualityTrivial (g : Rows → ℝ) (c : ℝ) : Prop :=
  ∀ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) → (∀ w, 0 < p w) →
    GlobalMarkov G val p → score g (districtFactor G.observed val (observedDistrict G) d p) = c

theorem equalityTrivial_iff_positiveConsequence (hdegree : ∀ x, cDegree G x ≤ 1)
    (g : Rows → ℝ) (c : ℝ) :
    EqualityTrivial G val d g c ↔
      PositiveConsequence (constraintsMatrix G val d) (constraintsRhs G val d) g c := by
  constructor
  · intro h q hq hNO
    obtain ⟨p, hp, hpos, hGlobal, hfactor⟩ :=
      realize_single_positive_kernel G val hdegree d q hq hNO
    simpa only [hfactor] using h p hp hpos hGlobal
  · intro h p _ hpos hGlobal
    have hc := (EqualityConstraints.positive_consequence_iff_consequence _ _ g c
      (uniformKernel G val d) (uniformKernel_feasible G val d) (uniformKernel_pos G val d)).mp h
    exact hc _ (observable_constraints G val p hpos hGlobal d)

/-- Proposition 4 (`prop:nontrivial`) (i), first claim: `gᵀp = c` is trivial if and
only if it is a linear combination of (N) and (O), with the same weights for `g` and
`c`. No H-representation is involved. -/
theorem equalityTrivial_iff_rowCombination (hdegree : ∀ x, cDegree G x ≤ 1)
    (g : Rows → ℝ) (c : ℝ) :
    EqualityTrivial G val d g c ↔
      RowCombination (constraintsMatrix G val d) (constraintsRhs G val d) g c :=
  (equalityTrivial_iff_positiveConsequence G val d hdegree g c).trans
    (positive_equation_iff_rowCombination G val d g c)

/-- The coefficient vectors `g` of trivial equality constraints. It is defined
from Definition 4 and does not refer to (N) and (O). -/
def graphTrivialSpace : Submodule ℝ (Rows → ℝ) where
  carrier := {g | ∃ c, EqualityTrivial G val d g c}
  zero_mem' := ⟨0, by intro p _ _ _; simp [score]⟩
  add_mem' := by
    rintro g h ⟨c, hc⟩ ⟨b, hb⟩
    refine ⟨c + b, ?_⟩
    intro p hp hpos hGlobal
    simpa only [score, Pi.add_apply, add_mul, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hc p hp hpos hGlobal) (hb p hp hpos hGlobal)
  smul_mem' := by
    rintro a g ⟨c, hc⟩
    refine ⟨a * c, ?_⟩
    intro p hp hpos hGlobal
    simpa only [score, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] using
      congrArg (a * ·) (hc p hp hpos hGlobal)

/-- The trivial coefficient vectors are the row space of (N) and (O). -/
theorem graphTrivialSpace_eq_rowSpace (hdegree : ∀ x, cDegree G x ≤ 1) :
    graphTrivialSpace G val d = rowSpace (constraintsMatrix G val d) := by
  classical
  ext g
  constructor
  · rintro ⟨c, hc⟩
    have hcon := (EqualityConstraints.positive_consequence_iff_consequence _ _ g c
      (uniformKernel G val d) (uniformKernel_feasible G val d) (uniformKernel_pos G val d)).mp
      ((equalityTrivial_iff_positiveConsequence G val d hdegree g c).mp hc)
    exact mem_rowSpan_of_consequence _ _ g c _ (uniformKernel_feasible G val d) hcon
  · intro hg
    obtain ⟨weights, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
    refine ⟨∑ e, weights e * constraintsRhs G val d e,
      (equalityTrivial_iff_rowCombination G val d hdegree g _).mpr ⟨weights, ?_, rfl⟩⟩
    intro j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using
      (congrFun hw j).symm

end MeraConstraints.CompactDistrict
