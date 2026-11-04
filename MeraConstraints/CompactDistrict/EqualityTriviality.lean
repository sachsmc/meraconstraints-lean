import MeraConstraints.GlobalModel.SingleKernel
import MeraConstraints.EqualityConstraints.Rank

/-!
# Graph-trivial equalities are precisely the (N)/(O) row combinations

This is Proposition `prop:nontrivial` (i), the equality iff. Triviality is
defined by quantifying over normalized positive observed distributions and
the graph's global conditional independencies, as in `def:nontrivial`.
It is not defined by kernel feasibility or by a row-span condition.

The single-kernel realization theorem identifies this domain with positive
(N)/(O) kernels. The checked affine-consequence theorem then extends an
equation to the full affine solution set and obtains its row combination,
with the same weights for coefficients and right-hand sides.
-/

namespace MeraConstraints.CompactDistrict

open HiddenGraph EqualityConstraints OrderingConstraints
open GlobalModel.KernelReconstruction GlobalModel.OrderingInvariance

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] (d : DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (observedDistrict G) d

/-- Equality triviality from the manuscript's definition, on actual observed
probability laws satisfying all graphical conditional independencies. -/
def EqualityTrivial (g : Rows → ℝ) (c : ℝ) : Prop :=
  ∀ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) → (∀ w, 0 < p w) →
    MoralGlobalMarkov G val p → score g (observableFactor G.observed val (observedDistrict G) d p) = c

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

/-- Proposition `prop:nontrivial` (i), including the affine constants.
No H-representation exactness is needed for this equality characterization. -/
theorem equalityTrivial_iff_rowCombination (hdegree : ∀ x, cDegree G x ≤ 1)
    (g : Rows → ℝ) (c : ℝ) :
    EqualityTrivial G val d g c ↔
      RowCombination (constraintsMatrix G val d) (constraintsRhs G val d) g c :=
  (equalityTrivial_iff_positiveConsequence G val d hdegree g c).trans
    (positive_equation_iff_rowCombination G val d g c)

/-- The intrinsic vector space of graph-trivial equality coefficients.
Its carrier quantifies over observed laws, independently of (N)/(O). -/
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

/-- Semantic identification needed to interpret the manuscript's rank count. -/
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
