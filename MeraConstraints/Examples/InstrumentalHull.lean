import MeraConstraints.Examples.InstrumentalExact
import MeraConstraints.Polytope.HRepAffine
import MeraConstraints.FacetCriterion.Span
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The affine hull of the instrumental variable polytope

The two rows of `H_e` are the normalizations of the entries with `Z = 0` and
with `Z = 1`. This chapter shows that the affine hull of the columns of
`printedB` is exactly the set of vectors satisfying these two equations
(`printed_columnHull_iff`), and that it has dimension six
(`printed_columnHull_finrank`). This is the hypothesis of Proposition 4
(`prop:nontrivial`) that the rows of `H_e` define the affine hull, here for the
instrumental variable district. Vectors in the hull may have negative entries.

Seven columns are selected (4, 7, 10, 12, 13, 14 and 15 in one-based numbering).
Every vector satisfying the two normalizations is an affine combination of them,
with the weights `affineWeight`. Conversely, every column satisfies the two
equations, so the hull is contained in the solution set. An explicit inverse of
the combination of the seven columns shows that they are linearly, hence
affinely, independent. They form an affine basis, so the hull has dimension six.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

open EqualityConstraints

theorem probability_coordinates (p : Fin 8 → ℝ) :
    p = ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7] := by
  funext i
  fin_cases i <;> rfl

theorem printed_equalities_iff (p : Fin 8 → ℝ) :
    Feasible printedHe printedTarget p ↔
      p 0 + p 1 + p 2 + p 3 = 1 ∧ p 4 + p 5 + p 6 + p 7 = 1 := by
  constructor
  · intro hp
    have h0 := hp 0
    have h1 := hp 1
    change (∑ i : Fin 8, ![-1,-1,-1,-1,0,0,0,0] i * p i) = -1 at h0
    change (∑ i : Fin 8, ![0,0,0,0,-1,-1,-1,-1] i * p i) = -1 at h1
    rw [probability_coordinates p] at h0 h1
    norm_num [Fin.sum_univ_succ] at h0 h1
    constructor <;> linarith only [h0, h1]
  · rintro ⟨h0, h1⟩ e
    change (∑ i, printedHe e i * p i) = printedTarget e
    rw [probability_coordinates p]
    fin_cases e <;> norm_num [printedHe, printedTarget, Fin.sum_univ_succ] <;>
      linarith only [h0, h1]

/-- Zero-based indices of the seven selected columns of `printedB`. -/
def affineColumn : Fin 7 → Fin 16 := ![3,6,9,11,12,13,14]

def affineWeight (p : Fin 8 → ℝ) : Fin 7 → ℝ :=
  ![p 0, p 1, p 5, p 2 - p 5, p 4, p 3 - p 4 - p 6 + p 1, p 6 - p 1]

/-- The combination of the seven selected columns with coefficients `w`, as a
vector in the eight coordinates. -/
def sevenColumnMap (w : Fin 7 → ℝ) : Fin 8 → ℝ :=
  ![w 0, w 1, w 2 + w 3, w 4 + w 5 + w 6, w 4, w 2,
    w 1 + w 6, w 0 + w 3 + w 5]

set_option maxHeartbeats 2000000 in
theorem sevenColumn_combination (w : Fin 7 → ℝ) :
    (∑ j : Fin 7, w j • (fun i : Fin 8 => printedB i (affineColumn j))) = sevenColumnMap w := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5, w 6] := by
    funext j
    fin_cases j <;> rfl
  rw [hw]
  funext i
  fin_cases i <;>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    dsimp [affineColumn, printedB, sevenColumnMap, Matrix.vecCons, Fin.cons, Fin.cases,
      Fin.induction, Fin.induction.go] <;> ring

theorem affineWeight_sevenColumnMap (w : Fin 7 → ℝ) : affineWeight (sevenColumnMap w) = w := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5, w 6] := by
    funext j
    fin_cases j <;> rfl
  rw [hw]
  funext j
  fin_cases j <;>
    dsimp [affineWeight, sevenColumnMap, Matrix.vecCons, Fin.cons, Fin.cases,
      Fin.induction, Fin.induction.go] <;> ring

theorem affineWeight_sum {p : Fin 8 → ℝ} (hp : Feasible printedHe printedTarget p) :
    (∑ j, affineWeight p j) = 1 := by
  have h0 := ((printed_equalities_iff p).mp hp).1
  norm_num [affineWeight, Fin.sum_univ_succ]
  linarith only [h0]

theorem sevenColumnMap_affineWeight {p : Fin 8 → ℝ} (hp : Feasible printedHe printedTarget p) :
    sevenColumnMap (affineWeight p) = p := by
  obtain ⟨h0, h1⟩ := (printed_equalities_iff p).mp hp
  rw [probability_coordinates p]
  funext i
  fin_cases i <;>
    dsimp [sevenColumnMap, affineWeight, Matrix.vecCons, Fin.cons, Fin.cases,
      Fin.induction, Fin.induction.go] <;> linarith only [h0, h1]

/-- Every vector satisfying the two normalizations is an affine combination of
the seven selected columns. -/
theorem normalized_mem_sevenColumnHull {p : Fin 8 → ℝ} (hp : Feasible printedHe printedTarget p) :
    p ∈ affineSpan ℝ (Set.range fun j : Fin 7 => fun i : Fin 8 => printedB i (affineColumn j)) := by
  have hw : ∑ j ∈ (Finset.univ : Finset (Fin 7)), affineWeight p j = 1 := affineWeight_sum hp
  have hm := affineCombination_mem_affineSpan hw
    (fun j : Fin 7 => fun i : Fin 8 => printedB i (affineColumn j))
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
    sevenColumn_combination, sevenColumnMap_affineWeight hp] at hm
  exact hm

/-- The affine hull of the columns of `printedB` is the set of vectors with
`H_e p = b_e`. -/
theorem printed_columnHull_iff (p : Fin 8 → ℝ) :
    p ∈ MeraConstraints.FacetCriterion.columnHull printedB ↔ Feasible printedHe printedTarget p := by
  constructor
  · intro hp
    apply printedHRep.equalities_on_affineSpan p
    rw [Polytope.mixture_eq_convexHull, affineSpan_convexHull]
    exact hp
  · intro hp
    have hm := normalized_mem_sevenColumnHull hp
    exact (affineSpan_mono ℝ (by
      rintro _ ⟨j, rfl⟩
      exact ⟨affineColumn j, rfl⟩)) hm

theorem printed_columnHull_eq_seven :
    MeraConstraints.FacetCriterion.columnHull printedB =
      affineSpan ℝ (Set.range fun j : Fin 7 => fun i : Fin 8 => printedB i (affineColumn j)) := by
  apply le_antisymm
  · intro p hp
    exact normalized_mem_sevenColumnHull ((printed_columnHull_iff p).mp hp)
  · apply affineSpan_mono ℝ
    rintro _ ⟨j, rfl⟩
    exact ⟨affineColumn j, rfl⟩

theorem sevenColumn_linearIndependent :
    LinearIndependent ℝ (fun j : Fin 7 => fun i : Fin 8 => printedB i (affineColumn j)) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro w v h
  simp only [Fintype.linearCombination_apply, sevenColumn_combination] at h
  have hh := congrArg affineWeight h
  simpa only [affineWeight_sevenColumnMap] using hh

theorem printed_columnHull_finrank :
    Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull printedB).direction = 6 := by
  rw [printed_columnHull_eq_seven, direction_affineSpan]
  exact sevenColumn_linearIndependent.affineIndependent.finrank_vectorSpan (by decide)

end MeraConstraints.Examples.Instrumental.Appendix
