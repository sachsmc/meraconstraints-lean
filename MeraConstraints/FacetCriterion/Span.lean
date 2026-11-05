import MeraConstraints.FacetCriterion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The span of a facet from its dimension

The manuscript says each inequality of `H_i` defines a facet of the district
polytope, relative to its affine hull. This file proves that the affine span of
the columns of `B` on the facet equals the affine hull intersected with the
hyperplane `hᵀp = c` (`FacetSpan`), from the dimension of the facet.

Let `F` be the affine span of the columns on the hyperplane and `L` the affine
hull of all columns (`incidentHull`, `columnHull`). Then `F` lies in `L` and on
the hyperplane, and `F` is nonempty. A column off the hyperplane makes the intersection
`L ∩ hyperplane` a proper subspace of `L`. If the dimension of `L` is one more
than that of `F`, no affine subspace fits strictly between them, so
`F = L ∩ hyperplane`.

Two different affine spans of the same dimension cannot contain one another. So
for two different facets, some column on the first is strict for the inequality of
the second. This is used to show that the average of the columns on a facet
satisfies every other inequality strictly.
-/

namespace MeraConstraints.FacetCriterion

open EqualityConstraints Geometry

variable {Row Col E : Type*} [Fintype Row]

noncomputable def columnHull (B : Matrix Row Col ℝ) : AffineSubspace ℝ (Row → ℝ) :=
  affineSpan ℝ (Set.range fun j => fun i => B i j)

noncomputable def incidentHull (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) :
    AffineSubspace ℝ (Row → ℝ) := affineSpan ℝ (incidentColumns B h c)

private theorem score_step (g : Row → ℝ) (t : ℝ) (x y z : Row → ℝ) :
    score g (t • (x -ᵥ y) +ᵥ z) = t * (score g x - score g y) + score g z := by
  simp only [score, vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  calc
    _ = ∑ i, (t * (g i * x i - g i * y i) + g i * z i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- The affine subspace `{p : hᵀp = c}`. -/
def equationPlane (h : Row → ℝ) (c : ℝ) : AffineSubspace ℝ (Row → ℝ) where
  carrier := {p | score h p = c}
  smul_vsub_vadd_mem := by
    intro t x y z hx hy hz
    change score h (t • (x -ᵥ y) +ᵥ z) = c
    rw [score_step, hx, hy, hz]
    ring

theorem incidentHull_le_columnHull (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) :
    incidentHull B h c ≤ columnHull B := by
  apply affineSpan_mono ℝ
  rintro _ ⟨j, _, rfl⟩
  exact ⟨j, rfl⟩

theorem incidentHull_le_equationPlane (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) :
    incidentHull B h c ≤ equationPlane h c := by
  apply affineSpan_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  change score h (fun i => B i j) = c
  change c - score h (fun i => B i j) = 0 at hj
  linarith

/-- If `F ≤ T < L`, `F` is nonempty, and the dimension of `L` is one more than that
of `F`, then `F = T`. -/
theorem eq_of_between_codimension_one
    (F T L : AffineSubspace ℝ (Row → ℝ))
    (hFT : F ≤ T) (hTL : T < L) (hne : (F : Set (Row → ℝ)).Nonempty)
    (hdim : Module.finrank ℝ L.direction = Module.finrank ℝ F.direction + 1) : F = T := by
  have hTne : (T : Set (Row → ℝ)).Nonempty := hne.mono hFT
  have hdirTL := AffineSubspace.direction_lt_of_nonempty hTL hTne
  have hdimTL := Submodule.finrank_lt_finrank_of_lt hdirTL
  have hdirFT := AffineSubspace.direction_le hFT
  have hdimFT := Submodule.finrank_mono hdirFT
  have heqdim : Module.finrank ℝ F.direction = Module.finrank ℝ T.direction := by omega
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq hdirFT heqdim) hne hFT

/-- `FacetSpan` holds when the equations define the affine hull of the columns,
some column is on the hyperplane, some column is off it, and the span of the
columns on the hyperplane has dimension one less than the hull. The inequality
need not be valid for this. -/
theorem facetSpan_of_codimension_one
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ) (h : Row → ℝ) (c : ℝ)
    (hhull : ∀ p, p ∈ columnHull B ↔ Feasible A b p)
    (hincident : (incidentColumns B h c).Nonempty)
    (hoff : ∃ j, 0 < slack h c (fun i => B i j))
    (hdim : Module.finrank ℝ (columnHull B).direction =
      Module.finrank ℝ (incidentHull B h c).direction + 1) :
    FacetSpan B A b h c := by
  let F := incidentHull B h c
  let L := columnHull B
  let T := L ⊓ equationPlane h c
  have hFT : F ≤ T := le_inf
    (incidentHull_le_columnHull B h c) (incidentHull_le_equationPlane B h c)
  have hFne : (F : Set (Row → ℝ)).Nonempty := by
    obtain ⟨x, hx⟩ := hincident
    exact ⟨x, mem_affineSpan ℝ hx⟩
  have hTL : T < L := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    obtain ⟨j, hj⟩ := hoff
    have hjL : (fun i => B i j) ∈ L := mem_affineSpan ℝ ⟨j, rfl⟩
    have hjT : (fun i => B i j) ∈ T := by
      exact Eq.mpr (congrArg (fun S : AffineSubspace ℝ (Row → ℝ) =>
        (fun i => B i j) ∈ S) heq) hjL
    have hscore : score h (fun i => B i j) = c := hjT.2
    have hzero : slack h c (fun i => B i j) = 0 := by
      change c - score h (fun i => B i j) = 0
      rw [hscore]
      exact sub_self _
    exact hj.ne' hzero
  have hEq : F = T := eq_of_between_codimension_one F T L hFT hTL hFne hdim
  intro p
  constructor
  · intro hp
    have hpT : p ∈ T := by
      exact Eq.mp (congrArg (fun S : AffineSubspace ℝ (Row → ℝ) => p ∈ S) hEq) hp
    refine ⟨(hhull p).mp hpT.1, ?_⟩
    change c - score h p = 0
    rw [show score h p = c from hpT.2]
    exact sub_self _
  · rintro ⟨hp, hzero⟩
    have hpT : p ∈ T := by
      refine ⟨(hhull p).mpr hp, ?_⟩
      change score h p = c
      change c - score h p = 0 at hzero
      linarith
    exact Eq.mpr (congrArg (fun S : AffineSubspace ℝ (Row → ℝ) => p ∈ S) hEq) hpT

/-- A nonempty affine subspace is not contained in a different one of the same
dimension. -/
theorem not_le_of_distinct_equal_dimension
    (F₁ F₂ : AffineSubspace ℝ (Row → ℝ))
    (hne : (F₁ : Set (Row → ℝ)).Nonempty) (hdistinct : F₁ ≠ F₂)
    (hdim : Module.finrank ℝ F₁.direction = Module.finrank ℝ F₂.direction) :
    ¬ F₁ ≤ F₂ := by
  intro hle
  exact hdistinct (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim) hne hle)

/-- If two facets, each of dimension one less than the affine hull, have different
spans, then some column on the first facet is strict for the (valid) inequality of
the second. -/
theorem strict_incident_column_of_distinct_facets
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h g : Row → ℝ) (c t : ℝ)
    (hhull : ∀ p, p ∈ columnHull B ↔ Feasible A b p)
    (hinc : (incidentColumns B h c).Nonempty)
    (ginc : (incidentColumns B g t).Nonempty)
    (goff : ∃ j, 0 < slack g t (fun i => B i j))
    (hvalid : ∀ j, 0 ≤ slack g t (fun i => B i j))
    (hdim : Module.finrank ℝ (columnHull B).direction =
      Module.finrank ℝ (incidentHull B h c).direction + 1)
    (gdim : Module.finrank ℝ (columnHull B).direction =
      Module.finrank ℝ (incidentHull B g t).direction + 1)
    (hdistinct : incidentHull B h c ≠ incidentHull B g t) :
    ∃ j, slack h c (fun i => B i j) = 0 ∧ 0 < slack g t (fun i => B i j) := by
  classical
  have hnon : ¬ incidentHull B h c ≤ incidentHull B g t := by
    apply not_le_of_distinct_equal_dimension _ _ ?_ hdistinct (by omega)
    obtain ⟨x, hx⟩ := hinc
    exact ⟨x, mem_affineSpan ℝ hx⟩
  have hgspan := facetSpan_of_codimension_one B A b g t hhull ginc goff gdim
  by_contra hn
  apply hnon
  apply affineSpan_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  apply (hgspan _).mpr
  refine ⟨(hhull _).mp (mem_affineSpan ℝ ⟨j, rfl⟩), ?_⟩
  have hnpos : ¬ 0 < slack g t (fun i => B i j) := fun hp => hn ⟨j, hj, hp⟩
  exact le_antisymm (le_of_not_gt hnpos) (hvalid j)

end MeraConstraints.FacetCriterion
