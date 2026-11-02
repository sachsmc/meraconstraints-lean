import MeraConstraints.FacetCriterion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Deriving the facet-span certificate from codimension one

The manuscript says each inequality row defines a proper facet relative to
the district polytope's affine hull. `FacetSpan` makes the affine consequence
of that hypothesis explicit: the incident-column span equals the full hull
intersected with the supporting hyperplane. This chapter derives that
certificate from actual affine incidence and codimension data.

Let `F` be the affine span of the incident columns and `L` the affine span
of all columns. Every point of `F` lies in `L` and on the plane. An incident
column makes `F` nonempty; a strictly off-plane column makes the intersection
`L ∩ plane` a proper subspace of `L`. If the direction dimension of `L` is
one more than that of `F`, no affine subspace can fit strictly between them.
This proves the required equality without assuming a coordinate-zero
criterion or its desired nonnegativity certificate.

Distinct incident spans of the same codimension cannot contain one another.
For valid supporting inequalities this also supplies an incident column of
one facet on which the other inequality is strict, the input needed for the
strictness of every other constraint at a facet average.
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

/-- The actual affine supporting hyperplane, including possibly degenerate
coefficient data. Properness is established separately from an off-plane point. -/
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

/-- A nonempty codimension-one affine subspace is maximal among the proper
affine subspaces of its ambient hull. -/
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

/-- `FacetSpan` follows from affine-hull equations, actual incidence,
properness and the facet's codimension-one direction rank. Validity of the
supporting inequality is not needed for this affine-span identity itself. -/
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

/-- Distinct nonempty affine subspaces of the same finite direction dimension
cannot be nested. Applied to codimension-one incident spans, this is the
geometric meaning of different facet rows, independent of row scaling. -/
theorem not_le_of_distinct_equal_dimension
    (F₁ F₂ : AffineSubspace ℝ (Row → ℝ))
    (hne : (F₁ : Set (Row → ℝ)).Nonempty) (hdistinct : F₁ ≠ F₂)
    (hdim : Module.finrank ℝ F₁.direction = Module.finrank ℝ F₂.direction) :
    ¬ F₁ ≤ F₂ := by
  intro hle
  exact hdistinct (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim) hne hle)

/-- If two proper codimension-one incident spans differ, some column on the
first facet is strict on the other valid supporting inequality. This supplies
the other-facet strictness used when averaging incident columns. -/
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
