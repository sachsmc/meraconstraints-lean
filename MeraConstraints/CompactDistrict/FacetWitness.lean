import MeraConstraints.GlobalModel.SingleKernelPolytope
import MeraConstraints.CompactDistrict.EqualityRank

/-!
# An observed law violating only one nontrivial facet

Proposition `prop:nontrivial` (ii), the final assertion. Genuine distinct
proper facets give a positive kernel violating the selected nontrivial facet
and strictly satisfying every other inequality. The kernel remains in the
actual affine hull, so all (N)/(O) equations hold there as well.

The strengthened single-kernel reconstruction then gives a strictly positive
normalized observed law satisfying all global graphical independencies.
Its selected district factor is exactly the violating kernel; all its other
district factors are inside their actual response polytopes. Consequently
every equality and every other inequality of every checked H-system holds.

Affine-hull exactness and proper, distinct codimension-one facets are checked
inputs, matching the manuscript. Neither a positive observed-law witness nor
a facet-span certificate is assumed. Numerical H-conversion is not certified
by the theorem.
-/

namespace MeraConstraints.CompactDistrict

open HiddenGraph EqualityConstraints Geometry
open GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] (d : DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (observedDistrict G) d
local notation "C" => matrix G.observed val (observedDistrict G) d

/-- The positive geometric witness on the actual district rows, with all
(N)/(O) equations derived from affine-hull membership. -/
theorem positive_facet_kernel {E I : Type*} [Fintype E] [Fintype I]
    (A : Matrix E Rows ℝ) (b : E → ℝ) (h : I → Rows → ℝ) (c : I → ℝ) (f : I)
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b q)
    (hvalid : ∀ g r, 0 ≤ slack (h g) (c g) (fun x => C x r))
    (hproper : ∀ g, ∃ r, 0 < slack (h g) (c g) (fun x => C x r))
    (hincident : ∀ g, (MeraConstraints.FacetCriterion.incidentColumns C (h g) (c g)).Nonempty)
    (hdim : ∀ g, Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull C).direction =
      Module.finrank ℝ (MeraConstraints.FacetCriterion.incidentHull C (h g) (c g)).direction + 1)
    (hdistinct : ∀ g, g ≠ f →
      MeraConstraints.FacetCriterion.incidentHull C (h f) (c f) ≠
        MeraConstraints.FacetCriterion.incidentHull C (h g) (c g))
    (hnontrivial : ¬ KernelTrivial G val d A b (h f) (c f)) :
    ∃ q : Rows → ℝ, (∀ x, 0 < q x) ∧ Feasible A b q ∧
      Feasible (OrderingConstraints.constraintsMatrix G val d)
        (OrderingConstraints.constraintsRhs G val d) q ∧
      slack (h f) (c f) q < 0 ∧ ∀ g, g ≠ f → 0 < slack (h g) (c g) q := by
  classical
  have hspan := MeraConstraints.FacetCriterion.facetSpan_of_codimension_one C A b (h f) (c f)
    hhull (hincident f) (hproper f) (hdim f)
  have he : ∀ r, Feasible A b (fun x => C x r) := fun r =>
    (hhull _).mp (mem_affineSpan ℝ ⟨r, rfl⟩)
  have htight : (MeraConstraints.FacetCriterion.incidentIndices C (h f) (c f)).Nonempty := by
    obtain ⟨_, r, hr, rfl⟩ := hincident f
    exact ⟨r, (MeraConstraints.FacetCriterion.mem_incidentIndices _ _ _ _).mpr hr⟩
  have hsep : ∀ g, g ≠ f → ∃ q, Feasible A b q ∧
      slack (h f) (c f) q = 0 ∧ slack (h g) (c g) q ≠ 0 := by
    intro g hg
    obtain ⟨r, hrf, hrg⟩ := MeraConstraints.FacetCriterion.strict_incident_column_of_distinct_facets
      C A b (h f) (h g) (c f) (c g) hhull (hincident f) (hincident g)
      (hproper g) (hvalid g) (hdim f) (hdim g) (hdistinct g hg)
    exact ⟨_, he r, hrf, ne_of_gt hrg⟩
  have hno : ¬ ∃ x : Rows, ∀ r : Profiles,
      slack (h f) (c f) (fun y => C y r) = 0 → C x r = 0 := by
    intro hz
    exact hnontrivial ((kernel_trivial_iff_incident_zero G val d A b h c f
      hhull hvalid hproper hincident hdim hdistinct).mpr hz)
  obtain ⟨q, hq, hA, hv, hother⟩ := MeraConstraints.FacetCriterion.positive_violator_of_no_incident_zero
    C A b h c f hspan (compatibility_nonneg G val d) he hvalid (hproper f) htight hsep hno
  refine ⟨q, hq, hA, ?_, hv, hother⟩
  intro index
  apply MeraConstraints.FacetCriterion.equation_on_affineSpan
    (Set.range fun r : Profiles => fun x : Rows => C x r)
    (OrderingConstraints.constraintsMatrix G val d index) (OrderingConstraints.constraintsRhs G val d index)
  · rintro _ ⟨r, rfl⟩
    exact constraints_column G val d r index
  · exact (hhull q).mpr hA

/-- Proposition `prop:nontrivial` (ii): a nontrivial facet can be violated by
a positive globally Markov observed distribution satisfying every equality
and every other district inequality. The other selected-district facets
are satisfied strictly. -/
theorem observed_law_violating_only_facet
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    [∀ e, Fintype (I e)] [∀ e, Fintype (E e)]
    (H : ∀ e, Polytope.HRep (matrix G.observed val (observedDistrict G) e) (I e) (E e)) (f : I d)
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔
      Feasible (H d).equalities (H d).target q)
    (hproper : ∀ g, ∃ r : Profiles,
      0 < slack ((H d).inequalities g) ((H d).upper g) (fun x => C x r))
    (hincident : ∀ g, (MeraConstraints.FacetCriterion.incidentColumns C
      ((H d).inequalities g) ((H d).upper g)).Nonempty)
    (hdim : ∀ g, Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull C).direction =
      Module.finrank ℝ (MeraConstraints.FacetCriterion.incidentHull C
        ((H d).inequalities g) ((H d).upper g)).direction + 1)
    (hdistinct : ∀ g, g ≠ f →
      MeraConstraints.FacetCriterion.incidentHull C ((H d).inequalities f) ((H d).upper f) ≠
        MeraConstraints.FacetCriterion.incidentHull C ((H d).inequalities g) ((H d).upper g))
    (hnontrivial : ¬ KernelTrivial G val d (H d).equalities (H d).target
      ((H d).inequalities f) ((H d).upper f)) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      MoralGlobalMarkov G val p ∧
      (∀ e, Feasible (H e).equalities (H e).target
        (observableFactor G.observed val (observedDistrict G) e p)) ∧
      (H d).upper f < score ((H d).inequalities f)
        (observableFactor G.observed val (observedDistrict G) d p) ∧
      (∀ g, g ≠ f → score ((H d).inequalities g)
        (observableFactor G.observed val (observedDistrict G) d p) < (H d).upper g) ∧
      ∀ e, e ≠ d → ∀ g, score ((H e).inequalities g)
        (observableFactor G.observed val (observedDistrict G) e p) ≤ (H e).upper g := by
  classical
  have hvalid (g : I d) (r : Profiles) :
      0 ≤ slack ((H d).inequalities g) ((H d).upper g) (fun x => C x r) := by
    have hr := ((H d).exact_representation _).mp (column_mem_mixture G val d r)
    exact sub_nonneg.mpr (hr.1 g)
  obtain ⟨q, hq, hA, hNO, hv, hother⟩ := positive_facet_kernel G val d
    (H d).equalities (H d).target (H d).inequalities (H d).upper f
    hhull hvalid hproper hincident hdim hdistinct hnontrivial
  obtain ⟨p, hp, hpos, hGlobal, hfactor, hrest⟩ :=
    realize_single_kernel_other_polytopes G val hdegree d q hq hNO
  refine ⟨p, hp, hpos, hGlobal, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases hed : e = d
    · subst e
      simpa only [hfactor] using hA
    · exact (((H e).exact_representation _).mp (hrest e hed)).2
  · rw [hfactor]
    exact sub_neg.mp hv
  · intro g hg
    rw [hfactor]
    exact sub_pos.mp (hother g hg)
  · intro e he g
    exact (((H e).exact_representation _).mp (hrest e he)).1 g

end MeraConstraints.CompactDistrict
