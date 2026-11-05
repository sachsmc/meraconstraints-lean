import MeraConstraints.GlobalModel.SingleKernelPolytope
import MeraConstraints.CompactDistrict.EqualityRank

/-!
# A distribution that violates only one nontrivial inequality

This chapter proves the last claim of Proposition 4 (`prop:nontrivial`) (ii): if an
inequality is nontrivial, some strictly positive distribution of the observed
variables satisfies the conditional independencies and every constraint of every
district except this one, which it violates. The hypotheses are those of the
proposition (c-degree at most 1, the rows of `H_e` define the affine hull, each row of
`H_i` defines a different facet), together with the nontriviality of the inequality.

The proof follows Step 4 of the proof in the Supplementary Materials.
`positive_facet_kernel` constructs a strictly positive vector `q` on the affine hull
of the district polytope that violates the inequality and satisfies every other
inequality of the district strictly. By Step 1, `q` satisfies (N) and (O).
The reconstruction of Step 2 (`realize_single_kernel_other_polytopes`) turns `q` into
the observed distribution, whose district factor is `q` for this district and lies
in the district polytope for every other district.
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

/-- A strictly positive vector `q` that satisfies `A q = b`, (N) and (O), violates
the nontrivial inequality `f`, and satisfies every other inequality strictly. -/
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
    (hnontrivial : ¬ InequalityTrivial G val d A b (h f) (c f)) :
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
    exact hnontrivial ((inequalityTrivial_iff_incident_zero G val d A b h c f
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

/-- Proposition 4 (`prop:nontrivial`) (ii), last claim: for a nontrivial
inequality `f` of district `d`, there is a strictly positive distribution that
satisfies the conditional independencies and all equality constraints of all
districts, violates `f`, and satisfies every other inequality of every district.
The other inequalities of `d` hold strictly. -/
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
    (hnontrivial : ¬ InequalityTrivial G val d (H d).equalities (H d).target
      ((H d).inequalities f) ((H d).upper f)) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      GlobalMarkov G val p ∧
      (∀ e, Feasible (H e).equalities (H e).target
        (districtFactor G.observed val (observedDistrict G) e p)) ∧
      (H d).upper f < score ((H d).inequalities f)
        (districtFactor G.observed val (observedDistrict G) d p) ∧
      (∀ g, g ≠ f → score ((H d).inequalities g)
        (districtFactor G.observed val (observedDistrict G) d p) < (H d).upper g) ∧
      ∀ e, e ≠ d → ∀ g, score ((H e).inequalities g)
        (districtFactor G.observed val (observedDistrict G) e p) ≤ (H e).upper g := by
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
