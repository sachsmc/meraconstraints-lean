import MeraConstraints.HiddenGraph.InstrumentalInequalities
import MeraConstraints.CompactDistrict.FacetWitness

/-!
# Instrumental structure: a distribution violating one inequality

Remark 3 (`prop:ineqstructure`), type (i), gives a nontrivial inequality in the
H-representation of the district. Proposition 4 (`prop:nontrivial`) (ii) says that
a nontrivial inequality can be violated on its own. Combining the two gives a
strictly positive observed distribution that satisfies the conditional
independencies, all equality constraints, and every inequality constraint
except that one.

As in Proposition 4, the hypotheses say that the rows of `H_e` define the affine
hull of the district polytope and that the rows of `H_i` define different facets
(`hhull`, `hproper`, `hincident`, `hdim`, `hdistinct`). The graph has c-degree at
most 1.
-/

namespace MeraConstraints.Completeness

open HiddenGraph CompactDistrict EqualityConstraints Geometry GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] (d : DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (observedDistrict G) d
local notation "C" => matrix G.observed val (observedDistrict G) d

theorem instrumental_structure_positive_witness
    (hdegree : ∀ x, cDegree G x ≤ 1) (hstructure : InstrumentalStructure G d)
    (hlevels : HasTwoLevels G.observed val (observedDistrict G) d)
    {I E : DistrictId G → Type*} [∀ e, Fintype (I e)] [∀ e, Fintype (E e)]
    (H : ∀ e, Polytope.HRep (matrix G.observed val (observedDistrict G) e) (I e) (E e))
    (hhull : ∀ q, q ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible (H d).equalities (H d).target q)
    (hproper : ∀ g, ∃ r : Profiles,
      0 < slack ((H d).inequalities g) ((H d).upper g) (fun x => C x r))
    (hincident : ∀ g, (MeraConstraints.FacetCriterion.incidentColumns C
      ((H d).inequalities g) ((H d).upper g)).Nonempty)
    (hdim : ∀ g, Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull C).direction =
      Module.finrank ℝ (MeraConstraints.FacetCriterion.incidentHull C
        ((H d).inequalities g) ((H d).upper g)).direction + 1)
    (hdistinct : ∀ f g : I d, g ≠ f →
      MeraConstraints.FacetCriterion.incidentHull C ((H d).inequalities f) ((H d).upper f) ≠
        MeraConstraints.FacetCriterion.incidentHull C ((H d).inequalities g) ((H d).upper g)) :
    ∃ f : I d, ∃ p : FullAssign val → ℝ,
      p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧ GlobalMarkov G val p ∧
      (∀ e, Feasible (H e).equalities (H e).target
        (districtFactor G.observed val (observedDistrict G) e p)) ∧
      (H d).upper f < score ((H d).inequalities f)
        (districtFactor G.observed val (observedDistrict G) d p) ∧
      (∀ g, g ≠ f → score ((H d).inequalities g)
        (districtFactor G.observed val (observedDistrict G) d p) < (H d).upper g) ∧
      ∀ e, e ≠ d → ∀ g, score ((H e).inequalities g)
        (districtFactor G.observed val (observedDistrict G) e p) ≤ (H e).upper g := by
  obtain ⟨f, hf⟩ := instrumental_nontrivial_H_row G d val (H d) hstructure hlevels
  obtain ⟨p, hp⟩ := observed_law_violating_only_facet G val d hdegree H f
    hhull hproper hincident hdim (hdistinct f) hf
  exact ⟨f, p, hp⟩

end MeraConstraints.Completeness
