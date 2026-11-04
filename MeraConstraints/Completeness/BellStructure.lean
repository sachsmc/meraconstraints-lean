import MeraConstraints.HiddenGraph.BellInequalities
import MeraConstraints.CompactDistrict.FacetWitness

/-!
# Bell structure gives a positive observed-law violator

The final sentence of manuscript `prop:ineqstructure` (ii) invokes
`prop:nontrivial` (ii). The Bell graph structure and level cardinalities
now supply a nontrivial inequality row. The existing positive-kernel and
global graphical realization theorem gives a strictly positive normalized
observed law violating that row alone while satisfying every equality,
all other selected-district facets strictly, and all other district inequalities.

As in the general facet theorem and the instrumental assembly, exact H-systems,
selected-district affine-hull exactness and genuine proper, distinct
codimension-one facet data are checked inputs. They are not inferred from
numerical output. C-degree is at most one; neither a nontrivial row nor a
positive observed distribution is assumed as input.
-/

namespace MeraConstraints.Completeness

open HiddenGraph CompactDistrict EqualityConstraints Geometry GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] (d : DistrictId G)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]

local notation "Rows" => Row G.observed val (observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (observedDistrict G) d
local notation "C" => matrix G.observed val (observedDistrict G) d

theorem bell_structure_positive_witness
    (hdegree : ∀ x, cDegree G x ≤ 1) (hstructure : BellStructure G d)
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
      p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧ MoralGlobalMarkov G val p ∧
      (∀ e, Feasible (H e).equalities (H e).target
        (observableFactor G.observed val (observedDistrict G) e p)) ∧
      (H d).upper f < score ((H d).inequalities f)
        (observableFactor G.observed val (observedDistrict G) d p) ∧
      (∀ g, g ≠ f → score ((H d).inequalities g)
        (observableFactor G.observed val (observedDistrict G) d p) < (H d).upper g) ∧
      ∀ e, e ≠ d → ∀ g, score ((H e).inequalities g)
        (observableFactor G.observed val (observedDistrict G) e p) ≤ (H e).upper g := by
  obtain ⟨f, hf⟩ := bell_nontrivial_H_row G d val (H d) hstructure hlevels
  obtain ⟨p, hp⟩ := observed_law_violating_only_facet G val d hdegree H f
    hhull hproper hincident hdim (hdistinct f) hf
  exact ⟨f, p, hp⟩

end MeraConstraints.Completeness
