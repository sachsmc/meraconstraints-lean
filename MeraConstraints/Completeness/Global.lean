import MeraConstraints.GlobalModel.GlobalToLocal
import MeraConstraints.Completeness.Graphical
import MeraConstraints.Completeness.ProbabilityModel

/-!
# Proposition 3 and Remark 2 with the graph's conditional independencies

This is the end of the route described in `Completeness.lean`. The two theorems
are Proposition 3 (`prop:complete`) and Remark 2 (`rmk:positivity`) for the
marginal model `ProbabilityModel`, with `GlobalMarkov`, the conditional
independencies implied by the graph, in place of the ordered local Markov
property. They are the statements behind `MainResults.prop_complete` and
`MainResults.rmk_positivity`.

One direction uses that every model in the marginal model satisfies
`GlobalMarkov` (`Completeness/Graphical.lean`). The other uses that `GlobalMarkov`
implies the ordered local Markov property. The conditional independencies are
defined by separation in the ancestral moral graph, including the unobserved
variables.
-/

namespace MeraConstraints.Completeness

open HiddenGraph GlobalModel.KernelReconstruction

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)] [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- Proposition 3 (`prop:complete`). At c-degree at most 1, a strictly positive
`p` is in the marginal model exactly when it satisfies the conditional
independencies implied by the graph and the H-representation constraints on the
district factor of every district. -/
theorem original_model_iff_global_compact_HRep
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔ GlobalMarkov G val p ∧
      ∀ d, (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d p x ≤ (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.districtFactor G.observed val (observedDistrict G) d p x = (H d).target e) := by
  constructor
  · rintro ⟨P, hP⟩
    have hg : GlobalMarkov G val p := hP ▸ probabilityModel_globalMarkov G val hdegree P
    have hc := (original_model_iff_compact_HRep G val hdegree H p hp hpos).mp ⟨P, hP⟩
    exact ⟨hg, hc.2⟩
  · rintro ⟨hg, hH⟩
    exact (original_model_iff_compact_HRep G val hdegree H p hp hpos).mpr
      ⟨globalMarkov_orderedMarkov G val p hg, hH⟩

/-- Remark 2 (`rmk:positivity`). At c-degree at most 1, any distribution `p`,
including one with zero probabilities, is in the marginal model exactly when it
satisfies the conditional independencies implied by the graph and, in every
district, the free entries of the district factor can be chosen so that the
H-representation constraints hold (`Boundary.CompactHCompletion`). -/
theorem original_model_iff_global_boundary_compact_HCompletion
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔
      GlobalMarkov G val p ∧ Boundary.CompactHCompletion G val H p := by
  constructor
  · rintro ⟨P, hP⟩
    have hg : GlobalMarkov G val p := hP ▸ probabilityModel_globalMarkov G val hdegree P
    have hc := (Boundary.original_model_iff_boundary_compact_HCompletion G val hdegree H p hp).mp ⟨P, hP⟩
    exact ⟨hg, hc.2⟩
  · rintro ⟨hg, hH⟩
    exact (Boundary.original_model_iff_boundary_compact_HCompletion G val hdegree H p hp).mpr
      ⟨globalMarkov_orderedMarkov G val p hg, hH⟩

end MeraConstraints.Completeness
