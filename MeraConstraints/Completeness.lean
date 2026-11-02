import MeraConstraints.Reconstruction
import MeraConstraints.Identification
import MeraConstraints.HiddenGraph.Realization
import MeraConstraints.HiddenGraph.SCMRealization

/-!
# Finite-source constraints and original-graph realization

The appendix proves Proposition `prop:complete` in two directions. This
chapter assembles its **sufficiency** construction: choose feasible district
profile laws, take independent original graph inputs, and reproduce a given
strictly positive observed law.

There are three distinct ingredients, all visible in the theorem statements:

1. `OrderedMarkov` supplies the supported conditional-independence equations
   used to reduce the chain-rule factors to the cumulative sets `C_i`.
2. A checked `HRep` supplies district profile distributions realizing those
   observable factors. Exact V/H equivalence is data with a proof.
3. The c-degree bound supplies a bijection between districts and independent
   original sources (one shared root, or a private source for a singleton).

The construction therefore uses actual roots and private
disturbances of the graph, rather than only an abstract correlated response
vector. It is not yet the full equality `M(G)=C(G)`: deriving the Markov
equations and observable district identification for every original model,
and transporting original SCM input laws to finite profile laws,
remain separate necessities for that claim. The final `finite_source_iff_HRep`
does prove both directions for the **canonical** independent finite-source
model defined by `sourceObserved`. In that model the ordered Markov equations
are derived. Canonicalization of general original SCM probability laws,
including general finite laws, has not yet been proved.
-/

namespace MeraConstraints.Completeness

open HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
variable [DecidableEq (DistrictId G)]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The constructive inclusion in Proposition `prop:complete`, with the
precise ordered Markov assumption exposed. The generated law uses independent
original graph sources, not an unrestricted profile for a higher-degree district. -/
theorem realize_of_orderedMarkov_and_factor_feasible
    (hdegree : ∀ x, cDegree G x ≤ 1) (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p)
    (hfeasible : ∀ d, Reconstruction.observableFactor G.observed val
      (observedDistrict G) p d ∈
        Polytope.mixture (GlobalModel.matrix G.observed val (observedDistrict G) d)) :
    ∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
      sourceObserved G val q = p := by
  classical
  obtain ⟨q, hq, hobs⟩ := Reconstruction.realize_of_factor_feasible
    G.observed val (observedDistrict G) p hp hpos hMarkov hfeasible
  exact ⟨q, hq, (sourceObserved_eq_observed G val hdegree q).trans hobs⟩

/-- Checked district H-constraints give a graph-compatible realization.
The H-matrices here retain redundant full-assignment row indexing, matching
`GlobalModel.matrix`; removing repeated rows is a separate presentation step. -/
theorem realize_of_orderedMarkov_and_HRep
    (hdegree : ∀ x, cDegree G x ≤ 1)
    {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (GlobalModel.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ w, 0 < p w)
    (hMarkov : Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p)
    (hH : ∀ d,
      (∀ i, ∑ w, (H d).inequalities i w *
        Reconstruction.observableFactor G.observed val (observedDistrict G) p d w ≤
          (H d).upper i) ∧
      (∀ e, ∑ w, (H d).equalities e w *
        Reconstruction.observableFactor G.observed val (observedDistrict G) p d w =
          (H d).target e)) :
    ∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
      sourceObserved G val q = p := by
  classical
  apply realize_of_orderedMarkov_and_factor_feasible G val hdegree p hp hpos hMarkov
  intro d
  exact ((H d).exact_representation _).mpr (hH d)

/-- The realization is the evaluation law of an explicit parent-restricted
SCM. Nonempty observed value types allow constants at unused private inputs;
all randomness used by the construction comes from mutually independent sources. -/
theorem realize_with_explicit_SCM [∀ i, Nonempty (val i)]
    (hdegree : ∀ x, cDegree G x ≤ 1) (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p)
    (hfeasible : ∀ d, Reconstruction.observableFactor G.observed val
      (observedDistrict G) p d ∈
        Polytope.mixture (GlobalModel.matrix G.observed val (observedDistrict G) d)) :
    ∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
      pushforward
        (fun r => (profileSCM G val).eval
          (sourceLatentInput G val r) (sourcePrivateInput G val r))
        (Independent.joint (fun s => q (sourceDistrict G s))) = p := by
  classical
  obtain ⟨q, hq, hobs⟩ := realize_of_orderedMarkov_and_factor_feasible
    G val hdegree p hp hpos hMarkov hfeasible
  exact ⟨q, hq, (sourceObserved_eq_profileSCM G val q).symm.trans hobs⟩

/-- Positive canonical finite-source equivalence for an actual c-degree-one graph.
The ordered Markov equations on the right are proved necessary, not assumed
for generated models. This does not quantify over every original SCM and its
latent law, or accept an unchecked H-matrix produced by the R code. -/
theorem finite_source_iff_HRep
    (hdegree : ∀ x, cDegree G x ≤ 1)
    {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep
      (GlobalModel.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ w, 0 < p w) :
    (∃ q : ∀ d, DistrictProfile G val d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (DistrictProfile G val d)) ∧
        sourceObserved G val q = p) ↔
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p ∧
      ∀ d,
        (∀ i, ∑ w, (H d).inequalities i w *
          Reconstruction.observableFactor G.observed val (observedDistrict G) p d w ≤
            (H d).upper i) ∧
        (∀ e, ∑ w, (H d).equalities e w *
          Reconstruction.observableFactor G.observed val (observedDistrict G) p d w =
            (H d).target e) := by
  constructor
  · rintro ⟨q, hq, hobs⟩
    apply (Identification.finite_profile_iff_HRep G.observed val (observedDistrict G) H p hp hpos).mp
    exact ⟨q, hq, (sourceObserved_eq_observed G val hdegree q).symm.trans hobs⟩
  · intro hc
    obtain ⟨q, hq, hobs⟩ :=
      (Identification.finite_profile_iff_HRep G.observed val (observedDistrict G) H p hp hpos).mpr hc
    exact ⟨q, hq, (sourceObserved_eq_observed G val hdegree q).trans hobs⟩

end MeraConstraints.Completeness
