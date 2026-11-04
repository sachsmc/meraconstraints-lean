import MeraConstraints.GlobalModel.GlobalToLocal
import MeraConstraints.Completeness.Graphical
import MeraConstraints.Completeness.ProbabilityModel

/-!
# Original marginal-model completeness with graphical independencies

This is Proposition `prop:complete` with the graph-defined global Markov
predicate on its right, rather than an additional assumed family of ordered
conditional equations. Original-model graphical necessity was proved by
canonicalization. Graphical separation now implies the precise cumulative
ordered equations used by the existing constructive completeness proof.

The same connection proves the boundary version of `rmk:positivity` using
the exact first-zero/first-undefined compact H-completions. Original latent
inputs may be arbitrary measurable spaces. H-representation exactness is
still a checked input; an external numerical conversion is not trusted.

Graphical separation is specified by the original DAG's ancestral moral
graph, including its latent roots. No active-trail equivalence or arbitrary
local-to-global equivalence is assumed in these proofs.
-/

namespace MeraConstraints.Completeness

open HiddenGraph GlobalModel.KernelReconstruction

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)] [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

/-- The exact positive-law graphical characterization of the original
marginal model, using the paper's compact district H-systems. -/
theorem original_model_iff_global_compact_HRep
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔ MoralGlobalMarkov G val p ∧
      ∀ d, (∀ i, ∑ x, (H d).inequalities i x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d p x ≤ (H d).upper i) ∧
        (∀ e, ∑ x, (H d).equalities e x *
          CompactDistrict.observableFactor G.observed val (observedDistrict G) d p x = (H d).target e) := by
  constructor
  · rintro ⟨P, hP⟩
    have hg : MoralGlobalMarkov G val p := hP ▸ probabilityModel_moralGlobalMarkov G val hdegree P
    have hc := (original_model_iff_compact_HRep G val hdegree H p hp hpos).mp ⟨P, hP⟩
    exact ⟨hg, hc.2⟩
  · rintro ⟨hg, hH⟩
    exact (original_model_iff_compact_HRep G val hdegree H p hp hpos).mpr
      ⟨moralGlobalMarkov_orderedMarkov G val p hg, hH⟩

/-- Remark `rmk:positivity` with graphical independencies and the exact
compact known/free-row completion rule, including zero observed probabilities. -/
theorem original_model_iff_global_boundary_compact_HCompletion
    (hdegree : ∀ x, cDegree G x ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep (CompactDistrict.matrix G.observed val (observedDistrict G) d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔
      MoralGlobalMarkov G val p ∧ Boundary.CompactHCompletion G val H p := by
  constructor
  · rintro ⟨P, hP⟩
    have hg : MoralGlobalMarkov G val p := hP ▸ probabilityModel_moralGlobalMarkov G val hdegree P
    have hc := (Boundary.original_model_iff_boundary_compact_HCompletion G val hdegree H p hp).mp ⟨P, hP⟩
    exact ⟨hg, hc.2⟩
  · rintro ⟨hg, hH⟩
    exact (Boundary.original_model_iff_boundary_compact_HCompletion G val hdegree H p hp).mpr
      ⟨moralGlobalMarkov_orderedMarkov G val p hg, hH⟩

end MeraConstraints.Completeness
