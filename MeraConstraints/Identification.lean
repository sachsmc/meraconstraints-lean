import MeraConstraints.Reconstruction
import MeraConstraints.GlobalModel.Prefix
import MeraConstraints.GlobalModel.OrderedMarkov

/-!
# Identifying observable district products in the finite profile model

The prefix chapter proves, directly from independent profile laws and
structural recursion, that the product of global-predecessor conditionals
over a block equals its structural factor. It does not assume a district
factorization of the observed law in order to derive this identity.

First the explicit `OrderedMarkov` equations replace global predecessor
sets by the manuscript's cumulative `C_i`. The resulting observable product
is the same structural factor, and hence satisfies the block V-representation.
Conversely, reconstruction realizes any positive law satisfying the same
ordered Markov equations and the feasible block constraints.

The final theorems use `GlobalModel.observed_orderedMarkov`, which derives
those equations directly for generated finite-profile laws. They characterize
the canonical finite model by ordered equations and feasible district factors.
They do not yet reduce every original SCM with an arbitrary latent law (even
a finite one) to this canonical model, or prove all graphical separation
results. The H-matrix
rows also retain full-assignment indexing; transporting the paper's compact
matrix indexing remains separate.
-/

namespace MeraConstraints.Identification

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [Fintype D] [DecidableEq D] (block : Fin n → D)
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Identification of the cumulative-conditioning product, with the precise
ordered Markov equations exposed as a hypothesis. -/
theorem structuralFactor_eq_observableFactor
    (q : ∀ d, GlobalModel.Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d))
    (hpos : ∀ w, 0 < GlobalModel.observed G val block q w)
    (hMarkov : Reconstruction.OrderedMarkov G val block (GlobalModel.observed G val block q))
    (d : D) (w : FullAssign val) :
    GlobalModel.factor G val block q d w =
      Reconstruction.observableFactor G val block (GlobalModel.observed G val block q) d w := by
  classical
  rw [GlobalModel.factor_eq_prod_prefixConditional G val block q hq hpos d w]
  let f := fun i : Fin n => conditional (GlobalModel.observed G val block q)
    (valueEvent val w i) (Reconstruction.conditioningEvent G val block w i)
  calc
    _ = ∏ i ∈ Finset.univ.filter (fun i => block i = d), f i := by
      apply Finset.prod_congr rfl
      intro i _
      exact conditional_eq_of_subset_independent _ _ _ _
        (Reconstruction.prefixEvent_subset_conditioningEvent G val block w i)
        (hMarkov w i) (prefix_mass_pos val _ hpos w i.val).ne'
        (mass_pos_of_mem hpos (Reconstruction.self_mem_conditioningEvent G val block w i)).ne'
    _ = _ := Finset.prod_subtype _ (by intro i; simp) f

/-- Necessary and sufficient V-constraints for the finite profile model among
positive laws with the explicit ordered Markov equations. -/
theorem finite_profile_iff_factor_feasible (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : Reconstruction.OrderedMarkov G val block p) :
    (∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
        GlobalModel.observed G val block q = p) ↔
    ∀ d, Reconstruction.observableFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d) := by
  constructor
  · rintro ⟨q, hq, hobs⟩ d
    have hposq : ∀ w, 0 < GlobalModel.observed G val block q w := by simpa [hobs] using hpos
    have hMarkovq : Reconstruction.OrderedMarkov G val block (GlobalModel.observed G val block q) := by
      simpa [hobs] using hMarkov
    have hfactor : GlobalModel.factor G val block q d =
        Reconstruction.observableFactor G val block p d := by
      funext w
      simpa [hobs] using structuralFactor_eq_observableFactor G val block q hq hposq hMarkovq d w
    rw [← hfactor]
    exact GlobalModel.factor_mem_mixture G val block q hq d
  · exact Reconstruction.realize_of_factor_feasible G val block p hp hpos hMarkov

/-- For generated finite-profile laws the ordered equations are now derived,
so cumulative-product identification has no additional Markov hypothesis. -/
theorem generated_factor_eq_observableFactor
    (q : ∀ d, GlobalModel.Profile G val block d → ℝ)
    (hq : ∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d))
    (hpos : ∀ w, 0 < GlobalModel.observed G val block q w) (d : D) (w : FullAssign val) :
    GlobalModel.factor G val block q d w =
      Reconstruction.observableFactor G val block (GlobalModel.observed G val block q) d w :=
  structuralFactor_eq_observableFactor G val block q hq hpos
    (GlobalModel.observed_orderedMarkov G val block q hpos) d w

/-- Exact positive-law characterization of the finite independent-profile model.
The forward direction proves the ordered equations from the mechanisms;
the reverse direction constructs profile laws from the feasible factors. -/
theorem finite_profile_iff_constraints (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w) :
    (∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
        GlobalModel.observed G val block q = p) ↔
    Reconstruction.OrderedMarkov G val block p ∧
      ∀ d, Reconstruction.observableFactor G val block p d ∈
        Polytope.mixture (GlobalModel.matrix G val block d) := by
  constructor
  · intro hmodel
    obtain ⟨q, hq, hobs⟩ := hmodel
    have hMarkov : Reconstruction.OrderedMarkov G val block p := by
      have hposq : ∀ w, 0 < GlobalModel.observed G val block q w := by simpa [hobs] using hpos
      simpa [hobs] using GlobalModel.observed_orderedMarkov G val block q hposq
    exact ⟨hMarkov, (finite_profile_iff_factor_feasible G val block p hp hpos hMarkov).mp
      ⟨q, hq, hobs⟩⟩
  · rintro ⟨hMarkov, hfeasible⟩
    exact (finite_profile_iff_factor_feasible G val block p hp hpos hMarkov).mpr hfeasible

/-- Checked H-constraints and the ordered equations characterize the same
finite model. No V-to-H conversion algorithm is trusted by this theorem. -/
theorem finite_profile_iff_HRep {I E : D → Type*}
    (H : ∀ d, Polytope.HRep (GlobalModel.matrix G val block d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ w, 0 < p w) :
    (∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
        GlobalModel.observed G val block q = p) ↔
    Reconstruction.OrderedMarkov G val block p ∧
      ∀ d,
        (∀ i, ∑ w, (H d).inequalities i w * Reconstruction.observableFactor G val block p d w ≤
          (H d).upper i) ∧
        (∀ e, ∑ w, (H d).equalities e w * Reconstruction.observableFactor G val block p d w =
          (H d).target e) := by
  rw [finite_profile_iff_constraints G val block p hp hpos]
  apply and_congr_right
  intro _
  constructor
  · intro hf d
    exact ((H d).exact_representation _).mp (hf d)
  · intro hf d
    exact ((H d).exact_representation _).mpr (hf d)

end MeraConstraints.Identification
