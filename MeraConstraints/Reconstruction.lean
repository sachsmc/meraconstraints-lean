import MeraConstraints.GlobalModel
import MeraConstraints.Probability.Conditional

/-!
# Observable factors and constructive reconstruction

This chapter formalizes the sufficiency argument in the proof of Proposition
`prop:complete`, with the ordered conditional-independence hypothesis stated
explicitly. `conditioningVariables i` is exactly the revised manuscript's
`C_i`: all earlier members of the same district, together with the external
observed parents of **every** member up to and including `i`.

The full graph's global Markov property has not been proved here. Instead
`OrderedMarkov` records the precise event-level conditional independence used
to replace `pre(V_i)` by `C_i`. Given this hypothesis, a positive observed law
is the product of its observable district factors. If those factors satisfy
checked H-representations, the finite independent-profile construction
reproduces the observed law exactly. No identification theorem is hidden in
the definition of the factors or the model.
-/

namespace MeraConstraints.Reconstruction

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D)

/-- The cumulative external-parent conditioning set in Proposition `prop:ident`.
The parent condition ranges over every earlier member, not just `i`. -/
def conditioningVariables (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j =>
    (j < i ∧ block j = block i) ∨
      ∃ k : Fin n, k ≤ i ∧ block k = block i ∧
        j ∈ G.parents k ∧ block j ≠ block i

theorem conditioningVariables_lt (i j : Fin n)
    (hj : j ∈ conditioningVariables G block i) : j < i := by
  rcases (Finset.mem_filter.mp hj).2 with h | ⟨k, hki, _, hjk, _⟩
  · exact h.1
  · exact lt_of_lt_of_le (G.parents_lt hjk) hki

theorem parents_subset_conditioningVariables (i : Fin n) :
    G.parents i ⊆ conditioningVariables G block i := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases h : block j = block i
  · exact Or.inl ⟨G.parents_lt hj, h⟩
  · exact Or.inr ⟨i, le_rfl, rfl, hj, h⟩

theorem conditioningVariables_mono (i k : Fin n) (hik : i ≤ k)
    (hb : block i = block k) :
    conditioningVariables G block i ⊆ conditioningVariables G block k := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases (Finset.mem_filter.mp hj).2 with h | ⟨l, hli, hblock, hparent, hne⟩
  · exact Or.inl ⟨lt_of_lt_of_le h.1 hik, h.2.trans hb⟩
  · exact Or.inr ⟨l, hli.trans hik, hblock.trans hb, hparent, by simpa [← hb] using hne⟩

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The assignment event for the variables in `C_i`. Smaller variable sets
give larger events, hence the direction of `prefixEvent_subset_conditioningEvent`. -/
def conditioningEvent (w : FullAssign val) (i : Fin n) : Finset (FullAssign val) :=
  Finset.univ.filter fun z => ∀ j ∈ conditioningVariables G block i, z j = w j

theorem self_mem_conditioningEvent (w : FullAssign val) (i : Fin n) :
    w ∈ conditioningEvent G val block w i := by
  simp [conditioningEvent]

theorem prefixEvent_subset_conditioningEvent (w : FullAssign val) (i : Fin n) :
    prefixEvent val w i.val ⊆ conditioningEvent G val block w i := by
  intro z hz
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro j hj
  exact (Finset.mem_filter.mp hz).2 j (conditioningVariables_lt G block i j hj)

/-- The specific ordered local Markov equations required for reconstruction.
They are assumptions here, not yet consequences of a separation theorem. -/
def OrderedMarkov (p : FullAssign val → ℝ) : Prop :=
  ∀ w i, CondIndependent p (valueEvent val w i) (prefixEvent val w i.val)
    (conditioningEvent G val block w i)

/-- The observable district product in Proposition `prop:ident`. -/
noncomputable def observableFactor (p : FullAssign val → ℝ) (d : D)
    (w : FullAssign val) : ℝ :=
  ∏ i : {i : Fin n // block i = d},
    conditional p (valueEvent val w i) (conditioningEvent G val block w i)

variable [Fintype D]

/-- Chain rule, conditioning-set replacement, and regrouping by district.
This is the last step of the appendix's reconstruction argument. -/
theorem observed_eq_prod_observableFactor (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : OrderedMarkov G val block p) (w : FullAssign val) :
    p w = ∏ d, observableFactor G val block p d w := by
  change p w = ∏ d, ∏ i : {i : Fin n // block i = d},
    conditional p (valueEvent val w i) (conditioningEvent G val block w i)
  rw [Fintype.prod_fiberwise block (fun i : Fin n =>
    conditional p (valueEvent val w i) (conditioningEvent G val block w i))]
  apply assignment_eq_prod_replaced val p hp hpos w
  · intro i
    exact prefixEvent_subset_conditioningEvent G val block w i
  · intro i
    exact (mass_pos_of_mem hpos (self_mem_conditioningEvent G val block w i)).ne'
  · exact hMarkov w

/-- Construct response laws from feasible district factors and reproduce `p`.
This proves sufficiency in the finite profile model under `OrderedMarkov`.
Connecting that model to the original common-cause graph is a separate bridge. -/
theorem realize_of_factor_feasible (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : OrderedMarkov G val block p)
    (hfeasible : ∀ d, observableFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d)) :
    ∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
      GlobalModel.observed G val block q = p := by
  classical
  choose q hq hmatrix using hfeasible
  refine ⟨q, hq, ?_⟩
  funext w
  rw [GlobalModel.observed_eq_prod_factor,
    observed_eq_prod_observableFactor G val block p hp hpos hMarkov]
  apply Finset.prod_congr rfl
  intro d _
  rw [GlobalModel.factor_eq_mulVec]
  exact congrFun (hmatrix d) w

/-- A checked H-representation can replace simplex feasibility in the previous
theorem. This uses its proof of exactness, not a numerical conversion oracle. -/
theorem realize_of_HRep {I E : D → Type*}
    (H : ∀ d, Polytope.HRep (GlobalModel.matrix G val block d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ w, 0 < p w) (hMarkov : OrderedMarkov G val block p)
    (hH : ∀ d,
      (∀ i, ∑ w, (H d).inequalities i w * observableFactor G val block p d w ≤
        (H d).upper i) ∧
      (∀ e, ∑ w, (H d).equalities e w * observableFactor G val block p d w =
        (H d).target e)) :
    ∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
      GlobalModel.observed G val block q = p := by
  apply realize_of_factor_feasible G val block p hp hpos hMarkov
  intro d
  exact ((H d).exact_representation _).mpr (hH d)

end MeraConstraints.Reconstruction
