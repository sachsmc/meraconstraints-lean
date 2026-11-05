import MeraConstraints.GlobalModel
import MeraConstraints.Probability.Conditional

/-!
# District factors and reconstruction

This chapter formalizes the sufficiency direction in the proof of Proposition 3
(`prop:complete`) for the model of independent block profiles; the blocks are later taken to be the
districts. `conditioningVariables i` is the set `C_i` of Proposition 1 (`prop:ident`):
the earlier members of the district of `V_i`, together with the external observed
parents of every member up to and including `V_i`. `districtFactor` is the district
factor `Pdo`, the product over a district of the conditionals of its members given
`C_i`.

`OrderedMarkov` is the ordered local Markov property: each `V_i` is independent of its
predecessors given `C_i`. If a strictly positive `p` satisfies it, `p` is the product of
its district factors (`observed_eq_prod_districtFactor`). If each district factor also
lies in the district polytope, or satisfies an H-representation, then independent block
profiles generate `p` (`realize_of_factor_feasible`, `realize_of_HRep`).

That the conditional independencies implied by the graph (`GlobalMarkov`) give
`OrderedMarkov` is proved in `GlobalModel.GlobalToLocal`. The step from block profiles to
the hidden variables DAG is in `Completeness.Global`.
-/

namespace MeraConstraints.Reconstruction

open FiniteProbability

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D)

/-- The set `C_i` of Proposition 1 (`prop:ident`): the earlier members of the block of
`V_i`, and the external parents of every member of the block up to and including `V_i`. -/
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

/-- The event that the variables in `C_i` take their values in `w`. Since `C_i` consists
of earlier variables, this event contains the prefix event
(`prefixEvent_subset_conditioningEvent`). -/
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

/-- The ordered local Markov property: for every `V_i` and every `w`, `V_i` is
independent of the earlier variables given `C_i`, written as an equation between
masses of events. It follows from `GlobalMarkov` (`globalMarkov_orderedMarkov`), and
holds for generated distributions (`GlobalModel.observed_orderedMarkov`). -/
def OrderedMarkov (p : FullAssign val → ℝ) : Prop :=
  ∀ w i, CondIndependent p (valueEvent val w i) (prefixEvent val w i.val)
    (conditioningEvent G val block w i)

/-- The district factor `Pdo` of Proposition 1 (`prop:ident`): the product over the
members `V_i` of district `d` of `Pr(V_i = w_i ∣ C_i = w)`. -/
noncomputable def districtFactor (p : FullAssign val → ℝ) (d : D)
    (w : FullAssign val) : ℝ :=
  ∏ i : {i : Fin n // block i = d},
    conditional p (valueEvent val w i) (conditioningEvent G val block w i)

variable [Fintype D]

/-- A strictly positive distribution with the ordered local Markov property is the
product of its district factors. This is the last step of the proof of Proposition 3
(`prop:complete`): chain rule, replacement of the predecessors by `C_i`, and grouping
by district. -/
theorem observed_eq_prod_districtFactor (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : OrderedMarkov G val block p) (w : FullAssign val) :
    p w = ∏ d, districtFactor G val block p d w := by
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

/-- Let `p` be strictly positive with `OrderedMarkov`, and suppose each district factor
lies in the district polytope. Then independent block profiles with some distributions
`q` generate `p`. This is sufficiency in the model of block profiles; the link to the
hidden variables DAG is in `Completeness.Global`. -/
theorem realize_of_factor_feasible (p : FullAssign val → ℝ)
    (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w)
    (hMarkov : OrderedMarkov G val block p)
    (hfeasible : ∀ d, districtFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d)) :
    ∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
      GlobalModel.observed G val block q = p := by
  classical
  choose q hq hmatrix using hfeasible
  refine ⟨q, hq, ?_⟩
  funext w
  rw [GlobalModel.observed_eq_prod_factor,
    observed_eq_prod_districtFactor G val block p hp hpos hMarkov]
  apply Finset.prod_congr rfl
  intro d _
  rw [GlobalModel.factor_eq_mulVec]
  exact congrFun (hmatrix d) w

/-- The same, with the H-representation constraints on each district factor in place
of membership in the district polytope. -/
theorem realize_of_HRep {I E : D → Type*}
    (H : ∀ d, Polytope.HRep (GlobalModel.matrix G val block d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val))
    (hpos : ∀ w, 0 < p w) (hMarkov : OrderedMarkov G val block p)
    (hH : ∀ d,
      (∀ i, ∑ w, (H d).inequalities i w * districtFactor G val block p d w ≤
        (H d).upper i) ∧
      (∀ e, ∑ w, (H d).equalities e w * districtFactor G val block p d w =
        (H d).target e)) :
    ∃ q : ∀ d, GlobalModel.Profile G val block d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (GlobalModel.Profile G val block d)) ∧
      GlobalModel.observed G val block q = p := by
  apply realize_of_factor_feasible G val block p hp hpos hMarkov
  intro d
  exact ((H d).exact_representation _).mpr (hH d)

end MeraConstraints.Reconstruction
