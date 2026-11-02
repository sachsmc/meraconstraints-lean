import MeraConstraints.CompactDistrict
import MeraConstraints.Reconstruction

/-!
# Observable factors on compact district rows

The row projection in `CompactDistrict.lean` removes only irrelevant
observed coordinates. This chapter proves that the manuscript's actual
observable product, with its cumulative conditioning sets `C_i`, is constant
on every projection fiber. Thus it defines a function of precisely `(v₁,v₂)`.

An auxiliary extension supplies a full assignment when evaluating that
product, but the result is independent of the values chosen outside the
district and its external parents. The final theorem transfers a checked
H-representation on compact manuscript rows directly to feasibility of the
full-row observable factor used in `Reconstruction`. This is a change of
row presentation, not an additional identification assumption.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D) (d : D)

/-- Every variable occurring in a member's cumulative conditioning set is
either a member or an external parent of this district. -/
theorem conditioningVariables_relevant (i : Member block d) (j : Fin n)
    (hj : j ∈ Reconstruction.conditioningVariables G block i) :
    block j = d ∨ IsExternalParent G block d j := by
  rcases (Finset.mem_filter.mp hj).2 with h | ⟨k, _, hkd, hjk, hne⟩
  · exact Or.inl (h.2.trans i.2)
  · exact Or.inr ⟨by simpa [i.2] using hne, ⟨k, hkd.trans i.2, hjk⟩⟩

omit [DecidableEq D] in
/-- Equal compact projections give equal values at every relevant coordinate. -/
theorem value_eq_of_project_eq (w v : FullAssign val)
    (heq : project G val block d w = project G val block d v)
    (j : Fin n) (hj : block j = d ∨ IsExternalParent G block d j) : w j = v j := by
  rcases hj with hm | he
  · exact congrFun (congrArg Prod.fst heq) ⟨j, hm⟩
  · exact congrFun (congrArg Prod.snd heq) ⟨j, he⟩

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The observed product depends only on district and external-parent values.
No positivity, graphical Markov, or compatibility assumption is needed for
this coordinate-dependence identity. -/
theorem observableFactor_congr_project (p : FullAssign val → ℝ) (w v : FullAssign val)
    (heq : project G val block d w = project G val block d v) :
    Reconstruction.observableFactor G val block p d w =
      Reconstruction.observableFactor G val block p d v := by
  unfold Reconstruction.observableFactor
  apply Finset.prod_congr rfl
  intro i _
  have hv : FiniteProbability.valueEvent val w i = FiniteProbability.valueEvent val v i := by
    ext z
    simp only [FiniteProbability.valueEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [value_eq_of_project_eq G val block d w v heq i (Or.inl i.2)]
  have hC : Reconstruction.conditioningEvent G val block w i =
      Reconstruction.conditioningEvent G val block v i := by
    ext z
    simp only [Reconstruction.conditioningEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz j hj
      rw [← value_eq_of_project_eq G val block d w v heq j
        (conditioningVariables_relevant G block d i j hj)]
      exact hz j hj
    · intro hz j hj
      rw [value_eq_of_project_eq G val block d w v heq j
        (conditioningVariables_relevant G block d i j hj)]
      exact hz j hj
  rw [hv, hC]

variable [∀ i, Nonempty (val i)]

/-- The manuscript's observable vector, indexed by compact pairs `(v₁,v₂)`.
The theorem below proves independence from auxiliary extension values. -/
noncomputable def observableFactor (p : FullAssign val → ℝ) : Row G val block d → ℝ :=
  fun x => Reconstruction.observableFactor G val block p d (extend G val block d x)

theorem observableFactor_project (p : FullAssign val → ℝ) (w : FullAssign val) :
    observableFactor G val block d p (project G val block d w) =
      Reconstruction.observableFactor G val block p d w := by
  apply observableFactor_congr_project G val block d p
  exact project_extend G val block d (project G val block d w)

/-- Compact district feasibility is exactly the full-row feasibility condition
in the constructive completeness theorem. -/
theorem observableFactor_mem_mixture_iff (p : FullAssign val → ℝ) :
    Reconstruction.observableFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d) ↔
    observableFactor G val block d p ∈ Polytope.mixture (matrix G val block d) := by
  have hf : (fun w => observableFactor G val block d p (project G val block d w)) =
      Reconstruction.observableFactor G val block p d :=
    funext (observableFactor_project G val block d p)
  rw [← hf, pullback_mem_mixture_iff]

/-- A checked compact H-system characterizes the existing full-row observable
feasibility condition, using precisely the manuscript's `(v₁,v₂)` rows. -/
theorem observableFactor_mem_mixture_iff_HRep {I E : Type*}
    (H : Polytope.HRep (matrix G val block d) I E) (p : FullAssign val → ℝ) :
    Reconstruction.observableFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d) ↔
      (∀ i, ∑ x, H.inequalities i x * observableFactor G val block d p x ≤ H.upper i) ∧
      (∀ e, ∑ x, H.equalities e x * observableFactor G val block d p x = H.target e) := by
  rw [observableFactor_mem_mixture_iff]
  exact H.exact_representation _

end MeraConstraints.CompactDistrict
