import MeraConstraints.CompactDistrict
import MeraConstraints.Reconstruction

/-!
# The district factor on rows `(v₁, v₂)`

The district factor `Pdo(V₁ = v₁ ∣ V₂ = v₂)` of Proposition 1 (`prop:ident`) is the
product over the members of conditional probabilities given the conditioning sets
`C_i`. `Reconstruction.districtFactor` evaluates it at a complete assignment. This
chapter shows that its value depends on the assignment only through the members and
external parents (`districtFactor_congr_project`), so it defines a vector indexed by
the rows `(v₁, v₂)` of the matrix `B` (`districtFactor`). To evaluate it at a row,
the row is extended to a complete assignment arbitrarily; the result does not
depend on the extension (`districtFactor_project`).

An H-representation of `B` therefore describes this vector: it lies in the district
polytope of `GlobalModel.matrix` if and only if it satisfies the H-representation
(`districtFactor_mem_mixture_iff_HRep`).
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D) (d : D)

/-- Every variable in the conditioning set `C_i` of a member is a member or an
external parent of the district. -/
theorem conditioningVariables_relevant (i : Member block d) (j : Fin n)
    (hj : j ∈ Reconstruction.conditioningVariables G block i) :
    block j = d ∨ IsExternalParent G block d j := by
  rcases (Finset.mem_filter.mp hj).2 with h | ⟨k, _, hkd, hjk, hne⟩
  · exact Or.inl (h.2.trans i.2)
  · exact Or.inr ⟨by simpa [i.2] using hne, ⟨k, hkd.trans i.2, hjk⟩⟩

omit [DecidableEq D] in
/-- Complete assignments with the same row agree at every member and external
parent. -/
theorem value_eq_of_project_eq (w v : FullAssign val)
    (heq : project G val block d w = project G val block d v)
    (j : Fin n) (hj : block j = d ∨ IsExternalParent G block d j) : w j = v j := by
  rcases hj with hm | he
  · exact congrFun (congrArg Prod.fst heq) ⟨j, hm⟩
  · exact congrFun (congrArg Prod.snd heq) ⟨j, he⟩

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The district factor at a complete assignment depends only on its row. This holds
for every vector `p`. -/
theorem districtFactor_congr_project (p : FullAssign val → ℝ) (w v : FullAssign val)
    (heq : project G val block d w = project G val block d v) :
    Reconstruction.districtFactor G val block p d w =
      Reconstruction.districtFactor G val block p d v := by
  unfold Reconstruction.districtFactor
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

/-- The district factor `Pdo(V₁ = v₁ ∣ V₂ = v₂)` as a vector indexed by rows. -/
noncomputable def districtFactor (p : FullAssign val → ℝ) : Row G val block d → ℝ :=
  fun x => Reconstruction.districtFactor G val block p d (extend G val block d x)

theorem districtFactor_project (p : FullAssign val → ℝ) (w : FullAssign val) :
    districtFactor G val block d p (project G val block d w) =
      Reconstruction.districtFactor G val block p d w := by
  apply districtFactor_congr_project G val block d p
  exact project_extend G val block d (project G val block d w)

/-- The district factor lies in the district polytope of `B` if and only if it lies
in the district polytope of `GlobalModel.matrix`. -/
theorem districtFactor_mem_mixture_iff (p : FullAssign val → ℝ) :
    Reconstruction.districtFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d) ↔
    districtFactor G val block d p ∈ Polytope.mixture (matrix G val block d) := by
  have hf : (fun w => districtFactor G val block d p (project G val block d w)) =
      Reconstruction.districtFactor G val block p d :=
    funext (districtFactor_project G val block d p)
  rw [← hf, pullback_mem_mixture_iff]

/-- An H-representation of `B` decides whether the district factor lies in the
district polytope of `GlobalModel.matrix`. -/
theorem districtFactor_mem_mixture_iff_HRep {I E : Type*}
    (H : Polytope.HRep (matrix G val block d) I E) (p : FullAssign val → ℝ) :
    Reconstruction.districtFactor G val block p d ∈
      Polytope.mixture (GlobalModel.matrix G val block d) ↔
      (∀ i, ∑ x, H.inequalities i x * districtFactor G val block d p x ≤ H.upper i) ∧
      (∀ e, ∑ x, H.equalities e x * districtFactor G val block d p x = H.target e) := by
  rw [districtFactor_mem_mixture_iff]
  exact H.exact_representation _

end MeraConstraints.CompactDistrict
