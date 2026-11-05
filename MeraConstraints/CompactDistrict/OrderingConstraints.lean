import MeraConstraints.CompactDistrict
import MeraConstraints.HiddenGraph.Ancestry
import MeraConstraints.EqualityConstraints
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Equations (N) and (O)

These are the linear equations (N) and (O) before Proposition 4 (`prop:nontrivial`),
written as coefficient matrices on the rows `(v₁, v₂)` of the matrix `B`. Equations
(N) say that `p(· ∣ v₂)` sums to one for every `v₂`. Equations (O) say that for every
nonempty closed set `S` of members, the margin of `p` over the members outside `S`
takes the same value at any two values of `v₂` that agree on the external parents
of `S`. "Closed" is `HiddenGraph.FullClosed`: `S` contains every member of the
district that is an ancestor of a member of `S`, where the ancestor may be reached
through variables outside the district. The weaker condition
`HiddenGraph.ClosedInDistrict` would also include the Verma equalities.

Every column of `B` satisfies (N) and (O) (`normalization_column`, `ordering_column`),
so every point of the district polytope does (`constraints_of_mixture`). The
uniform distribution of the members, repeated for every `v₂`, is a strictly positive
solution (`uniformKernel_feasible`). That equations (N) and (O) hold for every
strictly positive distribution satisfying the conditional independencies is shown in
`GlobalModel.ObservableConstraints`.
-/

namespace MeraConstraints.CompactDistrict.OrderingConstraints

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)] (d : HiddenGraph.DistrictId G)

local notation "Out" => MemberAssign val (HiddenGraph.observedDistrict G) d
local notation "Ext" => ExternalAssign G.observed val (HiddenGraph.observedDistrict G) d
local notation "Rows" => Row G.observed val (HiddenGraph.observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (HiddenGraph.observedDistrict G) d

/-- The nonempty closed sets of members used in equations (O). -/
abbrev ClosedSubset :=
  {S : Finset (Fin n) // S.Nonempty ∧ HiddenGraph.FullClosed G d S}

noncomputable instance : Fintype (ClosedSubset G d) := Fintype.ofFinite _

abbrev SubsetAssign (S : Finset (Fin n)) := ∀ i : {i : Fin n // i ∈ S}, val i

/-- Restrict an assignment of the members to the closed set `S`. -/
def restrictOutput (S : ClosedSubset G d) (out : Out) : SubsetAssign val S.val :=
  fun i => out ⟨i, S.2.2.1 i i.2⟩

/-- Two values of `v₂` agree on the external parents `E(S)` of `S`. -/
def ExternalAgreement (S : ClosedSubset G d) (e e' : Ext) : Prop :=
  ∀ j : ExternalParent G.observed (HiddenGraph.observedDistrict G) d,
    (∃ i : Fin n, i ∈ S.val ∧ j.val ∈ G.observed.parents i) → e j = e' j

/-- For a closed set `S`, the values that a profile gives the members of `S`
depend on `v₂` only through its value on `E(S)`. -/
theorem eval_eq_on_fullClosed (S : ClosedSubset G d) (r : Profiles) (e e' : Ext)
    (he : ExternalAgreement G val d S e e')
    (i : Member (HiddenGraph.observedDistrict G) d) (hi : i.val ∈ S.val) :
    CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d r e i =
      CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d r e' i := by
  rw [CompactDistrict.eval, CompactDistrict.eval]
  congr 1
  funext j
  by_cases hj : HiddenGraph.observedDistrict G j = d
  · simp only [dif_pos hj]
    exact eval_eq_on_fullClosed S r e e' he ⟨j, hj⟩
      (S.2.2.2 i hi j (HiddenGraph.observedAncestor_of_parent G j.2) hj)
  · simp only [dif_neg hj]
    exact he ⟨j, hj, ⟨i, i.2, j.2⟩⟩ ⟨i, hi, j.2⟩
termination_by i.val.val
decreasing_by exact G.observed.parents_lt j.2

theorem restrict_eval_eq (S : ClosedSubset G d) (r : Profiles) (e e' : Ext)
    (he : ExternalAgreement G val d S e e') :
    restrictOutput G val d S (CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d r e) =
      restrictOutput G val d S (CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d r e') := by
  funext i
  exact eval_eq_on_fullClosed G val d S r e e' he ⟨i, S.2.2.1 i i.2⟩ i.2

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The index of an equation (O): a closed set `S`, a value of `S`, and two values
of `v₂` that agree on `E(S)`. -/
abbrev OrderingIndex :=
  Σ S : ClosedSubset G d, SubsetAssign val S.val ×
    {ee : Ext × Ext // ExternalAgreement G val d S ee.1 ee.2}

noncomputable instance : Fintype (OrderingIndex G val d) := Fintype.ofFinite _

/-- Coefficients of equations (N), one for each value of `v₂`. -/
noncomputable def normalizationMatrix : Matrix Ext Rows ℝ := by
  classical
  exact fun e x => if x.2 = e then 1 else 0

noncomputable def marginIndicator (S : ClosedSubset G d) (a : SubsetAssign val S.val)
    (out : Out) : ℝ := by
  classical
  exact if restrictOutput G val d S out = a then 1 else 0

/-- The margin `p_S(a ∣ v₂)`: the sum of `p(v₁ ∣ v₂)` over the values `v₁` of
the members that agree with `a` on `S`. -/
noncomputable def margin (p : Rows → ℝ) (S : ClosedSubset G d)
    (a : SubsetAssign val S.val) (e : Ext) : ℝ :=
  ∑ out, marginIndicator G val d S a out * p (out, e)

/-- Coefficients of equations (O), each written as the difference of the two
margins being equated. -/
noncomputable def orderingMatrix : Matrix (OrderingIndex G val d) Rows ℝ := by
  classical
  exact fun o x =>
    (if x.2 = o.2.2.val.1 then marginIndicator G val d o.1 o.2.1 x.1 else 0) -
    (if x.2 = o.2.2.val.2 then marginIndicator G val d o.1 o.2.1 x.1 else 0)

theorem normalization_score (p : Rows → ℝ) (e : Ext) :
    (∑ x, normalizationMatrix G val d e x * p x) = ∑ out, p (out, e) := by
  classical
  simp [normalizationMatrix, Fintype.sum_prod_type, ite_mul]

theorem ordering_score (p : Rows → ℝ) (o : OrderingIndex G val d) :
    (∑ x, orderingMatrix G val d o x * p x) =
      margin G val d p o.1 o.2.1 o.2.2.val.1 - margin G val d p o.1 o.2.1 o.2.2.val.2 := by
  classical
  simp [orderingMatrix, margin, Fintype.sum_prod_type, sub_mul, ite_mul, Finset.sum_sub_distrib]

/-- Every column of `B` satisfies (N). -/
theorem normalization_column (r : Profiles) (e : Ext) :
    (∑ x, normalizationMatrix G val d e x *
      CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d x r) = 1 := by
  rw [normalization_score]
  simp [CompactDistrict.matrix_eq_eval]

/-- In a column of `B`, the margin over `S` is the indicator that the profile
gives the members of `S` the values `a`. -/
theorem margin_column (r : Profiles) (S : ClosedSubset G d)
    (a : SubsetAssign val S.val) (e : Ext) :
    margin G val d
      (fun x => CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d x r) S a e =
      marginIndicator G val d S a
        (CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d r e) := by
  classical
  simp [margin, CompactDistrict.matrix_eq_eval, mul_ite]

/-- Every column of `B` satisfies (O). -/
theorem ordering_column (r : Profiles) (o : OrderingIndex G val d) :
    (∑ x, orderingMatrix G val d o x *
      CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d x r) = 0 := by
  rw [ordering_score, margin_column, margin_column]
  have he := restrict_eval_eq G val d o.1 r o.2.2.val.1 o.2.2.val.2 o.2.2.property
  simp only [marginIndicator, he, sub_self]

/-- The coefficient matrix `(N; O)` of equations (N) and (O), stacked. -/
noncomputable def constraintsMatrix : Matrix (Ext ⊕ OrderingIndex G val d) Rows ℝ :=
  Matrix.fromRows (normalizationMatrix G val d) (orderingMatrix G val d)

def constraintsRhs : Ext ⊕ OrderingIndex G val d → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

/-- A vector `p` solves the stacked system if and only if it satisfies (N) and
(O) as stated above. -/
theorem feasible_iff (p : Rows → ℝ) :
    EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) p ↔
      (∀ e : Ext, (∑ out, p (out, e)) = 1) ∧
      ∀ (S : ClosedSubset G d) (a : SubsetAssign val S.val) (e e' : Ext),
        ExternalAgreement G val d S e e' → margin G val d p S a e = margin G val d p S a e' := by
  constructor
  · intro h
    constructor
    · intro e
      have hn := h (Sum.inl e)
      change (∑ x, normalizationMatrix G val d e x * p x) = 1 at hn
      rwa [normalization_score] at hn
    · intro S a e e' he
      have ho := h (Sum.inr ⟨S, a, ⟨(e, e'), he⟩⟩)
      change (∑ x, orderingMatrix G val d ⟨S, a, ⟨(e, e'), he⟩⟩ x * p x) = 0 at ho
      rw [ordering_score] at ho
      exact sub_eq_zero.mp ho
  · rintro ⟨hn, ho⟩ index
    cases index with
    | inl e =>
        change (∑ x, normalizationMatrix G val d e x * p x) = 1
        rw [normalization_score]
        exact hn e
    | inr o =>
        change (∑ x, orderingMatrix G val d o x * p x) = 0
        rw [ordering_score, ho o.1 o.2.1 o.2.2.val.1 o.2.2.val.2 o.2.2.property]
        exact sub_self _

/-- Equations (N) and (O) hold at every point of the district polytope. -/
theorem constraints_of_mixture (p : Rows → ℝ)
    (hp : p ∈ Polytope.mixture
      (CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d)) :
    EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d) p := by
  obtain ⟨q, hq, rfl⟩ := hp
  intro index
  cases index with
  | inl e =>
      change (∑ x, normalizationMatrix G val d e x *
        (CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d).mulVec q x) = 1
      rw [Polytope.score_mulVec]
      simp_rw [normalization_column]
      simpa only [mul_one] using hq.2
  | inr o =>
      change (∑ x, orderingMatrix G val d o x *
        (CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d).mulVec q x) = 0
      rw [Polytope.score_mulVec]
      simp only [ordering_column, mul_zero, Finset.sum_const_zero]

variable [∀ i, Nonempty (val i)]

/-- The point used in Step 3 of the proof of Proposition 4: the uniform
distribution of the members, repeated for every value of `v₂`. -/
noncomputable def uniformKernel : Rows → ℝ :=
  fun x => uniformDist Out x.1

omit [∀ i, DecidableEq (val i)] in
theorem uniformKernel_pos (x : Rows) : 0 < uniformKernel G val d x :=
  uniformDist_pos Out x.1

theorem uniformKernel_feasible :
    EqualityConstraints.Feasible (constraintsMatrix G val d) (constraintsRhs G val d)
      (uniformKernel G val d) := by
  intro index
  cases index with
  | inl e =>
      change (∑ x, normalizationMatrix G val d e x * uniformKernel G val d x) = 1
      rw [normalization_score]
      exact (uniformDist_mem_stdSimplex Out).2
  | inr o =>
      change (∑ x, orderingMatrix G val d o x * uniformKernel G val d x) = 0
      rw [ordering_score]
      simp only [margin, uniformKernel, sub_self]

/-- An equation `gᵀp = c` holds at every strictly positive solution of (N) and (O)
if and only if it is a linear combination of (N) and (O). This is Step 3 of the
proof of Proposition 4 (i); `CompactDistrict.EqualityTriviality` connects it to
Definition 4. -/
theorem positive_equation_iff_rowCombination (g : Rows → ℝ) (c : ℝ) :
    EqualityConstraints.PositiveConsequence
      (constraintsMatrix G val d) (constraintsRhs G val d) g c ↔
    EqualityConstraints.RowCombination
      (constraintsMatrix G val d) (constraintsRhs G val d) g c :=
  EqualityConstraints.positive_consequence_iff_rowCombination _ _ g c
    (uniformKernel G val d) (uniformKernel_feasible G val d) (uniformKernel_pos G val d)

end MeraConstraints.CompactDistrict.OrderingConstraints
