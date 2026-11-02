import MeraConstraints.CompactDistrict
import MeraConstraints.HiddenGraph.Ancestry
import MeraConstraints.EqualityConstraints
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The actual normalization and ordering equations (N)/(O)

In Proposition `prop:nontrivial` (i), equations (N) normalize each external
input block. Equations (O) equate margins for a **fully closed** nonempty
subset of the district at external inputs agreeing on that subset's parents.
The closure here is `HiddenGraph.FullClosed`: directed ancestral paths may
leave the district and return. Internal-parent closure alone would also include
Verma equalities and must not replace this definition.

We construct both coefficient matrices on the manuscript's compact `(v₁,v₂)`
rows, prove every deterministic compatibility column satisfies them, and
extend the result to every response-profile mixture. The normalized uniform
kernel is a strictly positive solution of these concrete equations.

These facts show (N)/(O) are equality constraints of the district polytope.
They do not yet show that they are *trivial* in the manuscript's sense:
that requires every positive observed law satisfying the graph's ordinary
conditional independencies to satisfy them. In particular, one fixed-order
`OrderedMarkov` hypothesis is not substituted for the ordering-invariance
argument over all full-ancestry-closed subsets.
-/

namespace MeraConstraints.CompactDistrict.OrderingConstraints

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)] (d : HiddenGraph.DistrictId G)

local notation "Out" => MemberAssign val (HiddenGraph.observedDistrict G) d
local notation "Ext" => ExternalAssign G.observed val (HiddenGraph.observedDistrict G) d
local notation "Rows" => Row G.observed val (HiddenGraph.observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (HiddenGraph.observedDistrict G) d

/-- Precisely the nonempty closed subsets used in equations (O). -/
abbrev ClosedSubset :=
  {S : Finset (Fin n) // S.Nonempty ∧ HiddenGraph.FullClosed G d S}

noncomputable instance : Fintype (ClosedSubset G d) := Fintype.ofFinite _

abbrev SubsetAssign (S : Finset (Fin n)) := ∀ i : {i : Fin n // i ∈ S}, val i

/-- Restrict a district assignment to the specified fully closed subset. -/
def restrictOutput (S : ClosedSubset G d) (out : Out) : SubsetAssign val S.val :=
  fun i => out ⟨i, S.2.2.1 i i.2⟩

/-- Agreement on `E(S)`, not on every external parent of the district. -/
def ExternalAgreement (S : ClosedSubset G d) (e e' : Ext) : Prop :=
  ∀ j : ExternalParent G.observed (HiddenGraph.observedDistrict G) d,
    (∃ i : Fin n, i ∈ S.val ∧ j.val ∈ G.observed.parents i) → e j = e' j

/-- Deterministic outputs in `S` depend only on `E(S)`. Full observed
ancestry closure supplies internal-parent closure in the recursive step. -/
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

/-- A row of (O): subset, partial observed value, and two agreeing inputs. -/
abbrev OrderingIndex :=
  Σ S : ClosedSubset G d, SubsetAssign val S.val ×
    {ee : Ext × Ext // ExternalAgreement G val d S ee.1 ee.2}

noncomputable instance : Fintype (OrderingIndex G val d) := Fintype.ofFinite _

/-- Coefficients of the normalization equation at one external input. -/
noncomputable def normalizationMatrix : Matrix Ext Rows ℝ := by
  classical
  exact fun e x => if x.2 = e then 1 else 0

noncomputable def marginIndicator (S : ClosedSubset G d) (a : SubsetAssign val S.val)
    (out : Out) : ℝ := by
  classical
  exact if restrictOutput G val d S out = a then 1 else 0

/-- The margin at `a`, summing over the other members of the district. -/
noncomputable def margin (p : Rows → ℝ) (S : ClosedSubset G d)
    (a : SubsetAssign val S.val) (e : Ext) : ℝ :=
  ∑ out, marginIndicator G val d S a out * p (out, e)

/-- Coefficients of the difference between the two margins in (O). -/
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

/-- Each deterministic column is a normalized point mass in every input block. -/
theorem normalization_column (r : Profiles) (e : Ext) :
    (∑ x, normalizationMatrix G val d e x *
      CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d x r) = 1 := by
  rw [normalization_score]
  simp [CompactDistrict.matrix_eq_eval]

/-- A deterministic column margin is the indicator of the subset's output. -/
theorem margin_column (r : Profiles) (S : ClosedSubset G d)
    (a : SubsetAssign val S.val) (e : Ext) :
    margin G val d
      (fun x => CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d x r) S a e =
      marginIndicator G val d S a
        (CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d r e) := by
  classical
  simp [margin, CompactDistrict.matrix_eq_eval, mul_ite]

/-- Fully closed margins have the same value at external inputs agreeing on
their own parents, hence every compatibility column satisfies (O). -/
theorem ordering_column (r : Profiles) (o : OrderingIndex G val d) :
    (∑ x, orderingMatrix G val d o x *
      CompactDistrict.matrix G.observed val (HiddenGraph.observedDistrict G) d x r) = 0 := by
  rw [ordering_score, margin_column, margin_column]
  have he := restrict_eval_eq G val d o.1 r o.2.2.val.1 o.2.2.val.2 o.2.2.property
  simp only [marginIndicator, he, sub_self]

/-- The actual coefficient matrix `(N;O)` and its affine right-hand side. -/
noncomputable def constraintsMatrix : Matrix (Ext ⊕ OrderingIndex G val d) Rows ℝ :=
  Matrix.fromRows (normalizationMatrix G val d) (orderingMatrix G val d)

def constraintsRhs : Ext ⊕ OrderingIndex G val d → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

/-- The matrix system is exactly the stated block normalizations and closed
margin equalities, not a stronger unspecified family of constraints. -/
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

/-- The concrete (N)/(O) equations hold throughout the district polytope. -/
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

/-- The positive reference point in Appendix Step 3: uniform district output
at every external input, rather than uniform mass over all compact rows. -/
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

/-- The generic affine-consequence theorem applies to these actual (N)/(O)
matrices. This concerns consequences on their positive kernel solution set;
identifying it with graph-trivial equalities still requires realization. -/
theorem positive_equation_iff_rowCombination (g : Rows → ℝ) (c : ℝ) :
    EqualityConstraints.PositiveConsequence
      (constraintsMatrix G val d) (constraintsRhs G val d) g c ↔
    EqualityConstraints.RowCombination
      (constraintsMatrix G val d) (constraintsRhs G val d) g c :=
  EqualityConstraints.positive_consequence_iff_rowCombination _ _ g c
    (uniformKernel G val d) (uniformKernel_feasible G val d) (uniformKernel_pos G val d)

end MeraConstraints.CompactDistrict.OrderingConstraints
