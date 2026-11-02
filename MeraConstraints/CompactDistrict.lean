import MeraConstraints.GlobalModel

/-!
# District rows with precisely the manuscript's coordinates

The manuscript's compatibility matrix has one row for each pair `(v₁,v₂)`:
values of all observed district members and their external observed parents.
`GlobalModel.matrix` instead retained a complete observed assignment as its
row index. Coordinates outside these two sets cause repeated rows.

This chapter defines the compact row type directly. Its parent assignment
chooses a parent's value from the district assignment when that parent is a
member, and from the external assignment otherwise. Compatibility means
that every district mechanism satisfies its structural equation using those
values. A well-founded local evaluation, following the original global
topological order, proves this predicate is the usual deterministic district
output event. No ordering of whole districts is required.

The projection of a full assignment gives exactly the same matrix entry.
When observed state spaces are nonempty, every compact row extends to a full
assignment. Hence compact simplex feasibility is equivalent to full-row
feasibility for the pulled-back vector, and any checked compact H-system can
be used without computing a second H-system on the repeated full rows.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D) (d : D)

abbrev Member := {i : Fin n // block i = d}

/-- An observed parent outside the district, `Paobs(V₁) \ V₁`. -/
def IsExternalParent (j : Fin n) : Prop :=
  block j ≠ d ∧ ∃ i : Fin n, block i = d ∧ j ∈ G.parents i

abbrev ExternalParent := {j : Fin n // IsExternalParent G block d j}

noncomputable instance : Fintype (ExternalParent G block d) := Fintype.ofFinite _

abbrev MemberAssign := ∀ i : Member block d, val i
abbrev ExternalAssign := ∀ j : ExternalParent G block d, val j

/-- The manuscript's pair `(v₁,v₂)`, with each variable appearing once. -/
abbrev Row := MemberAssign val block d × ExternalAssign G val block d

/-- Discard irrelevant coordinates of a full observed assignment. -/
def project (w : FullAssign val) : Row G val block d :=
  (fun i => w i, fun j => w j)

/-- The parent values supplied by a compact district row. -/
def parentAssign (x : Row G val block d) (i : Member block d) :
    PaAssign G val i :=
  fun j => if hj : block j = d then x.1 ⟨j, hj⟩
    else x.2 ⟨j, hj, ⟨i, i.2, j.2⟩⟩

theorem parentAssign_project (w : FullAssign val) (i : Member block d) :
    parentAssign G val block d (project G val block d w) i = PaAssign.restrict w i := by
  funext j
  unfold parentAssign
  split <;> rfl

/-- The structural equations for one compact row and deterministic profile. -/
def Compatible (x : Row G val block d) (r : GlobalModel.Profile G val block d) : Prop :=
  ∀ i : Member block d, r i (parentAssign G val block d x i) = x.1 i

theorem compatible_project (w : FullAssign val) (r : GlobalModel.Profile G val block d) :
    Compatible G val block d (project G val block d w) r ↔
      GlobalModel.Compatible G val block d w r := by
  simp only [Compatible, GlobalModel.Compatible, parentAssign_project]
  rfl

/-- Evaluate the district with all external parents fixed. Recursion uses
the original observed index, so internal members need not be contiguous. -/
def eval (r : GlobalModel.Profile G val block d) (e : ExternalAssign G val block d)
    (i : Member block d) : val i :=
  r i (fun j => if hj : block j = d then eval r e ⟨j, hj⟩
    else e ⟨j, hj, ⟨i, i.2, j.2⟩⟩)
termination_by i.val.val
decreasing_by exact G.parents_lt j.2

theorem eval_eq (r : GlobalModel.Profile G val block d) (e : ExternalAssign G val block d)
    (i : Member block d) :
    eval G val block d r e i =
      r i (parentAssign G val block d (eval G val block d r e, e) i) := by
  rw [eval]
  rfl

theorem eval_unique_apply (x : Row G val block d) (r : GlobalModel.Profile G val block d)
    (hx : Compatible G val block d x r) (i : Member block d) :
    eval G val block d r x.2 i = x.1 i := by
  rw [eval, ← hx i]
  congr 1
  funext j
  by_cases hj : block j = d
  · simp only [parentAssign, dif_pos hj]
    exact eval_unique_apply x r hx ⟨j, hj⟩
  · simp only [parentAssign, dif_neg hj]
termination_by i.val.val
decreasing_by exact G.parents_lt j.2

/-- Compact compatibility is exactly the deterministic district output event. -/
theorem eval_eq_iff_compatible (x : Row G val block d)
    (r : GlobalModel.Profile G val block d) :
    eval G val block d r x.2 = x.1 ↔ Compatible G val block d x r := by
  constructor
  · intro heq i
    have h := eval_eq G val block d r x.2 i
    rw [heq] at h
    exact h.symm
  · intro hx
    funext i
    exact eval_unique_apply G val block d x r hx i

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The manuscript's zero/one matrix, without irrelevant observed coordinates. -/
noncomputable def matrix : Matrix (Row G val block d) (GlobalModel.Profile G val block d) ℝ := by
  classical
  exact fun x r => if Compatible G val block d x r then 1 else 0

omit [∀ i, Fintype (val i)] in
theorem matrix_eq_eval (x : Row G val block d) (r : GlobalModel.Profile G val block d) :
    matrix G val block d x r = if eval G val block d r x.2 = x.1 then 1 else 0 := by
  classical
  simp only [matrix, eval_eq_iff_compatible]

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
/-- Pullback along the row projection is exactly the existing full-row matrix. -/
theorem matrix_project (w : FullAssign val) (r : GlobalModel.Profile G val block d) :
    matrix G val block d (project G val block d w) r = GlobalModel.matrix G val block d w r := by
  classical
  simp only [matrix, GlobalModel.matrix, compatible_project]

theorem mulVec_project (q : GlobalModel.Profile G val block d → ℝ) (w : FullAssign val) :
    (matrix G val block d).mulVec q (project G val block d w) =
      (GlobalModel.matrix G val block d).mulVec q w := by
  simp only [Matrix.mulVec, dotProduct, matrix_project]

variable [∀ i, Nonempty (val i)]

/-- Extend a compact row arbitrarily outside its members and external parents.
The compact matrix itself does not depend on this auxiliary extension. -/
noncomputable def extend (x : Row G val block d) : FullAssign val := by
  classical
  exact fun j => if hj : block j = d then x.1 ⟨j, hj⟩ else
    if he : IsExternalParent G block d j then x.2 ⟨j, he⟩ else Classical.choice (inferInstance)

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem project_extend (x : Row G val block d) :
    project G val block d (extend G val block d x) = x := by
  apply Prod.ext
  · funext i
    simp only [project, extend, dif_pos i.2]
  · funext j
    simp only [project, extend, dif_neg j.2.1, dif_pos j.2]

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem project_surjective : Function.Surjective (project G val block d) :=
  fun x => ⟨extend G val block d x, project_extend G val block d x⟩

/-- Compact V-feasibility is equivalent to V-feasibility on repeated full rows. -/
theorem pullback_mem_mixture_iff (p : Row G val block d → ℝ) :
    (fun w => p (project G val block d w)) ∈ Polytope.mixture (GlobalModel.matrix G val block d) ↔
      p ∈ Polytope.mixture (matrix G val block d) := by
  constructor
  · rintro ⟨q, hq, hm⟩
    refine ⟨q, hq, ?_⟩
    funext x
    have h := congrFun hm (extend G val block d x)
    rw [← mulVec_project, project_extend] at h
    exact h
  · rintro ⟨q, hq, hm⟩
    refine ⟨q, hq, ?_⟩
    funext w
    rw [← mulVec_project, hm]

/-- A checked H-representation on the manuscript's compact rows characterizes
the same pulled-back full-row factors used by reconstruction. No double
description computation on duplicated rows is necessary. -/
theorem pullback_mem_mixture_iff_HRep {I E : Type*}
    (H : Polytope.HRep (matrix G val block d) I E) (p : Row G val block d → ℝ) :
    (fun w => p (project G val block d w)) ∈ Polytope.mixture (GlobalModel.matrix G val block d) ↔
      (∀ i, ∑ x, H.inequalities i x * p x ≤ H.upper i) ∧
      (∀ e, ∑ x, H.equalities e x * p x = H.target e) := by
  rw [pullback_mem_mixture_iff]
  exact H.exact_representation p

end MeraConstraints.CompactDistrict
