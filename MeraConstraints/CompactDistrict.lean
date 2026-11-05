import MeraConstraints.GlobalModel

/-!
# The matrix `B` with rows `(v₁, v₂)`

For a district with members `V₁` and external parents `V₂`, the manuscript's
compatibility matrix `B` has one row for each pair `(v₁, v₂)` and one column for
each profile. `CompactDistrict.matrix` is this matrix `B`. `GlobalModel.matrix`
has complete assignments of all observed variables as rows, so its rows repeat
whenever assignments differ only outside `V₁` and `V₂`.

The entry of `B` at row `(v₁, v₂)` and profile `r` is `1` when every member's
response function in `r`, applied to the values of its parents in the row,
returns the member's value in `v₁` (`Compatible`), and `0` otherwise. By
`eval_eq_iff_compatible` this means that `r`, with the external parents set to
`v₂`, gives the members the values `v₁`; `eval` computes those values recursively
along the topological order.

`project` sends a complete assignment to its row, and `matrix_project` shows that
both matrices have the same entries there. When every observed variable has at
least one value, each row extends to a complete assignment. Hence a vector indexed by rows
lies in the district polytope of `B` if and only if its pullback to complete
assignments lies in that of `GlobalModel.matrix`
(`pullback_mem_mixture_iff`), and an H-representation of `B` describes the
pulled-back vectors (`pullback_mem_mixture_iff_HRep`).
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

/-- A row `(v₁, v₂)` of `B`: values of the members and of the external parents,
each variable appearing once. -/
abbrev Row := MemberAssign val block d × ExternalAssign G val block d

/-- Keep the values of the members and external parents of a complete assignment. -/
def project (w : FullAssign val) : Row G val block d :=
  (fun i => w i, fun j => w j)

/-- The values of a member's parents in a row: from `v₁` for a member, from `v₂`
for an external parent. -/
def parentAssign (x : Row G val block d) (i : Member block d) :
    PaAssign G val i :=
  fun j => if hj : block j = d then x.1 ⟨j, hj⟩
    else x.2 ⟨j, hj, ⟨i, i.2, j.2⟩⟩

theorem parentAssign_project (w : FullAssign val) (i : Member block d) :
    parentAssign G val block d (project G val block d w) i = PaAssign.restrict w i := by
  funext j
  unfold parentAssign
  split <;> rfl

/-- The row `(v₁, v₂)` is compatible with the profile `r`: each member's response
function, applied to its parents' values in the row, returns its value in `v₁`. -/
def Compatible (x : Row G val block d) (r : GlobalModel.Profile G val block d) : Prop :=
  ∀ i : Member block d, r i (parentAssign G val block d x i) = x.1 i

theorem compatible_project (w : FullAssign val) (r : GlobalModel.Profile G val block d) :
    Compatible G val block d (project G val block d w) r ↔
      GlobalModel.Compatible G val block d w r := by
  simp only [Compatible, GlobalModel.Compatible, parentAssign_project]
  rfl

/-- The values that the profile `r` gives the members when the external parents
take the values `e`. Defined by recursion on the topological order of the observed
variables. -/
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

/-- The row `(v₁, v₂)` is compatible with `r` if and only if `r`, with the
external parents set to `v₂`, gives the members the values `v₁`. -/
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

/-- The compatibility matrix `B`: entry `((v₁, v₂), r)` is `1` if the row is
compatible with the profile `r` and `0` otherwise. -/
noncomputable def matrix : Matrix (Row G val block d) (GlobalModel.Profile G val block d) ℝ := by
  classical
  exact fun x r => if Compatible G val block d x r then 1 else 0

omit [∀ i, Fintype (val i)] in
theorem matrix_eq_eval (x : Row G val block d) (r : GlobalModel.Profile G val block d) :
    matrix G val block d x r = if eval G val block d r x.2 = x.1 then 1 else 0 := by
  classical
  simp only [matrix, eval_eq_iff_compatible]

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
/-- The entry of `GlobalModel.matrix` at a complete assignment is the entry of `B`
at its row. -/
theorem matrix_project (w : FullAssign val) (r : GlobalModel.Profile G val block d) :
    matrix G val block d (project G val block d w) r = GlobalModel.matrix G val block d w r := by
  classical
  simp only [matrix, GlobalModel.matrix, compatible_project]

theorem mulVec_project (q : GlobalModel.Profile G val block d → ℝ) (w : FullAssign val) :
    (matrix G val block d).mulVec q (project G val block d w) =
      (GlobalModel.matrix G val block d).mulVec q w := by
  simp only [Matrix.mulVec, dotProduct, matrix_project]

variable [∀ i, Nonempty (val i)]

/-- Extend a row to a complete assignment by choosing values arbitrarily for the
other variables. -/
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

/-- A vector `p` indexed by rows lies in the district polytope of `B` if and only
if its pullback to complete assignments lies in the district polytope of
`GlobalModel.matrix`. -/
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

/-- An H-representation of `B` describes the vectors `p` whose pullback lies in
the district polytope of `GlobalModel.matrix`. -/
theorem pullback_mem_mixture_iff_HRep {I E : Type*}
    (H : Polytope.HRep (matrix G val block d) I E) (p : Row G val block d → ℝ) :
    (fun w => p (project G val block d w)) ∈ Polytope.mixture (GlobalModel.matrix G val block d) ↔
      (∀ i, ∑ x, H.inequalities i x * p x ≤ H.upper i) ∧
      (∀ e, ∑ x, H.equalities e x * p x = H.target e) := by
  rw [pullback_mem_mixture_iff]
  exact H.exact_representation p

end MeraConstraints.CompactDistrict
