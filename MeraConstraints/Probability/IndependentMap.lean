import MeraConstraints.Probability.Independent
import MeraConstraints.Probability.Pushforward

/-!
# Independent laws under local maps and regrouping

The response-function reduction must preserve the independence of distinct
districts, rather than impose that independence after the reduction. This
chapter proves two finite probability identities that supply that step.

First, mapping each coordinate separately carries a product law to the
product of the mapped coordinate laws. The proof is the rectangular-event
formula applied to the fibers of those maps. Second, grouping coordinates
according to a block map is an equivalence of assignment types. Transporting
the original product law along it yields independent block laws, each of
which is the product of the original coordinate laws within that block.

Combining the two facts permits a district's response-profile map to depend
jointly on all exogenous coordinates assigned to that district. Distinct
district profiles remain independent because the source law was a product
law and the grouping is disjoint. No independence of the mapped profiles is
assumed in any of these theorems. Source state spaces in this chapter are
finite; arbitrary measurable latent spaces require a separate measure-theory
bridge.
-/

namespace MeraConstraints.Independent

section CoordinateMaps

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {X Y : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Y d)]

/-- Coordinatewise measurable information reduction in the finite setting
preserves the explicit product-law construction. -/
theorem pushforward_coordinatewise (f : ∀ d, X d → Y d) (q : ∀ d, X d → ℝ) :
    pushforward (fun x => fun d => f d (x d)) (joint q) =
      joint (fun d => pushforward (f d) (q d)) := by
  funext y
  classical
  simp only [pushforward, Finset.sum_filter]
  simp_rw [funext_iff]
  simpa only [joint, pushforward, Finset.sum_filter] using
    rectangular_mass q (fun d x => f d x = y d)

end CoordinateMaps

section Grouping

variable {I D : Type*} (block : I → D) (X : I → Type*)

/-- Disjoint regrouping of a dependent coordinate assignment into its blocks.
The equivalence is valid for empty blocks and does not require surjectivity
of `block`. Its forward map is literal restriction, without arbitrary choices. -/
def groupEquiv : (∀ i, X i) ≃ (∀ d, ∀ i : {i : I // block i = d}, X i) where
  toFun x _ i := x i
  invFun y i := y (block i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv y := by
    funext d i
    rcases i with ⟨i, hi⟩
    subst d
    rfl

@[simp] theorem groupEquiv_apply (x : ∀ i, X i) (d : D)
    (i : {i : I // block i = d}) : groupEquiv block X x d i = x i := rfl

@[simp] theorem groupEquiv_symm_apply
    (y : ∀ d, ∀ i : {i : I // block i = d}, X i) (i : I) :
    (groupEquiv block X).symm y i = y (block i) ⟨i, rfl⟩ := rfl

variable [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

private theorem pushforward_equiv_apply {A B : Type*} [Fintype A] [DecidableEq B]
    (e : A ≃ B) (p : A → ℝ) (b : B) : pushforward e p b = p (e.symm b) := by
  classical
  have hf : Finset.univ.filter (fun a => e a = b) = {e.symm b} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact e.apply_eq_iff_eq_symm_apply
  simp only [pushforward, hf, Finset.sum_singleton]

/-- Regrouping an independent source tuple produces independent block tuples.
Each block's law is the product of its original coordinate laws. -/
theorem pushforward_groupEquiv (q : ∀ i, X i → ℝ) :
    pushforward (groupEquiv block X) (joint q) =
      joint (fun d => joint (fun i : {i : I // block i = d} => q i)) := by
  funext y
  rw [pushforward_equiv_apply]
  change (∏ i, q i (y (block i) ⟨i, rfl⟩)) =
    ∏ d, ∏ i : {i : I // block i = d}, q i (y d i)
  symm
  calc
    _ = ∏ d, ∏ i : {i : I // block i = d}, q i (y (block i) ⟨i, rfl⟩) := by
      apply Finset.prod_congr rfl
      intro d _
      apply Finset.prod_congr rfl
      rintro ⟨i, hi⟩ _
      subst d
      rfl
    _ = _ := Fintype.prod_fiberwise block (fun i => q i (y (block i) ⟨i, rfl⟩))

/-- A local map may use all source coordinates of its block jointly. Its
output law is nevertheless the product of the corresponding block laws. -/
theorem pushforward_grouped {Y : D → Type*} [∀ d, DecidableEq (Y d)]
    (f : ∀ d, (∀ i : {i : I // block i = d}, X i) → Y d) (q : ∀ i, X i → ℝ) :
    pushforward (fun x => fun d => f d (fun i => x i)) (joint q) =
      joint (fun d => pushforward (f d) (joint (fun i : {i : I // block i = d} => q i))) := by
  calc
    _ = pushforward (fun x => fun d => f d (x d))
        (pushforward (groupEquiv block X) (joint q)) :=
      (FiniteProbability.pushforward_comp (groupEquiv block X)
        (fun x => fun d => f d (x d)) (joint q)).symm
    _ = _ := by rw [pushforward_groupEquiv, pushforward_coordinatewise]

end Grouping
end MeraConstraints.Independent
