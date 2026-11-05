import MeraConstraints.Probability.Independent
import MeraConstraints.Probability.Pushforward

/-!
# Independent laws under coordinatewise maps and regrouping

The response function variable transformation must keep the districts' response
function variables independent. This chapter proves two identities for finite
value sets that give this.

First, applying a map to each coordinate separately carries a product law to the
product of the mapped coordinate laws (`pushforward_coordinatewise`). Second,
grouping the coordinates into blocks carries a product law to a product of block
laws, each the product of the original coordinate laws in that block
(`pushforward_groupEquiv`). Together they show that a district's response
function variables may depend on all the inputs assigned to that district, and
the variables of different districts are still independent, because the blocks
are disjoint (`pushforward_grouped`).

The value sets here are finite. The corresponding statement for arbitrary
measurable value sets is in `Probability.IndependentGroupingMeasure`.
-/

namespace MeraConstraints.Independent

section CoordinateMaps

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {X Y : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Y d)]

/-- Mapping each coordinate separately sends the product law `joint q` to the
product of the mapped coordinate laws. -/
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

/-- Regroup an assignment of the coordinates `i` into its blocks `block i = d`,
by restriction. Blocks may be empty; `block` need not be surjective. -/
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

/-- Regrouping a tuple with independent coordinates gives independent block
tuples. The law of each block is the product of its original coordinate laws. -/
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

/-- A map for each block may use all the coordinates of its block together. The
law of the outputs is still the product of the laws of the block outputs. -/
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
