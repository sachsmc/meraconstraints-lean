import MeraConstraints.GlobalModel.ObservableMargins

/-!
# Necessity of every manuscript (N)/(O) equation

Proposition `prop:nontrivial`, proof Step 1: the observable district factor
of every strictly positive graph-compatible observed law satisfies (N) and
(O). The law need not belong to the hidden-variable marginal model.

For (N), the retained product on the empty ancestral set is one. For (O),
take the full observed ancestors of the specified fully closed subset `S`.
Its intersection with the district is exactly `S`, even when directed paths
leave the district and return. The literal margin equals the retained
product, which depends only on `S` and its own external parents `E(S)`.
Thus this proves all fully closed subset equations, not just fixed-order
prefix equations. The theorem uses no c-degree bound.
-/

namespace MeraConstraints.GlobalModel.OrderingInvariance

open FiniteProbability HiddenGraph
open GlobalModel.KernelReconstruction

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, Nonempty (val i)]

/-- Full closure is exactly what identifies the district portion of the
ancestor set; internal-parent closure would not suffice. -/
theorem fullClosed_ancestor_intersection (d : DistrictId G) (S : Finset (Fin n))
    (hS : FullClosed G d S) :
    (observedAncestors G S).filter (fun j => observedDistrict G j = d) = S := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨hiA, hid⟩ := Finset.mem_filter.mp hi
    obtain ⟨j, hj, hij⟩ := (mem_observedAncestors G S i).mp hiA
    exact hS.2 j hj i hij hid
  · intro hi
    exact Finset.mem_filter.mpr ⟨subset_observedAncestors G S hi, hS.1 i hi⟩

/-- Equation (N), for every external-input block of the actual compact factor. -/
theorem observable_normalization (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (d : DistrictId G)
    (e : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d) :
    (∑ out, CompactDistrict.observableFactor G.observed val (observedDistrict G) d p (out, e)) = 1 := by
  classical
  let out : Output G val d := fun i => Classical.choice (inferInstance : Nonempty (val i))
  let w := CompactDistrict.extend G.observed val (observedDistrict G) d (out, e)
  have he : (fun j : CompactDistrict.ExternalParent G.observed (observedDistrict G) d => w j.val) = e :=
    congrArg Prod.snd (CompactDistrict.project_extend G.observed val (observedDistrict G) d (out, e))
  have h := observable_setMargin_eq_ancestralProduct G val p hpos hGlobal d ∅
    (by simp [ObservedAncestral]) w
  rw [ancestralProduct_empty] at h
  simpa only [setMargin, SetMatch, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    forall_const, if_true, he, observableKernels] using h

/-- Equation (O), for every fully closed subset and every pair of external
inputs agreeing on that subset's own parents. -/
theorem observable_ordering (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (d : DistrictId G)
    (S : CompactDistrict.OrderingConstraints.ClosedSubset G d)
    (a : CompactDistrict.OrderingConstraints.SubsetAssign val S.val)
    (e e' : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d)
    (hee : CompactDistrict.OrderingConstraints.ExternalAgreement G val d S e e') :
    CompactDistrict.OrderingConstraints.margin G val d
        (CompactDistrict.observableFactor G.observed val (observedDistrict G) d p) S a e =
      CompactDistrict.OrderingConstraints.margin G val d
        (CompactDistrict.observableFactor G.observed val (observedDistrict G) d p) S a e' := by
  classical
  let out : Output G val d := fun i =>
    if hi : i.val ∈ S.val then a ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty (val i))
  let w := CompactDistrict.extend G.observed val (observedDistrict G) d (out, e)
  let v := CompactDistrict.extend G.observed val (observedDistrict G) d (out, e')
  have hw := CompactDistrict.project_extend G.observed val (observedDistrict G) d (out, e)
  have hv := CompactDistrict.project_extend G.observed val (observedDistrict G) d (out, e')
  have hwm (i : CompactDistrict.Member (observedDistrict G) d) : w i.val = out i :=
    congrFun (congrArg Prod.fst hw) i
  have hvm (i : CompactDistrict.Member (observedDistrict G) d) : v i.val = out i :=
    congrFun (congrArg Prod.fst hv) i
  have hwe : (fun j : CompactDistrict.ExternalParent G.observed (observedDistrict G) d => w j.val) = e :=
    congrArg Prod.snd hw
  have hve : (fun j : CompactDistrict.ExternalParent G.observed (observedDistrict G) d => v j.val) = e' :=
    congrArg Prod.snd hv
  have hwa : (fun j : {j : Fin n // j ∈ S.val} => w j.val) = a := by
    funext j
    rw [hwm ⟨j, S.2.2.1 j j.2⟩]
    exact dif_pos j.2
  have hva : (fun j : {j : Fin n // j ∈ S.val} => v j.val) = a := by
    funext j
    rw [hvm ⟨j, S.2.2.1 j j.2⟩]
    exact dif_pos j.2
  let A := observedAncestors G S.val
  have hA : ObservedAncestral G A := observedAncestors_ancestral G S.val
  have hS : S.val = A.filter (fun j => observedDistrict G j = d) :=
    (fullClosed_ancestor_intersection G d S.val S.2.2).symm
  have hmw := setMargin_eq_closedMargin G val (observableKernels G val p) d A w S hS
  have hmv := setMargin_eq_closedMargin G val (observableKernels G val p) d A v S hS
  rw [hwa, hwe] at hmw
  rw [hva, hve] at hmv
  change CompactDistrict.OrderingConstraints.margin G val d (observableKernels G val p d) S a e =
    CompactDistrict.OrderingConstraints.margin G val d (observableKernels G val p d) S a e'
  rw [← hmw, ← hmv, observable_setMargin_eq_ancestralProduct G val p hpos hGlobal d A hA,
    observable_setMargin_eq_ancestralProduct G val p hpos hGlobal d A hA]
  apply ancestralProduct_congr
  · intro j hj hjd
    exact (hwm ⟨j, hjd⟩).trans (hvm ⟨j, hjd⟩).symm
  · intro j hj hjd l hlj hld
    have hjS : j ∈ S.val := by rw [hS]; exact Finset.mem_filter.mpr ⟨hj, hjd⟩
    let l' : CompactDistrict.ExternalParent G.observed (observedDistrict G) d := ⟨l, hld, j, hjd, hlj⟩
    exact (congrFun hwe l').trans ((hee l' ⟨j, hjS, hlj⟩).trans (congrFun hve l').symm)

/-- The actual stacked manuscript matrix `(N;O)` holds for every positive
globally Markov observed law, without a hidden-variable realization premise. -/
theorem observable_constraints (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (hGlobal : MoralGlobalMarkov G val p) (d : DistrictId G) :
    EqualityConstraints.Feasible
      (CompactDistrict.OrderingConstraints.constraintsMatrix G val d)
      (CompactDistrict.OrderingConstraints.constraintsRhs G val d)
      (CompactDistrict.observableFactor G.observed val (observedDistrict G) d p) := by
  apply (CompactDistrict.OrderingConstraints.feasible_iff G val d _).mpr
  exact ⟨observable_normalization G val p hpos hGlobal d,
    observable_ordering G val p hpos hGlobal d⟩

end MeraConstraints.GlobalModel.OrderingInvariance
