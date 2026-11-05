import MeraConstraints.HiddenGraph.Ancestry
import MeraConstraints.CompactDistrict.InstrumentalStructure

/-!
# Structures that imply inequality constraints: reaching a member

This file is the first step towards Remark 3 (`prop:ineqstructure`). It restates
the definitions of `CompactDistrict` for the districts of a hidden variables DAG,
using `observedDistrict G`. An external parent `w` of the district `d` reaches a
member `v` (`DistrictReaches`) if there is a directed path from `w` to `v` whose
vertices other than `w` are members of `d`. A path of this kind is a directed
path in the observed DAG (`districtReaches_observedAncestor`). `InstrumentalStructure`
is the instrumental type of the remark.

`eval_eq_of_eq_on_districtReaches` is Step 1 of the proof in the Supplementary
Materials: the value of a member of the district depends on the values of the
external parents only through those that reach it. It holds for every c-degree.
The conclusion of the remark is proved in `InstrumentalInequalities.lean` and
`BellInequalities.lean`.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) (d : DistrictId G)

abbrev DistrictReaches (w v : Fin n) : Prop :=
  CompactDistrict.Reaches G.observed (observedDistrict G) d w v

abbrev InstrumentalStructure : Prop :=
  CompactDistrict.InstrumentalType G.observed (observedDistrict G) d

theorem districtReaches_observedAncestor {w v : Fin n} (h : DistrictReaches G d w v) :
    ObservedAncestor G w v := by
  obtain ⟨p⟩ := h
  induction p with
  | direct _ hwv => exact observedAncestor_of_parent G hwv
  | tail _ _ hij ih => exact observedAncestor_trans G ih (observedAncestor_of_parent G hij)

theorem districtReaches_lt {w v : Fin n} (h : DistrictReaches G d w v) : w < v :=
  CompactDistrict.reaches_lt G.observed (observedDistrict G) d h

theorem districtReaches_member {w v : Fin n} (h : DistrictReaches G d w v) :
    observedDistrict G v = d := by
  obtain ⟨p⟩ := h
  exact p.endpoint_member

theorem districtReaches_externalParent {w v : Fin n} (hw : observedDistrict G w ≠ d)
    (h : DistrictReaches G d w v) :
    CompactDistrict.IsExternalParent G.observed (observedDistrict G) d w :=
  CompactDistrict.isExternalParent_of_reaches G.observed (observedDistrict G) d hw h

variable [DecidableEq (DistrictId G)] (val : Fin n → Type*)

/-- Step 1 of the proof of Remark 3 (`prop:ineqstructure`): the value of the
member `i` is unchanged if the external parents that reach `i` keep their
values. -/
theorem eval_eq_of_eq_on_districtReaches
    (r : GlobalModel.Profile G.observed val (observedDistrict G) d)
    (e e' : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d)
    (i : CompactDistrict.Member (observedDistrict G) d)
    (he : ∀ w : CompactDistrict.ExternalParent G.observed (observedDistrict G) d,
      DistrictReaches G d w.val i.val → e w = e' w) :
    CompactDistrict.eval G.observed val (observedDistrict G) d r e i =
      CompactDistrict.eval G.observed val (observedDistrict G) d r e' i :=
  CompactDistrict.eval_eq_of_eq_on_reaching G.observed (observedDistrict G) d val r e e' i he

end MeraConstraints.HiddenGraph
