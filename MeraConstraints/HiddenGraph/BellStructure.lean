import MeraConstraints.HiddenGraph.InequalityStructures
import MeraConstraints.CompactDistrict.BellStructure

/-!
# The Bell type: external parents that reach only one member

This file defines the Bell type of Remark 3 (`prop:ineqstructure`) (ii) for the
districts of a hidden variables DAG (`BellStructure`): members `A` and `B` and
external parents `W_A` and `W_B` such that `W_A` reaches `A` but not `B`, and
`W_B` reaches `B` but not `A`.

The theorems are part of Step 1 of the proof in the Supplementary Materials. For
every profile of response functions, changing only `W_B` does not change the
value of `A` (`bell_eval_A_eq`), and changing only `W_A` does not change the value
of `B` (`bell_eval_B_eq`). These are used in `BellInequalities.lean`.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) (d : DistrictId G)

abbrev BellStructure : Prop :=
  CompactDistrict.BellType G.observed (observedDistrict G) d

variable [DecidableEq (DistrictId G)] (val : Fin n → Type*)
  {wA wB : CompactDistrict.ExternalParent G.observed (observedDistrict G) d}
  {a b : CompactDistrict.Member (observedDistrict G) d}
  (P : CompactDistrict.BellWitness G.observed (observedDistrict G) d wA wB a b)

include P in
/-- The value of `a` is unchanged when only the external parent `wB` is changed. -/
theorem bell_eval_A_eq
    (r : GlobalModel.Profile G.observed val (observedDistrict G) d)
    (e e' : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d)
    (he : ∀ j, j ≠ wB → e j = e' j) :
    CompactDistrict.eval G.observed val (observedDistrict G) d r e a =
      CompactDistrict.eval G.observed val (observedDistrict G) d r e' a :=
  CompactDistrict.eval_eq_of_change_unreached G.observed (observedDistrict G) d val
    r e e' wB a P.not_reach_A he

include P in
/-- The value of `b` is unchanged when only the external parent `wA` is changed. -/
theorem bell_eval_B_eq
    (r : GlobalModel.Profile G.observed val (observedDistrict G) d)
    (e e' : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d)
    (he : ∀ j, j ≠ wA → e j = e' j) :
    CompactDistrict.eval G.observed val (observedDistrict G) d r e b =
      CompactDistrict.eval G.observed val (observedDistrict G) d r e' b :=
  CompactDistrict.eval_eq_of_change_unreached G.observed (observedDistrict G) d val
    r e e' wA b P.not_reach_B he

end MeraConstraints.HiddenGraph
