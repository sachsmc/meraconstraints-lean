import MeraConstraints.HiddenGraph.InequalityStructures
import MeraConstraints.CompactDistrict.BellStructure

/-!
# Bell geometry for the actual hidden-graph district

The Bell hypothesis of `prop:ineqstructure` (ii) is specialized to
`observedDistrict G`. The generic path geometry therefore applies to the
actual graph partition. Appendix Step 1 also proves that changing W_B alone
cannot change A, and changing W_A alone cannot change B, for every profile.
These deterministic statements prepare the subsequent CHSH obstruction.
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
/-- The actual A evaluation is unchanged when only the opposite input varies. -/
theorem bell_eval_A_eq
    (r : GlobalModel.Profile G.observed val (observedDistrict G) d)
    (e e' : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d)
    (he : ∀ j, j ≠ wB → e j = e' j) :
    CompactDistrict.eval G.observed val (observedDistrict G) d r e a =
      CompactDistrict.eval G.observed val (observedDistrict G) d r e' a :=
  CompactDistrict.eval_eq_of_change_unreached G.observed (observedDistrict G) d val
    r e e' wB a P.not_reach_A he

include P in
/-- The actual B evaluation is unchanged when only the opposite input varies. -/
theorem bell_eval_B_eq
    (r : GlobalModel.Profile G.observed val (observedDistrict G) d)
    (e e' : CompactDistrict.ExternalAssign G.observed val (observedDistrict G) d)
    (he : ∀ j, j ≠ wA → e j = e' j) :
    CompactDistrict.eval G.observed val (observedDistrict G) d r e b =
      CompactDistrict.eval G.observed val (observedDistrict G) d r e' b :=
  CompactDistrict.eval_eq_of_change_unreached G.observed (observedDistrict G) d val
    r e e' wA b P.not_reach_B he

end MeraConstraints.HiddenGraph
