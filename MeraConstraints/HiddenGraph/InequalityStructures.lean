import MeraConstraints.HiddenGraph.Ancestry
import MeraConstraints.CompactDistrict.InstrumentalStructure

/-!
# Inequality-structure paths in the actual hidden graph

These definitions specialize the compact district path and instrumental-type
witness to the actual partition `observedDistrict G`. Reachability stays in
that district after its external source. It implies ordinary observed ancestry;
no converse allowing paths outside the district is asserted.

The appendix's Step 1 dependence theorem is exposed for the actual district
profile and evaluation. These graph and deterministic dependence results do
not require c-degree one. The full nontrivial-inequality construction for
`prop:ineqstructure` remains a subsequent step.
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

/-- Appendix `prop:ineqstructure`, Step 1, with the actual hidden graph's
district members, external parent coordinates and deterministic evaluation. -/
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
