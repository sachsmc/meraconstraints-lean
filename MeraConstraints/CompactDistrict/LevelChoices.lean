import MeraConstraints.CompactDistrict
import Mathlib.Data.Fintype.EquivFin

/-!
# Choosing levels from the manuscript's categorical-state assumptions

For `prop:ineqstructure`, only district members and external parents must
have at least two levels. Other observed variables need only be nonempty,
so the global reference assignments can be extended to their coordinates.
The chosen assignments are distinct on all relevant coordinates and may
coincide elsewhere. No chosen binary encoding is an input to the graph-level
inequality theorem.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} (G : CausalDAG n) (val : Fin n → Type*)
  (block : Fin n → D) (d : D) [∀ i, Fintype (val i)]

/-- Literal at-least-two-level assumption of `prop:ineqstructure`. -/
def HasTwoLevels : Prop := ∀ i : Fin n,
  block i = d ∨ IsExternalParent G block d i → 2 ≤ Fintype.card (val i)

variable [∀ i, Nonempty (val i)]

theorem exists_reference_levels (hlevels : HasTwoLevels G val block d) :
    ∃ v0 v1 : FullAssign val, ∀ i : Fin n,
      block i = d ∨ IsExternalParent G block d i → v0 i ≠ v1 i := by
  classical
  have hpairs (i : Fin n) : ∃ x y : val i,
      (block i = d ∨ IsExternalParent G block d i) → x ≠ y := by
    by_cases hi : block i = d ∨ IsExternalParent G block d i
    · obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp (hlevels i hi)
      exact ⟨x, y, fun _ => hxy⟩
    · let x := Classical.choice (inferInstance : Nonempty (val i))
      exact ⟨x, x, fun h => False.elim (hi h)⟩
  choose v0 v1 h using hpairs
  exact ⟨v0, v1, h⟩

theorem exists_instrumental_levels (hlevels : HasTwoLevels G val block d)
    (w : ExternalParent G block d) :
    ∃ v0 v1 : FullAssign val, (∀ i : Member block d, v0 i.val ≠ v1 i.val) ∧ v0 w.val ≠ v1 w.val := by
  obtain ⟨v0, v1, h⟩ := exists_reference_levels G val block d hlevels
  exact ⟨v0, v1, fun i => h i.val (Or.inl i.property), h w.val (Or.inr w.property)⟩

end MeraConstraints.CompactDistrict
