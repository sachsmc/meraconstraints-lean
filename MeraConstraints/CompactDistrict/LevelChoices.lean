import MeraConstraints.CompactDistrict
import Mathlib.Data.Fintype.EquivFin

/-!
# Two levels for each member and external parent

Remark 3 (`prop:ineqstructure`) assumes that the members and external parents of the
district each have at least two levels (`HasTwoLevels`). The proof labels two values
of each of them `0` and `1`, and chooses the values `w⁰ ≠ w¹` of an external parent.
Here those choices are made: there are two complete assignments that differ at every
member and external parent (`exists_reference_levels`). The other observed variables
need only be nonempty, and the two assignments may agree there.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} (G : CausalDAG n) (val : Fin n → Type*)
  (block : Fin n → D) (d : D) [∀ i, Fintype (val i)]

/-- Every member and external parent of the district has at least two levels. -/
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
