import MeraConstraints.CompactDistrict.Reachability

/-!
# The instrumental-type path and its exclusion obstruction

Manuscript `prop:ineqstructure` (i) gives a path from an external parent W to
a member A, an edge A to B, and excludes every other vertex of that path
from the parents of B. The witness below includes W in that exclusion. Its
member path includes A, so intermediate vertices are defined explicitly by
erasing A. Direct W-to-A paths are permitted.

The DAG order proves B is not on the path. If two compact rows differ only
in W, intermediate-path values and B, then they give identical parent values
to B. Consequently a single profile cannot produce different B values in
those rows. This checks the deterministic contradiction in the appendix's
instrumental argument; constructing its affine 0/1 witness and separating
the district polytope remain subsequent steps.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} (G : CausalDAG n) (block : Fin n → D) (d : D)

/-- Literal graph hypothesis of instrumental type, with an explicit path.
State-space assumptions belong to the later witness construction. -/
structure InstrumentalWitness (w : ExternalParent G block d) (a b : Member block d) where
  path : MemberPath G block d w.val a.val
  treatment_parent : a.val ∈ G.parents b.val
  exclusion : ∀ i ∈ insert w.val path.vertices, i ≠ a.val → i ∉ G.parents b.val

def InstrumentalType : Prop :=
  ∃ w : ExternalParent G block d, ∃ a b : Member block d, Nonempty (InstrumentalWitness G block d w a b)

namespace InstrumentalWitness

variable {G block d} {w : ExternalParent G block d} {a b : Member block d}
  (P : InstrumentalWitness G block d w a b)

def intermediates : Finset (Fin n) := P.path.vertices.erase a.val

/-- The usual direct instrument-to-treatment edge is the case with no
intermediate members; it satisfies precisely the same exclusion condition. -/
def direct (hwa : w.val ∈ G.parents a.val) (hab : a.val ∈ G.parents b.val)
    (hwb : w.val ∉ G.parents b.val) : InstrumentalWitness G block d w a b where
  path := .direct a.property hwa
  treatment_parent := hab
  exclusion := by
    intro i hi hia
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact hwb
    · exact False.elim (hia (Finset.mem_singleton.mp hi))

theorem direct_intermediates (hwa : w.val ∈ G.parents a.val) (hab : a.val ∈ G.parents b.val)
    (hwb : w.val ∉ G.parents b.val) : (direct hwa hab hwb).intermediates = ∅ := by
  simp [direct, intermediates, MemberPath.vertices]

include P in
theorem treatment_lt_outcome : a.val < b.val := G.parents_lt P.treatment_parent

theorem outcome_not_on_path : b.val ∉ P.path.vertices := P.path.next_not_mem P.treatment_parent

theorem instrument_not_on_path : w.val ∉ P.path.vertices := by
  intro hw
  exact w.property.1 (P.path.vertices_member hw)

include P in
theorem instrument_not_parent : w.val ∉ G.parents b.val := by
  apply P.exclusion w.val (Finset.mem_insert_self _ _)
  intro hwa
  apply w.property.1
  exact (congrArg block hwa).trans a.property

theorem intermediate_not_parent {i : Fin n} (hi : i ∈ P.intermediates) : i ∉ G.parents b.val := by
  obtain ⟨hia, hip⟩ := Finset.mem_erase.mp hi
  exact P.exclusion i (Finset.mem_insert_of_mem hip) hia

theorem intermediate_member {i : Fin n} (hi : i ∈ P.intermediates) : block i = d :=
  P.path.vertices_member (Finset.mem_erase.mp hi).2

theorem treatment_not_intermediate : a.val ∉ P.intermediates := Finset.notMem_erase _ _

theorem outcome_not_intermediate : b.val ∉ P.intermediates :=
  fun hb => P.outcome_not_on_path (Finset.mem_erase.mp hb).2

variable [DecidableEq D] (val : Fin n → Type*)

/-- Under the appendix's proposed instrumental witness, varying the copied
intermediate vertices and W cannot change any permitted argument of B. -/
theorem parentAssign_eq (x x' : MemberAssign val block d) (e e' : ExternalAssign G val block d)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j)
    (hx : ∀ i : Member block d, i.val ∉ insert b.val P.intermediates → x i = x' i) :
    CompactDistrict.parentAssign G val block d (x, e) b =
      CompactDistrict.parentAssign G val block d (x', e') b := by
  funext j
  by_cases hj : block j = d
  · simp only [CompactDistrict.parentAssign, dif_pos hj]
    apply hx ⟨j, hj⟩
    intro hm
    obtain hjb | hji := Finset.mem_insert.mp hm
    · exact (ne_of_lt (G.parents_lt j.property)) hjb
    · exact P.intermediate_not_parent hji j.property
  · simp only [CompactDistrict.parentAssign, dif_neg hj]
    apply he ⟨j, hj, ⟨b, b.property, j.property⟩⟩
    intro hje
    apply P.instrument_not_parent
    have hv : j.val = w.val := congrArg Subtype.val hje
    simpa only [hv] using j.property

/-- The B mechanism is a function of its permitted parents in each profile. -/
theorem outcome_eq_of_compatible (r : GlobalModel.Profile G val block d)
    (x x' : MemberAssign val block d) (e e' : ExternalAssign G val block d)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j)
    (hx : ∀ i : Member block d, i.val ∉ insert b.val P.intermediates → x i = x' i)
    (hr : Compatible G val block d (x, e) r) (hr' : Compatible G val block d (x', e') r) :
    x b = x' b := by
  have h := hr b
  rw [P.parentAssign_eq val x x' e e' he hx] at h
  exact h.symm.trans (hr' b)

/-- Core instrumental obstruction: the two proposed deterministic blocks
cannot be columns of the same response profile if B changes. -/
theorem not_both_compatible (x x' : MemberAssign val block d) (e e' : ExternalAssign G val block d)
    (he : ∀ j : ExternalParent G block d, j ≠ w → e j = e' j)
    (hx : ∀ i : Member block d, i.val ∉ insert b.val P.intermediates → x i = x' i)
    (hb : x b ≠ x' b) :
    ¬ ∃ r : GlobalModel.Profile G val block d,
      Compatible G val block d (x, e) r ∧ Compatible G val block d (x', e') r := by
  rintro ⟨r, hr, hr'⟩
  exact hb (P.outcome_eq_of_compatible val r x x' e e' he hx hr hr')

end InstrumentalWitness
end MeraConstraints.CompactDistrict
