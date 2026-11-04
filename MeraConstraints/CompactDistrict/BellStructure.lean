import MeraConstraints.CompactDistrict.Reachability

/-!
# Bell-type paths and their separation

Manuscript `prop:ineqstructure` (ii) assumes that W_A reaches A but not B,
and W_B reaches B but not A, always through the selected district. The
appendix chooses two paths and asserts that their member vertices are
disjoint. We check that assertion by extending a reaching path along the
suffix of either chosen path. A common member would make W_A reach B.

The source and endpoint inequalities and opposite-endpoint exclusions are
consequences, not extra hypotheses. Direct source-to-member edges are allowed.
These are graph facts; state cardinalities, c-degree and probability laws
enter the subsequent lifted Bell construction.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*}

namespace MemberPath

variable {G : CausalDAG n} {block : Fin n → D} {d : D} {w v : Fin n}

/-- Every member on a chosen path is reached by its source. -/
theorem reaches_vertex (p : MemberPath G block d w v) {i : Fin n}
    (hi : i ∈ p.vertices) : Reaches G block d w i := by
  induction p with
  | direct hv hwv =>
    have h := Finset.mem_singleton.mp hi
    subst i
    exact ⟨.direct hv hwv⟩
  | tail initial hv hiv ih =>
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact ⟨.tail initial hv hiv⟩
    · exact ih hi

/-- Splice a reaching path at any member, then follow the chosen suffix.
The resulting path still stays in the selected district after its source. -/
theorem reaches_endpoint (p : MemberPath G block d w v) {z i : Fin n}
    (hi : i ∈ p.vertices) (hz : Reaches G block d z i) : Reaches G block d z v := by
  induction p with
  | direct _ _ =>
    have h := Finset.mem_singleton.mp hi
    subst i
    exact hz
  | tail initial hv hiv ih =>
    obtain rfl | hi := Finset.mem_insert.mp hi
    · exact hz
    · exact reaches_tail G block d (ih hi) hv hiv

end MemberPath

variable (G : CausalDAG n) (block : Fin n → D) (d : D)

/-- Literal Bell-type graph hypothesis, with the two chosen district paths.
No-cross reachability uses all permitted district paths, not just these two. -/
structure BellWitness (wA wB : ExternalParent G block d) (a b : Member block d) where
  pathA : MemberPath G block d wA.val a.val
  pathB : MemberPath G block d wB.val b.val
  not_reach_B : ¬ Reaches G block d wA.val b.val
  not_reach_A : ¬ Reaches G block d wB.val a.val

def BellType : Prop :=
  ∃ wA wB : ExternalParent G block d, ∃ a b : Member block d,
    Nonempty (BellWitness G block d wA wB a b)

namespace BellWitness

variable {G block d} {wA wB : ExternalParent G block d} {a b : Member block d}
  (P : BellWitness G block d wA wB a b)

def intermediatesA : Finset (Fin n) := P.pathA.vertices.erase a.val
def intermediatesB : Finset (Fin n) := P.pathB.vertices.erase b.val

include P in
theorem sources_ne : wA ≠ wB := by
  intro h
  exact P.not_reach_A (h ▸ Nonempty.intro P.pathA)

include P in
theorem endpoints_ne : a ≠ b := by
  intro h
  exact P.not_reach_B (h ▸ Nonempty.intro P.pathA)

theorem sourceA_not_reach_pathB {i : Fin n} (hi : i ∈ P.pathB.vertices) :
    ¬ Reaches G block d wA.val i := fun h => P.not_reach_B (P.pathB.reaches_endpoint hi h)

theorem sourceB_not_reach_pathA {i : Fin n} (hi : i ∈ P.pathA.vertices) :
    ¬ Reaches G block d wB.val i := fun h => P.not_reach_A (P.pathA.reaches_endpoint hi h)

theorem paths_disjoint : Disjoint P.pathA.vertices P.pathB.vertices := by
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  exact P.sourceA_not_reach_pathB hiB (P.pathA.reaches_vertex hiA)

theorem endpointB_not_pathA : b.val ∉ P.pathA.vertices := by
  intro h
  exact P.not_reach_B (P.pathA.reaches_vertex h)

theorem endpointA_not_pathB : a.val ∉ P.pathB.vertices := by
  intro h
  exact P.not_reach_A (P.pathB.reaches_vertex h)

theorem intermediates_disjoint : Disjoint P.intermediatesA P.intermediatesB := by
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  exact Finset.disjoint_left.mp P.paths_disjoint
    (Finset.mem_erase.mp hiA).2 (Finset.mem_erase.mp hiB).2

/-- Direct paths still require the full no-cross-path hypotheses: absence
of a cross edge alone would not exclude an indirect district path. -/
def direct (hwa : wA.val ∈ G.parents a.val) (hwb : wB.val ∈ G.parents b.val)
    (hAB : ¬ Reaches G block d wA.val b.val)
    (hBA : ¬ Reaches G block d wB.val a.val) : BellWitness G block d wA wB a b where
  pathA := .direct a.property hwa
  pathB := .direct b.property hwb
  not_reach_B := hAB
  not_reach_A := hBA

theorem direct_intermediates (hwa : wA.val ∈ G.parents a.val) (hwb : wB.val ∈ G.parents b.val)
    (hAB : ¬ Reaches G block d wA.val b.val) (hBA : ¬ Reaches G block d wB.val a.val) :
    (direct hwa hwb hAB hBA).intermediatesA = ∅ ∧
      (direct hwa hwb hAB hBA).intermediatesB = ∅ := by
  simp [direct, intermediatesA, intermediatesB, MemberPath.vertices]

end BellWitness

end MeraConstraints.CompactDistrict
