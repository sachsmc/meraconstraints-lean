import MeraConstraints.CompactDistrict.PathCopying

/-!
# Instrumental path-copying profiles on arbitrary state spaces

Appendix `prop:ineqstructure` (i): choose values called zero and one at each
member. At an external input e write ζ for the indicator that W is at its
chosen one value. Intermediate path members copy ζ through listed parents.
The treatment A applies a binary function f to its path input; B applies a
binary function g to its parent A. Every other member is zero.

Two full assignments provide the chosen values. Distinctness is required
only at district members here; the one/zero values at W must be distinct only
when the later incompatibility argument needs both external input blocks.
Values outside the relevant coordinates can coincide. No binary-only state
space or finiteness premise is used in the deterministic evaluation theorem.
-/

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} {D : Type*} [DecidableEq D]
  {G : CausalDAG n} {block : Fin n → D} {d : D} {val : Fin n → Type*}

namespace BinaryValues

def encode (v0 v1 : FullAssign val) (i : Fin n) (z : Bool) : val i := if z then v1 i else v0 i

noncomputable def decode (v1 : FullAssign val) (i : Fin n) (x : val i) : Bool := by
  classical
  exact if x = v1 i then true else false

theorem decode_encode (v0 v1 : FullAssign val) (i : Fin n) (hi : v0 i ≠ v1 i) (z : Bool) :
    decode v1 i (encode v0 v1 i z) = z := by
  cases z <;> simp [encode, decode, hi]

end BinaryValues

namespace InstrumentalWitness

variable {w : ExternalParent G block d} {a b : Member block d}
  (P : InstrumentalWitness G block d w a b) (v0 v1 : FullAssign val)

noncomputable def sourceBit (e : ExternalAssign G val block d) : Bool := BinaryValues.decode v1 w.val (e w)

/-- Explicit member assignment: only intermediate vertices copy z; A and B
have the separately specified values x and y. -/
def binaryAssignment (z x y : Bool) : MemberAssign val block d :=
  fun i => if i = a then BinaryValues.encode v0 v1 i.val x else
    if i = b then BinaryValues.encode v0 v1 i.val y else
      if i.val ∈ P.intermediates then BinaryValues.encode v0 v1 i.val z else v0 i.val

noncomputable def copyingProfile (f g : Bool → Bool) : GlobalModel.Profile G val block d := by
  classical
  intro i pa
  by_cases hib : i = b
  · subst i
    exact BinaryValues.encode v0 v1 b.val
      (g (BinaryValues.decode v1 a.val (pa ⟨a.val, P.treatment_parent⟩)))
  · exact if hi : i.val ∈ P.path.vertices then
      let j := P.path.copyParent i.val hi
      let z := BinaryValues.decode v1 j (pa ⟨j, P.path.copyParent_mem i.val hi⟩)
      BinaryValues.encode v0 v1 i.val (if i = a then f z else z)
    else v0 i.val

omit [DecidableEq D] in
theorem binaryAssignment_at_treatment (z x y : Bool) : P.binaryAssignment v0 v1 z x y a =
    BinaryValues.encode v0 v1 a.val x := by simp [binaryAssignment]

omit [DecidableEq D] in
theorem binaryAssignment_at_outcome (z x y : Bool) : P.binaryAssignment v0 v1 z x y b =
    BinaryValues.encode v0 v1 b.val y := by
  have hba : b ≠ a := fun h => (ne_of_lt P.treatment_lt_outcome) (congrArg Subtype.val h).symm
  simp [binaryAssignment, hba]

omit [DecidableEq D] in
theorem binaryAssignment_at_intermediate (z x y : Bool) (i : Member block d) (hi : i.val ∈ P.intermediates) :
    P.binaryAssignment v0 v1 z x y i = BinaryValues.encode v0 v1 i.val z := by
  have hia : i ≠ a := fun h => P.treatment_not_intermediate (h ▸ hi)
  have hib : i ≠ b := fun h => P.outcome_not_intermediate (h ▸ hi)
  simp [binaryAssignment, hia, hib, hi]

/-- Reading the selected parent from the explicit assignment recovers ζ.
Every parent used here is an actual observed parent of the copying member. -/
theorem read_copyParent (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (e : ExternalAssign G val block d) (x y : Bool) (i : Member block d) (hi : i.val ∈ P.path.vertices) :
    BinaryValues.decode v1 (P.path.copyParent i.val hi)
      (CompactDistrict.parentAssign G val block d (P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e) x y, e) i
        ⟨P.path.copyParent i.val hi, P.path.copyParent_mem i.val hi⟩) = sourceBit (w := w) v1 e := by
  let j := P.path.copyParent i.val hi
  have hji : j ∈ G.parents i.val := P.path.copyParent_mem i.val hi
  have hja : j ≠ a.val := ne_of_lt (P.path.copyParent_lt_terminal i.val hi)
  obtain hjw | hjp := P.path.copyParent_source_or_path i.val hi
  · change j = w.val at hjw
    change BinaryValues.decode v1 j
      (CompactDistrict.parentAssign G val block d (P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e) x y, e) i ⟨j, hji⟩) = _
    have hjout : block j ≠ d := by
      intro h
      apply w.property.1
      simpa only [hjw] using h
    simp only [CompactDistrict.parentAssign, dif_neg hjout]
    exact congrArg (fun k : ExternalParent G block d => BinaryValues.decode v1 k.val (e k))
      (show (⟨j, hjout, ⟨i, i.property, hji⟩⟩ : ExternalParent G block d) = w from Subtype.ext hjw)
  · have hjm : block j = d := P.path.vertices_member hjp
    have hmid : j ∈ P.intermediates := Finset.mem_erase.mpr ⟨hja, hjp⟩
    change BinaryValues.decode v1 j
      (CompactDistrict.parentAssign G val block d (P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e) x y, e) i ⟨j, hji⟩) = _
    simp only [CompactDistrict.parentAssign, dif_pos hjm]
    rw [P.binaryAssignment_at_intermediate v0 v1 _ x y ⟨j, hjm⟩ hmid]
    exact BinaryValues.decode_encode v0 v1 j (hlevels ⟨j, hjm⟩) _

/-- Actual compact profile evaluation of every constructed copying profile. -/
theorem eval_copyingProfile (hlevels : ∀ i : Member block d, v0 i.val ≠ v1 i.val)
    (f g : Bool → Bool) (e : ExternalAssign G val block d) :
    eval G val block d (P.copyingProfile v0 v1 f g) e =
      P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e) (f (sourceBit (w := w) v1 e)) (g (f (sourceBit (w := w) v1 e))) := by
  classical
  apply (eval_eq_iff_compatible G val block d
    (P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e)
      (f (sourceBit (w := w) v1 e)) (g (f (sourceBit (w := w) v1 e))), e)
    (P.copyingProfile v0 v1 f g)).mpr
  intro i
  by_cases hib : i = b
  · subst i
    simp only [copyingProfile, dite_true]
    have hpa : CompactDistrict.parentAssign G val block d
        (P.binaryAssignment v0 v1 (sourceBit (w := w) v1 e) (f (sourceBit (w := w) v1 e)) (g (f (sourceBit (w := w) v1 e))), e) b
          ⟨a.val, P.treatment_parent⟩ = BinaryValues.encode v0 v1 a.val (f (sourceBit (w := w) v1 e)) := by
      simp only [CompactDistrict.parentAssign, dif_pos a.property]
      exact P.binaryAssignment_at_treatment v0 v1 _ _ _
    rw [hpa, BinaryValues.decode_encode v0 v1 a.val (hlevels a), P.binaryAssignment_at_outcome]
  · simp only [copyingProfile, dif_neg hib]
    by_cases hi : i.val ∈ P.path.vertices
    · simp only [dif_pos hi]
      rw [P.read_copyParent v0 v1 hlevels e]
      by_cases hia : i = a
      · subst i
        simp only [ite_true, P.binaryAssignment_at_treatment]
      · have hmid : i.val ∈ P.intermediates := Finset.mem_erase.mpr
          ⟨fun h => hia (Subtype.ext h), hi⟩
        simp only [if_neg hia, P.binaryAssignment_at_intermediate v0 v1 _ _ _ i hmid]
    · simp only [dif_neg hi]
      have hia : i ≠ a := fun h => hi (h.symm ▸ P.path.endpoint_mem)
      have hmid : i.val ∉ P.intermediates := fun hm => hi (Finset.mem_erase.mp hm).2
      simp only [binaryAssignment, if_neg hia, if_neg hib, if_neg hmid]

end InstrumentalWitness
end MeraConstraints.CompactDistrict
