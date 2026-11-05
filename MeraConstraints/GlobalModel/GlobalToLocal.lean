import MeraConstraints.GlobalModel.MoralMarkov
import MeraConstraints.GlobalModel.AncestralMarkov
import MeraConstraints.HiddenGraph.LocalSeparation
import MeraConstraints.Probability.CoordinateJoin

/-!
# The conditional independencies imply the local equations

`GlobalMarkov` is the set of conditional independencies implied by the graph,
defined by separation in the ancestral moral graph (see `GlobalModel.MoralMarkov`).
This chapter shows that any distribution satisfying it also satisfies the ordered
local Markov property used in the proofs of Propositions 1 and 3
(`globalMarkov_orderedMarkov`). No positivity or bound on the c-degree is needed.

The graph theorem `ancestral_sink_blanket_separated` says that a variable with no
children in an ancestral set `A` is separated from the rest of `A` by its blanket.
Joining the conditioning coordinates gives the local independence equation
(`globalMarkov_ancestral_equation`). For the set of variables up to `V_i`, the blanket
is the set `C_i` of Proposition 1, including the external parents of every earlier
member of the district (`observedUpto_blanket`).
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) [DecidableEq (DistrictId G)]

def observedUpto (i : Fin n) : Finset (Fin n) := Finset.univ.filter fun j => j ≤ i

omit [DecidableEq (DistrictId G)] in
theorem observedUpto_ancestral (i : Fin n) : ObservedAncestral G (observedUpto i) := by
  intro j hj k hkj
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (observedAncestor_le G hkj).trans (Finset.mem_filter.mp hj).2⟩

omit [DecidableEq (DistrictId G)] in
theorem observedUpto_sink (i : Fin n) : ObservedSink G (observedUpto i) i := by
  refine ⟨by simp [observedUpto], ?_⟩
  intro j hj hij
  have hji : j ≤ i := (Finset.mem_filter.mp hj).2
  exact (not_lt_of_ge hji) (G.observed.parents_lt hij)

omit [DecidableEq (DistrictId G)] in
theorem observedUpto_erase (i : Fin n) :
    (observedUpto i).erase i = Finset.univ.filter (fun j => j.val < i.val) := by
  ext j
  simp only [observedUpto, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hle⟩
    exact (show j < i from lt_of_le_of_ne hle hne)
  · intro hlt
    have hji : j < i := hlt
    exact ⟨ne_of_lt hji, hji.le⟩

/-- The blanket of `V_i` in the set of variables up to `V_i` is the set `C_i` of
Proposition 1 (`prop:ident`): the earlier members of its district and the external
parents of every member up to `V_i`. -/
theorem observedUpto_blanket (i : Fin n) :
    ancestralBlanket G (observedUpto i) i =
      Reconstruction.conditioningVariables G.observed (observedDistrict G) i := by
  ext j
  simp only [ancestralBlanket, observedUpto, Reconstruction.conditioningVariables,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hji, ⟨hne, hjd⟩ | ⟨hne, k, hki, hkd, hjk⟩⟩
    · exact Or.inl ⟨lt_of_le_of_ne hji hne, hjd⟩
    · exact Or.inr ⟨k, hki, hkd, hjk, hne⟩
  · rintro (⟨hji, hjd⟩ | ⟨k, hki, hkd, hjk, hne⟩)
    · exact ⟨hji.le, Or.inl ⟨ne_of_lt hji, hjd⟩⟩
    · exact ⟨(G.observed.parents_lt hjk).le.trans hki, Or.inr ⟨hne, k, hki, hkd, hjk⟩⟩

end MeraConstraints.HiddenGraph

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Every distribution satisfying `GlobalMarkov` satisfies the local equation on every
ancestral set `A`, with the blanket taken in the original graph. Zero probabilities
are allowed. -/
theorem globalMarkov_ancestral_equation (p : FullAssign val → ℝ) (hGlobal : GlobalMarkov G val p)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (i : Fin n) (hs : ObservedSink G A i)
    (w : FullAssign val) :
    CondIndependent p (valueEvent val w i) (assignmentEvent val w (A.erase i))
      (assignmentEvent val w (ancestralBlanket G A i)) := by
  let B := ancestralBlanket G A i
  have hci := hGlobal {i} ((A.erase i) \ B) B (ancestral_sink_blanket_separated G A hA i hs)
  have hjoin := coordinateCI_join_conditioning val p {i} ((A.erase i) \ B) B hci
  rw [Finset.sdiff_union_of_subset (ancestralBlanket_subset_erase G A i)] at hjoin
  simpa only [assignmentEvent_singleton] using hjoin w

/-- At c-degree at most 1 the blanket may be taken in the subgraph induced by `A`:
`GlobalMarkov` implies `AncestralLocalMarkov`. -/
theorem globalMarkov_ancestralLocalMarkov (p : FullAssign val → ℝ)
    (hGlobal : GlobalMarkov G val p) (hdegree : ∀ x, cDegree G x ≤ 1) :
    AncestralLocalMarkov G val p := by
  intro A hA i hs w
  rw [inducedAncestralBlanket_eq G A i hs.1 hdegree]
  exact globalMarkov_ancestral_equation G val p hGlobal A hA i hs w

/-- `GlobalMarkov` implies the ordered local Markov property. No positivity or c-degree
bound is needed. -/
theorem globalMarkov_orderedMarkov (p : FullAssign val → ℝ)
    (hGlobal : GlobalMarkov G val p) :
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p := by
  intro w i
  have h := globalMarkov_ancestral_equation G val p hGlobal (observedUpto i)
    (observedUpto_ancestral G i) i (observedUpto_sink G i) w
  have hR : assignmentEvent val w ((observedUpto i).erase i) = prefixEvent val w i.val := by
    rw [observedUpto_erase, ← prefixEvent_eq_assignmentEvent]
  have hB : assignmentEvent val w (ancestralBlanket G (observedUpto i) i) =
      Reconstruction.conditioningEvent G.observed val (observedDistrict G) w i := by
    rw [observedUpto_blanket]
    rfl
  rw [hR, hB] at h
  exact h

end MeraConstraints.GlobalModel.KernelReconstruction
