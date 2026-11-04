import MeraConstraints.GlobalModel.MoralMarkov
import MeraConstraints.GlobalModel.AncestralMarkov
import MeraConstraints.HiddenGraph.LocalSeparation
import MeraConstraints.Probability.CoordinateJoin

/-!
# Graphical global Markov implies the required local equations

The law in this chapter is arbitrary. Its only Markov hypothesis is the
independence predicate defined by separation in the original ancestral moral
graph. The graph theorem `ancestral_sink_blanket_separated` supplies the
separation; joining the conditioning coordinates gives the literal local
cross-product equation. No positivity is used in this implication.

The global-prefix ancestral set has blanket exactly the manuscript's
cumulative `C_i`. This is proved as a set identity, including parents of
every earlier district member, not just the current member. Consequently
the sufficient `OrderedMarkov` predicate in the existing completeness
theorems follows from the full graphical predicate.
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

/-- Literal identity with the revised manuscript's cumulative conditioning
set, including external parents of all members up to the current vertex. -/
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

/-- Every globally Markov law satisfies the ancestral local equation for
the original district blanket, including zero-probability strata. -/
theorem moralGlobalMarkov_ancestral_equation (p : FullAssign val → ℝ) (hGlobal : MoralGlobalMarkov G val p)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (i : Fin n) (hs : ObservedSink G A i)
    (w : FullAssign val) :
    CondIndependent p (valueEvent val w i) (assignmentEvent val w (A.erase i))
      (assignmentEvent val w (ancestralBlanket G A i)) := by
  let B := ancestralBlanket G A i
  have hci := hGlobal {i} ((A.erase i) \ B) B (ancestral_sink_blanket_separated G A hA i hs)
  have hjoin := coordinateCI_join_conditioning val p {i} ((A.erase i) \ B) B hci
  rw [Finset.sdiff_union_of_subset (ancestralBlanket_subset_erase G A i)] at hjoin
  simpa only [assignmentEvent_singleton] using hjoin w

/-- At c-degree at most one this is the local equation with the actual
induced graph's blanket, not merely the larger original district. -/
theorem moralGlobalMarkov_ancestralLocalMarkov (p : FullAssign val → ℝ)
    (hGlobal : MoralGlobalMarkov G val p) (hdegree : ∀ x, cDegree G x ≤ 1) :
    AncestralLocalMarkov G val p := by
  intro A hA i hs w
  rw [inducedAncestralBlanket_eq G A i hs.1 hdegree]
  exact moralGlobalMarkov_ancestral_equation G val p hGlobal A hA i hs w

/-- The graphical predicate implies exactly the ordered equations required
by the reconstruction theorem. No positivity or c-degree bound is needed
for this direction with the manuscript's original district coordinates. -/
theorem moralGlobalMarkov_orderedMarkov (p : FullAssign val → ℝ)
    (hGlobal : MoralGlobalMarkov G val p) :
    Reconstruction.OrderedMarkov G.observed val (observedDistrict G) p := by
  intro w i
  have h := moralGlobalMarkov_ancestral_equation G val p hGlobal (observedUpto i)
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
