import MeraConstraints.HiddenGraph.StrongFaceReplay
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# The first accepted trial: partition and measurability

`firstReplay`, defined with the split model of Proposition 6 (`prop:strong`),
returns the first trial of a sequence that lies in an acceptance set `S`, or trial
zero if there is none. This chapter writes the event "the first accepted trial lies
in `B`" as a disjoint union of the events `firstHit n`, and uses this to show that
`firstReplay` is measurable. No independence or probability assumption is used, and
the trials take values in an arbitrary measurable space.
-/

namespace MeraConstraints.Replay

open MeasureTheory Set
open HiddenGraph.StrongFaceSplitting (firstReplay)

variable {Ω T : Type*} (X : ℕ → Ω → T) (S B : Set T)

/-- The trials before `n` lie outside `S`, and trial `n` lies in `S ∩ B`. -/
def firstHit (n : ℕ) : Set Ω :=
  ⋂ j ∈ insert n (Finset.range n), X j ⁻¹' (if j = n then S ∩ B else Sᶜ)

theorem mem_firstHit (n : ℕ) (ω : Ω) :
    ω ∈ firstHit X S B n ↔ X n ω ∈ S ∧ X n ω ∈ B ∧ ∀ j < n, X j ω ∉ S := by
  simp only [firstHit, mem_iInter, mem_preimage]
  constructor
  · intro h
    have hn : X n ω ∈ S ∩ B := by simpa using h n (Finset.mem_insert_self _ _)
    refine ⟨hn.1, hn.2, ?_⟩
    intro j hj
    have hj' := h j (Finset.mem_insert_of_mem (Finset.mem_range.mpr hj))
    simpa only [if_neg (ne_of_lt hj), mem_compl_iff] using hj'
  · rintro ⟨hs, hb, hprior⟩ j hj
    by_cases hjn : j = n
    · subst j
      simpa using (⟨hs, hb⟩ : X n ω ∈ S ∩ B)
    · have hjn' : j < n := Finset.mem_range.mp ((Finset.mem_insert.mp hj).resolve_left hjn)
      simpa only [if_neg hjn, mem_compl_iff] using hprior j hjn'

theorem firstHit_pairwise_disjoint :
    Pairwise (fun m n => Disjoint (firstHit X S B m) (firstHit X S B n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro ω hm hn
  obtain ⟨hmS, _, hmPrior⟩ := (mem_firstHit X S B m ω).mp hm
  obtain ⟨hnS, _, hnPrior⟩ := (mem_firstHit X S B n ω).mp hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hnPrior m hlt hmS
  · exact hmPrior n hgt hnS

theorem mem_selected_iff (ω : Ω) (hs : ∃ n, X n ω ∈ S) :
    firstReplay (fun n => X n ω) (· ∈ S) ∈ B ↔ ∃ n, ω ∈ firstHit X S B n := by
  classical
  constructor
  · intro hb
    refine ⟨Nat.find hs, (mem_firstHit X S B _ ω).mpr ⟨Nat.find_spec hs, ?_, ?_⟩⟩
    · simpa only [firstReplay, dif_pos hs] using hb
    · intro j hj
      exact Nat.find_min hs hj
  · rintro ⟨n, hn⟩
    obtain ⟨hnS, hnB, hprior⟩ := (mem_firstHit X S B n ω).mp hn
    have heq : Nat.find hs = n := (Nat.find_eq_iff hs).mpr ⟨hnS, hprior⟩
    simpa only [firstReplay, dif_pos hs, heq] using hnB

theorem success_eq_union : {ω | ∃ n, X n ω ∈ S} = ⋃ n, firstHit X S Set.univ n := by
  ext ω
  simp only [mem_setOf_eq, mem_iUnion]
  constructor
  · intro hs
    exact (mem_selected_iff X S Set.univ ω hs).mp (Set.mem_univ _)
  · rintro ⟨n, hn⟩
    exact ⟨n, ((mem_firstHit X S Set.univ n ω).mp hn).1⟩

theorem selected_preimage :
    (fun ω => firstReplay (fun n => X n ω) (· ∈ S)) ⁻¹' B =
      (⋃ n, firstHit X S B n) ∪ ({ω | ¬ ∃ n, X n ω ∈ S} ∩ X 0 ⁻¹' B) := by
  classical
  ext ω
  by_cases hs : ∃ n, X n ω ∈ S
  · simpa only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_setOf_eq,
      not_true_eq_false, hs, false_and, or_false] using mem_selected_iff X S B ω hs
  · simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    have hnone : ¬ ∃ n, ω ∈ firstHit X S B n := by
      rintro ⟨n, hn⟩
      exact hs ⟨n, ((mem_firstHit X S B n ω).mp hn).1⟩
    simp only [firstReplay, hnone, false_or, hs, not_false_eq_true, true_and, dite_false]

variable [MeasurableSpace Ω] [MeasurableSpace T]

theorem firstHit_measurable (hX : ∀ n, Measurable (X n)) (hS : MeasurableSet S)
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (firstHit X S B n) := by
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  by_cases hj : j = n
  · simpa only [if_pos hj] using (hS.inter hB).preimage (hX j)
  · simpa only [if_neg hj] using hS.compl.preimage (hX j)

theorem success_measurable (hX : ∀ n, Measurable (X n)) (hS : MeasurableSet S) :
    MeasurableSet {ω | ∃ n, X n ω ∈ S} := by
  rw [success_eq_union X S]
  exact MeasurableSet.iUnion fun n => firstHit_measurable X S Set.univ hX hS MeasurableSet.univ n

/-- `firstReplay` is measurable, including when no trial is accepted. -/
theorem firstReplay_measurable (hX : ∀ n, Measurable (X n)) (hS : MeasurableSet S) :
    Measurable (fun ω => firstReplay (fun n => X n ω) (· ∈ S)) := by
  intro B hB
  rw [selected_preimage X S B]
  exact (MeasurableSet.iUnion fun n => firstHit_measurable X S B hX hS hB n).union
    ((success_measurable X S hX hS).compl.inter (hB.preimage (hX 0)))

end MeraConstraints.Replay
