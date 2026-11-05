import MeraConstraints.Probability.ReplayTrials
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Replay with an acceptance set that depends on a context

In the split model the set of accepted candidates depends on the observed values
of `C` and their parents, which play the role of a context. Here an acceptance
event `E` is a measurable subset of `Context × Candidate`; `acceptanceFiber E c` is
the set of candidates accepted at context `c`. `contextReplay E (c, trials)` is the
first trial accepted at `c`, with the same fallback as `firstReplay`.

The main result is that `contextReplay E` is measurable as a function of the context
and the stream together (`contextReplay_measurable`), not only for each fixed
context. The proof attaches the context to every trial and applies
`firstReplay_measurable` on the product space. Neither space is assumed finite or
countable.
-/

namespace MeraConstraints.Replay

open MeasureTheory Set
open HiddenGraph.StrongFaceSplitting (firstReplay firstReplay_accept)

variable {C T : Type*}

theorem firstReplay_pair (c : C) (trials : ℕ → T) (P : C × T → Prop) :
    firstReplay (fun n => (c, trials n)) P =
      (c, firstReplay trials (fun x => P (c, x))) := by
  classical
  by_cases h : ∃ n, P (c, trials n)
  · simp only [firstReplay, dif_pos h]
  · simp only [firstReplay, dif_neg h]

def acceptanceFiber (E : Set (C × T)) (c : C) : Set T := Prod.mk c ⁻¹' E

noncomputable def contextReplay (E : Set (C × T)) (z : C × (ℕ → T)) : T :=
  firstReplay z.2 (fun x => (z.1, x) ∈ E)

noncomputable def contextJoint (E : Set (C × T)) (z : C × (ℕ → T)) : C × T :=
  (z.1, contextReplay E z)

theorem contextReplay_accept (E : Set (C × T)) (z : C × (ℕ → T))
    (hz : ∃ n, (z.1, z.2 n) ∈ E) : (z.1, contextReplay E z) ∈ E :=
  firstReplay_accept z.2 (fun x => (z.1, x) ∈ E) hz

variable [MeasurableSpace C] [MeasurableSpace T]

theorem acceptanceFiber_measurable (E : Set (C × T)) (hE : MeasurableSet E) (c : C) :
    MeasurableSet (acceptanceFiber E c) :=
  hE.preimage (measurable_const.prodMk measurable_id)

/-- The replayed candidate is a measurable function of the context and the stream
together. It need not be the case that some trial is accepted. -/
theorem contextReplay_measurable (E : Set (C × T)) (hE : MeasurableSet E) :
    Measurable (contextReplay E) := by
  have hX (n : ℕ) : Measurable (fun z : C × (ℕ → T) => (z.1, z.2 n)) :=
    measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd)
  have h := measurable_snd.comp (firstReplay_measurable
    (fun n (z : C × (ℕ → T)) => (z.1, z.2 n)) E hX hE)
  change Measurable (fun z : C × (ℕ → T) => firstReplay z.2 (fun x => (z.1, x) ∈ E))
  simpa only [Function.comp_def, firstReplay_pair] using h

theorem contextJoint_measurable (E : Set (C × T)) (hE : MeasurableSet E) :
    Measurable (contextJoint E) :=
  measurable_fst.prodMk (contextReplay_measurable E hE)

theorem contextReplay_success_measurable (E : Set (C × T)) (hE : MeasurableSet E) :
    MeasurableSet {z : C × (ℕ → T) | ∃ n, (z.1, z.2 n) ∈ E} := by
  have heq : {z : C × (ℕ → T) | ∃ n, (z.1, z.2 n) ∈ E} =
      ⋃ n, (fun z : C × (ℕ → T) => (z.1, z.2 n)) ⁻¹' E := by ext z; simp
  rw [heq]
  exact MeasurableSet.iUnion fun n => hE.preimage
    (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd))

/-- If the context and the stream are measurable functions of a point `ω`, so is
the replayed candidate. -/
theorem contextReplay_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (E : Set (C × T)) (hE : MeasurableSet E) (Z : Ω → C) (W : Ω → ℕ → T)
    (hZ : Measurable Z) (hW : Measurable W) :
    Measurable (fun ω => contextReplay E (Z ω, W ω)) :=
  (contextReplay_measurable E hE).comp (hZ.prodMk hW)

end MeraConstraints.Replay
