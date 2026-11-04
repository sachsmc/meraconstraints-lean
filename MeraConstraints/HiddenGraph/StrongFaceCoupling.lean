import MeraConstraints.HiddenGraph.StrongFaceMeasurability

/-!
# The split evaluation on the original-context and trial-stream space

The common D root receives the independent trial stream, while each other
split root receives its corresponding original root coordinate. Unlike the
constant pointwise encoding, this map keeps the common root's stream separate
from the original context. On the product probability space from
`StrongFaceSupport` it is the concrete encoding whose output law must be
compared with the original model. This chapter establishes measurability;
law equality and independence of the complete encoded family remain separate.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

def encodeReplayStream (x : ReplayCandidate A C D other M)
    (trials : ℕ → ReplayCandidate A C D other M) : ∀ r, replayRootValue A C D other M r
  | .inl none => trials
  | .inl (some k) => ULift.up (x.1 (.inl k))
  | .inr j => ULift.up (x.1 (.inr j))

include h in
noncomputable def coupledReplayEval
    (z : ReplayCandidate A C D other M × (ℕ → ReplayCandidate A C D other M)) : FullAssign val :=
  (replayModel A C D other h M).eval (encodeReplayStream A C D other M z.1 z.2) z.1.2

variable [∀ i, MeasurableSpace (val i)]
  [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

omit [Fintype K] [∀ i, MeasurableSpace (val i)] in
theorem encodeReplayStream_measurable :
    Measurable (fun z : ReplayCandidate A C D other M × (ℕ → ReplayCandidate A C D other M) =>
      encodeReplayStream A C D other M z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro r
  cases r with
  | inl k =>
    cases k with
    | none => exact measurable_snd
    | some k => exact measurable_up.comp ((measurable_pi_apply (Sum.inl k : K ⊕ J)).comp measurable_fst.fst)
  | inr j => exact measurable_up.comp ((measurable_pi_apply (Sum.inr j : K ⊕ J)).comp measurable_fst.fst)

variable [∀ i, MeasurableSingletonClass (val i)] [∀ i, Countable (val i)]

include h in
theorem coupledReplayEval_measurable (hF : RootMechanismsMeasurable A C D other M) :
    Measurable (coupledReplayEval A C D other h M) :=
  (replayModel_eval_measurable A C D other h M hF).comp
    ((encodeReplayStream_measurable A C D other M).prodMk measurable_fst.snd)

end MeraConstraints.HiddenGraph.StrongFaceSplitting
