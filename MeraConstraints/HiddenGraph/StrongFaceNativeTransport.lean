import MeraConstraints.HiddenGraph.RootProbabilityModel
import MeraConstraints.HiddenGraph.StrongFaceLaw

/-!
# The inputs of the split model on its own input types

The preceding chapters describe the inputs through `ULift` wrappers, which only
change the Lean types of values. Here measurable maps convert them to the input
types of `replayModel` (`rootValue` and `privateNoise`). `replayNativeEncode` takes
original inputs and a stream to the inputs of `replayModel`, and
`replayNativeEncode_independent` shows that these inputs are mutually independent
under the product of `ν` and the law of the stream. This supplies the independence
field of the `RootProbabilityModel` in `Completeness.StrongFaceSplitting`.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe u

variable {n : ℕ} {K J : Type u} [Fintype K] [Fintype J]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type u} (M : RootSCM.{u,u,u,u} (originalGraph A C D other) val)

def liftOriginalInput (t : (K ⊕ J) ⊕ Fin n) : M.InputValue t → ReplayInputValue A C D other M t := by
  cases t <;> exact ULift.up

include h in
def replayNativeEncode (z : M.NativeInputs × (ℕ → M.NativeInputs)) :
    (replayModel A C D other h M).NativeInputs :=
  (encodeReplayStream A C D other M z.1 z.2, z.1.2)

include h in
def decodeReplayInput (t : (Option K ⊕ J) ⊕ Fin n) :
    StreamInputValue A C D other M (splitInputIndex t) → (replayModel A C D other h M).InputValue t := by
  cases t with
  | inl r => cases r with
    | inl k => cases k <;> exact id
    | inr j => exact id
  | inr i => exact ULift.down

variable [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

omit [Fintype K] [Fintype J] in
theorem liftOriginalInput_measurable (t : (K ⊕ J) ⊕ Fin n) :
    Measurable (liftOriginalInput A C D other M t) := by
  cases t <;> exact measurable_up

omit [Fintype K] [Fintype J] in
theorem replayInput_independent_native (ν : Measure M.NativeInputs)
    (hInd : iIndepFun (fun t x => M.input x t) ν) :
    iIndepFun (fun t x => replayInput A C D other M x t) ν := by
  have hi := hInd.comp (liftOriginalInput A C D other M) (liftOriginalInput_measurable A C D other M)
  apply hi.congr
  intro t
  filter_upwards [] with x
  cases t <;> rfl

include h in
omit [Fintype J] in
theorem replayNativeEncode_measurable : Measurable (replayNativeEncode A C D other h M) :=
  (encodeReplayStream_measurable A C D other M).prodMk measurable_fst.snd

include h in
omit [Fintype J] in
theorem decodeReplayInput_measurable (t : (Option K ⊕ J) ⊕ Fin n) :
    Measurable (decodeReplayInput A C D other h M t) := by
  cases t with
  | inl r => cases r with
    | inl k => cases k <;> exact measurable_id
    | inr j => exact measurable_id
  | inr i => exact measurable_down

include h in
theorem replayNativeEncode_independent (ν : Measure M.NativeInputs) [IsProbabilityMeasure ν]
    (hInd : iIndepFun (fun t x => M.input x t) ν) :
    iIndepFun (fun t z => (replayModel A C D other h M).input
      (replayNativeEncode A C D other h M z) t) (ν.prod (Replay.trialMeasure ν)) := by
  have hi := encodedSplitInput_independent A C D other M ν
    (replayInput_independent_native A C D other M ν hInd)
  have hd := hi.comp (decodeReplayInput A C D other h M) (decodeReplayInput_measurable A C D other h M)
  apply hd.congr
  intro t
  filter_upwards [] with z
  cases t with
  | inl r => cases r with
    | inl k => cases k <;> rfl
    | inr j => rfl
  | inr i => rfl

end MeraConstraints.HiddenGraph.StrongFaceSplitting
