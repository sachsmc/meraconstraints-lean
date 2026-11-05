import MeraConstraints.HiddenGraph.StrongFaceCoupling
import MeraConstraints.Probability.IndependentAppend

/-!
# The inputs of the split model are mutually independent

In `coupledReplayEval`, the new unobserved variable with children `D` carries the
stream, and every other unobserved variable and every private noise carries its
coordinate of the original inputs. Suppose the original inputs are mutually
independent under `ν`, and the stream has law `trialMeasure ν` and is independent
of them (the product measure). Then all inputs of the split model are mutually
independent (`encodedSplitInput_independent`). The proof views them as an injective
re-indexing of the original inputs with the stream appended, which is independent by
`Probability.IndependentAppend`. This gives the independence required of a model
with independent unobserved inputs. The selected candidate, which depends on the
original inputs, is not an input of the split model.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K] [Fintype J]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

def StreamInputValue : Option (ReplayInputIndex (K := K) (J := J) (n := n)) → Type (max uK uJ uR uP)
  | none => ℕ → ReplayCandidate A C D other M
  | some t => ReplayInputValue A C D other M t

def splitInputIndex : ((Option K ⊕ J) ⊕ Fin n) → Option (ReplayInputIndex (K := K) (J := J) (n := n))
  | .inl (.inl none) => none
  | .inl (.inl (some k)) => some (.inl (.inl k))
  | .inl (.inr j) => some (.inl (.inr j))
  | .inr i => some (.inr i)

omit [Fintype K] [Fintype J] in
theorem splitInputIndex_injective : Function.Injective (splitInputIndex (K := K) (J := J) (n := n)) := by
  intro a b hab
  cases a with
  | inl a => cases a with
    | inl a => cases a <;> cases b with
      | inl b => cases b with
        | inl b => cases b <;> simp_all [splitInputIndex]
        | inr b => simp_all [splitInputIndex]
      | inr b => simp_all [splitInputIndex]
    | inr a => cases b with
      | inl b => cases b with
        | inl b => cases b <;> simp_all [splitInputIndex]
        | inr b => simp_all [splitInputIndex]
      | inr b => simp_all [splitInputIndex]
  | inr a => cases b with
    | inl b => cases b with
      | inl b => cases b <;> simp_all [splitInputIndex]
      | inr b => simp_all [splitInputIndex]
    | inr b => simp_all [splitInputIndex]

/-- The inputs of the split model as functions of the original inputs and the
stream. The `ULift` wrappers only change the Lean type of a value, not the value. -/
def encodedSplitInput (t : (Option K ⊕ J) ⊕ Fin n)
    (z : ReplayCandidate A C D other M × (ℕ → ReplayCandidate A C D other M)) :
    StreamInputValue A C D other M (splitInputIndex t) :=
  match t with
  | .inl (.inl none) => z.2
  | .inl (.inl (some k)) => ULift.up (z.1.1 (.inl k))
  | .inl (.inr j) => ULift.up (z.1.1 (.inr j))
  | .inr i => ULift.up (z.1.2 i)

omit [Fintype K] [Fintype J] in
theorem encodedSplitInput_root (r : Option K ⊕ J)
    (z : ReplayCandidate A C D other M × (ℕ → ReplayCandidate A C D other M)) :
    HEq (encodedSplitInput A C D other M (.inl r) z)
      (encodeReplayStream A C D other M z.1 z.2 r) := by
  cases r with
  | inl k => cases k <;> rfl
  | inr j => rfl

omit [Fintype K] [Fintype J] in
theorem encodedSplitInput_private (i : Fin n)
    (z : ReplayCandidate A C D other M × (ℕ → ReplayCandidate A C D other M)) :
    (encodedSplitInput A C D other M (.inr i) z).down = z.1.2 i := rfl

variable [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

instance streamInputValueMeasurableSpace (t : Option (ReplayInputIndex (K := K) (J := J) (n := n))) :
    MeasurableSpace (StreamInputValue A C D other M t) := by
  cases t <;> dsimp [StreamInputValue] <;> infer_instance

theorem encodedSplitInput_independent (ν : Measure (ReplayCandidate A C D other M))
    [IsProbabilityMeasure ν]
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    iIndepFun (encodedSplitInput A C D other M) (ν.prod (Replay.trialMeasure ν)) := by
  have hi := Independent.appendInput_independent (B := StreamInputValue A C D other M)
    (hτ := Replay.trialMeasure_probability ν)
    ν (Replay.trialMeasure ν) (fun t x => replayInput A C D other M x t)
    (replayInput_measurable A C D other M) hInd
  have hr := hi.precomp (splitInputIndex_injective (K := K) (J := J) (n := n))
  apply hr.congr
  intro t
  filter_upwards [] with z
  cases t with
  | inl r => cases r with
    | inl k => cases k <;> rfl
    | inr j => rfl
  | inr i => rfl

end MeraConstraints.HiddenGraph.StrongFaceSplitting
