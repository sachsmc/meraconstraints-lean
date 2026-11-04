import MeraConstraints.HiddenGraph.StrongFaceBundling
import MeraConstraints.HiddenGraph.StrongFaceNativeTransport

/-!
# Strong Face Splitting for actual A1 probability models

Manuscript `prop:strong` preserves the entire observational marginal model.
Every original model has a split probability model with the same observed
law, using the checked measurable independent conditional-replay transport.
Every split model has an original model with the same law, by disjointly
bundling its common D input into one selected anchor root.

These are literal bundled models with arbitrary measurable root, private and
sample spaces. Their independence and mechanism measurability fields are
proved. The reverse construction first derives the joint original input law
from the original arbitrary sample space, then takes its product with the
independent stream law. No conditional output law, positivity, c-degree, or
A2 condition is assumed. Observed states are finite, as in the manuscript.
The intended nonempty selected root family is explicit in `Conditions`.
-/

namespace MeraConstraints.Completeness

open MeasureTheory ProbabilityTheory HiddenGraph.StrongFaceSplitting

universe u

variable {n : ℕ} {K J : Type u} [Fintype K] [Fintype J]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (val : Fin n → Type u) [∀ i, MeasurableSpace (val i)]

/-- The easy direction retains the source sample space and groups the common
D input with exactly one selected original root. -/
noncomputable def probabilityModel_bundleSplit
    (P : RootProbabilityModel (splitGraph A C D other) val)
    (anchor : K) (constant : P.model.rootValue (.inl none)) :
    RootProbabilityModel (originalGraph A C D other) val := by
  classical
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  exact {
    model := bundledModel A C D other P.model anchor
    sample := P.sample
    sampleSpace := P.sampleSpace
    rootSpaces := fun r => bundledModelRootMeasurableSpace A C D other P.model anchor r
    privateSpaces := P.privateSpaces
    measure := P.measure
    probability := P.probability
    roots := fun r ω => (bundleEncode A C D other P.model anchor constant (P.nativeInputs ω)).1 r
    privateInputs := P.privateInputs
    measurableRoots := fun r => (measurable_pi_apply r).comp
      (((bundleEncode_measurable A C D other P.model anchor constant).comp P.nativeInputs_measurable).fst)
    measurablePrivate := P.measurablePrivate
    independent := bundleEncode_independent A C D other P.model P.measure P.nativeInputs
      P.nativeInputs_measurable P.independent anchor constant
    measurableMechanisms := bundledModel_mechanismsMeasurable A C D other P.model P.measurableMechanisms anchor }

theorem probabilityModel_bundleSplit_observed
    (P : RootProbabilityModel (splitGraph A C D other) val)
    (anchor : K) (constant : P.model.rootValue (.inl none)) :
    (probabilityModel_bundleSplit A C D other val P anchor constant).observed = P.observed := by
  classical
  letI := P.sampleSpace
  change P.measure.map (fun ω => (bundledModel A C D other P.model anchor).eval
    (encodeSplitInputs A C D other P.model anchor constant (fun r => P.roots r ω))
    (fun i => P.privateInputs i ω)) =
      P.measure.map (fun ω => P.model.eval (fun r => P.roots r ω) (fun i => P.privateInputs i ω))
  apply congrArg (fun f => P.measure.map f)
  funext ω
  exact split_eval_reproduced A C D other P.model anchor constant _ _

variable [∀ i, Fintype (val i)] [∀ i, MeasurableSingletonClass (val i)]
  (h : Conditions A C D other)

/-- The reverse direction is an actual split probability model. Its sample
space carries the derived original input law and an independent trial stream. -/
noncomputable def probabilityModel_replayStrong
    (P : RootProbabilityModel (originalGraph A C D other) val) :
    RootProbabilityModel (splitGraph A C D other) val := by
  letI := P.rootSpaces
  letI := P.privateSpaces
  letI := P.nativeLaw_probability
  exact {
    model := replayModel A C D other h P.model
    sample := P.model.NativeInputs × (ℕ → P.model.NativeInputs)
    sampleSpace := inferInstance
    rootSpaces := fun r => replayModelRootValueMeasurableSpace A C D other h P.model r
    privateSpaces := P.privateSpaces
    measure := P.nativeLaw.prod (MeraConstraints.Replay.trialMeasure P.nativeLaw)
    probability := inferInstance
    roots := fun r z => (replayNativeEncode A C D other h P.model z).1 r
    privateInputs := fun i z => z.1.2 i
    measurableRoots := fun r => (measurable_pi_apply r).comp
      (replayNativeEncode_measurable A C D other h P.model).fst
    measurablePrivate := fun i => (measurable_pi_apply i).comp measurable_fst.snd
    independent := replayNativeEncode_independent A C D other h P.model P.nativeLaw P.nativeLaw_independent
    measurableMechanisms := replayModel_mechanismsMeasurable A C D other h P.model P.measurableMechanisms }

theorem probabilityModel_replayStrong_observed
    (P : RootProbabilityModel (originalGraph A C D other) val) :
    (probabilityModel_replayStrong A C D other val h P).observed = P.observed := by
  letI := P.rootSpaces
  letI := P.privateSpaces
  letI := P.nativeLaw_probability
  change (P.nativeLaw.prod (MeraConstraints.Replay.trialMeasure P.nativeLaw)).map
    (coupledReplayEval A C D other h P.model) = P.observed
  rw [coupledReplayEval_map A C D other h P.model P.nativeLaw P.measurableMechanisms
    (replayInput_independent_native A C D other P.model P.nativeLaw P.nativeLaw_independent)]
  exact P.observed_eq_nativeLaw.symm

include h in
/-- Proposition `prop:strong`: equality of the actual A1 observational
marginal-model classes, including zero-probability observed states. -/
theorem original_model_iff_strongFaceSplitting (p : Measure (FullAssign val)) :
    (∃ P : RootProbabilityModel (originalGraph A C D other) val, P.observed = p) ↔
      ∃ Q : RootProbabilityModel (splitGraph A C D other) val, Q.observed = p := by
  classical
  constructor
  · rintro ⟨P, hp⟩
    exact ⟨probabilityModel_replayStrong A C D other val h P,
      (probabilityModel_replayStrong_observed A C D other val h P).trans hp⟩
  · rintro ⟨Q, hq⟩
    let anchor := Classical.choice h.selected_nonempty
    let constant := Classical.choice (Q.model.rootNonempty (.inl none))
    exact ⟨probabilityModel_bundleSplit A C D other val Q anchor constant,
      (probabilityModel_bundleSplit_observed A C D other val Q anchor constant).trans hq⟩

include h in
/-- Every observed-law predicate is valid on the original graph iff it is
valid on the split graph: the manuscript's 'same constraints' conclusion. -/
theorem constraint_valid_iff_strongFaceSplitting (F : Measure (FullAssign val) → Prop) :
    (∀ P : RootProbabilityModel (originalGraph A C D other) val, F P.observed) ↔
      ∀ Q : RootProbabilityModel (splitGraph A C D other) val, F Q.observed := by
  classical
  constructor
  · intro hF Q
    let anchor := Classical.choice h.selected_nonempty
    let constant := Classical.choice (Q.model.rootNonempty (.inl none))
    rw [← probabilityModel_bundleSplit_observed A C D other val Q anchor constant]
    exact hF _
  · intro hF P
    rw [← probabilityModel_replayStrong_observed A C D other val h P]
    exact hF _

end MeraConstraints.Completeness
