import MeraConstraints.HiddenGraph.RootMeasurability
import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# Probability models on a `RootGraph`

`RootProbabilityModel` is a structural model with independent unobserved inputs on
a `RootGraph`, as in `HiddenGraph.ProbabilityModel` but without Condition 2 (`A2`).
It is a `RootSCM` together with a probability space carrying a measurable random
input for each unobserved variable and each private noise. These inputs are
mutually independent, and each mechanism is jointly measurable in its observed
parents, unobserved parents and private noise. The input spaces are arbitrary
measurable spaces, in one common universe.

The observed distribution `RootProbabilityModel.observed` is the law of the
evaluation, written as a measure. `nativeLaw` is the joint law of all the inputs on
their own space; for finitely many unobserved variables it is again mutually
independent (`nativeLaw_independent`), and it reproduces the observed distribution
(`observed_eq_nativeLaw`).
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe u

namespace RootSCM

variable {n : ℕ} {R : Type u} {G : RootGraph n R} {val : Fin n → Type u}
  (M : RootSCM.{u,u,u,u} G val)

abbrev NativeInputs := (∀ r, M.rootValue r) × (∀ i, M.privateNoise i)

def InputValue : R ⊕ Fin n → Type u
  | .inl r => M.rootValue r
  | .inr i => M.privateNoise i

def input (x : M.NativeInputs) : ∀ t, M.InputValue t
  | .inl r => x.1 r
  | .inr i => x.2 i

variable [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

instance inputValueMeasurableSpace (t : R ⊕ Fin n) : MeasurableSpace (M.InputValue t) := by
  cases t <;> dsimp [InputValue] <;> infer_instance

theorem input_measurable (t : R ⊕ Fin n) : Measurable (fun x => M.input x t) := by
  cases t with
  | inl r => exact (measurable_pi_apply r).comp measurable_fst
  | inr i => exact (measurable_pi_apply i).comp measurable_snd

end RootSCM

/-- Mutual independence of a finite family of functions of a random element `Y`
holds also on the space of values of `Y`, under the law of `Y`. -/
theorem independent_map_inputs {I Ω T : Type*} [Fintype I]
    [MeasurableSpace Ω] [MeasurableSpace T] {B : I → Type*} [∀ i, MeasurableSpace (B i)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → T) (hY : Measurable Y)
    (F : ∀ i, T → B i) (hF : ∀ i, Measurable (F i))
    (hind : iIndepFun (fun i ω => F i (Y ω)) μ) : iIndepFun F (μ.map Y) := by
  letI : IsProbabilityMeasure (μ.map Y) := μ.isProbabilityMeasure_map hY.aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hF i).aemeasurable)).mpr
  rw [Measure.map_map (measurable_pi_iff.mpr hF) hY]
  have hi := hind.map_fun_eq_pi_map (fun i => ((hF i).comp hY).aemeasurable)
  simpa only [Measure.map_map, hY, hF, Function.comp_def] using hi

variable {n : ℕ} {R : Type u} (G : RootGraph n R) (val : Fin n → Type u)
  [∀ i, MeasurableSpace (val i)]

structure RootProbabilityModel where
  model : RootSCM.{u,u,u,u} G val
  sample : Type u
  sampleSpace : MeasurableSpace sample
  rootSpaces : ∀ r, MeasurableSpace (model.rootValue r)
  privateSpaces : ∀ i, MeasurableSpace (model.privateNoise i)
  measure : @Measure sample sampleSpace
  probability : @IsProbabilityMeasure sample sampleSpace measure
  roots : ∀ r, sample → model.rootValue r
  privateInputs : ∀ i, sample → model.privateNoise i
  measurableRoots : ∀ r, @Measurable _ _ sampleSpace (rootSpaces r) (roots r)
  measurablePrivate : ∀ i, @Measurable _ _ sampleSpace (privateSpaces i) (privateInputs i)
  independent :
    letI := sampleSpace
    letI := rootSpaces
    letI := privateSpaces
    iIndepFun (fun t ω => model.input (fun r => roots r ω, fun i => privateInputs i ω) t) measure
  measurableMechanisms :
    letI := rootSpaces
    letI := privateSpaces
    model.MechanismsMeasurable

namespace RootProbabilityModel

variable {G val} (P : RootProbabilityModel G val)

def nativeInputs (ω : P.sample) : P.model.NativeInputs :=
  (fun r => P.roots r ω, fun i => P.privateInputs i ω)

noncomputable def nativeLaw :
    @Measure P.model.NativeInputs (by letI := P.rootSpaces; letI := P.privateSpaces; infer_instance) :=
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  P.measure.map P.nativeInputs

noncomputable def observed : Measure (FullAssign val) :=
  letI := P.sampleSpace
  P.measure.map (fun ω => P.model.eval (fun r => P.roots r ω) (fun i => P.privateInputs i ω))

theorem nativeInputs_measurable :
    letI := P.sampleSpace
    letI := P.rootSpaces
    letI := P.privateSpaces
    Measurable P.nativeInputs := by
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  exact (measurable_pi_iff.mpr P.measurableRoots).prodMk (measurable_pi_iff.mpr P.measurablePrivate)

theorem nativeLaw_probability :
    letI := P.rootSpaces
    letI := P.privateSpaces
    IsProbabilityMeasure P.nativeLaw := by
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  letI := P.probability
  exact P.measure.isProbabilityMeasure_map P.nativeInputs_measurable.aemeasurable

theorem observed_probability : IsProbabilityMeasure P.observed := by
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  letI := P.probability
  exact P.measure.isProbabilityMeasure_map
    (((P.model.eval_measurable P.measurableMechanisms).comp P.nativeInputs_measurable).aemeasurable)

variable [Fintype R]

theorem nativeLaw_independent :
    letI := P.rootSpaces
    letI := P.privateSpaces
    iIndepFun (fun t x => P.model.input x t) P.nativeLaw := by
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  letI := P.probability
  exact independent_map_inputs P.measure P.nativeInputs P.nativeInputs_measurable
    (fun t x => P.model.input x t) P.model.input_measurable P.independent

omit [Fintype R] in
theorem observed_eq_nativeLaw :
    letI := P.rootSpaces
    letI := P.privateSpaces
    P.observed = P.nativeLaw.map (fun x => P.model.eval x.1 x.2) := by
  letI := P.sampleSpace
  letI := P.rootSpaces
  letI := P.privateSpaces
  exact (Measure.map_map (P.model.eval_measurable P.measurableMechanisms) P.nativeInputs_measurable).symm

end RootProbabilityModel
end MeraConstraints.HiddenGraph.StrongFaceSplitting
