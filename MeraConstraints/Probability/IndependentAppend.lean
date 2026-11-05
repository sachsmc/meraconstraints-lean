import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# Appending an independent input to an independent family

Let `X i` (for `i` in a finite index type `I`) be mutually independent random
variables on `Ω` under a probability measure `μ`, and let `τ` be a probability
measure on one further space. On the product space with measure `μ.prod τ`,
the family consisting of the `X i` (as functions of the first coordinate) and the
second coordinate is mutually independent (`appendInput_independent`).

This is used in `HiddenGraph.StrongFaceIndependence`, for the independence of the
inputs in the proof of Proposition 6 (`prop:strong`).
-/

namespace MeraConstraints.Independent

open MeasureTheory ProbabilityTheory

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
  {B : Option I → Type*} [∀ i, MeasurableSpace (B i)]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Measure (B none)) [hτ : IsProbabilityMeasure τ]
  (X : ∀ i, Ω → B (some i))

def appendInput (z : Ω × B none) : ∀ i, B i :=
  (MeasurableEquiv.piOptionEquivProd B).symm (fun i => X i z.1, z.2)

omit [Fintype I] in
theorem appendInput_measurable (hX : ∀ i, Measurable (X i)) :
    Measurable (appendInput X) :=
  (MeasurableEquiv.piOptionEquivProd B).symm.measurable.comp
    ((measurable_pi_iff.mpr fun i => (hX i).comp measurable_fst).prodMk measurable_snd)

theorem appendInput_independent (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ) :
    iIndepFun (fun i z => appendInput X z i) (μ.prod τ) := by
  let ν : ∀ i, Measure (B i) := fun i => match i with
    | none => τ
    | some i => μ.map (X i)
  letI : ∀ i, IsProbabilityMeasure (ν i) := fun i => by
    cases i with
    | none => exact inferInstanceAs (IsProbabilityMeasure τ)
    | some i => exact μ.isProbabilityMeasure_map (hX i).aemeasurable
  have hv : Measurable (fun ω i => X i ω) := measurable_pi_iff.mpr hX
  have hp : (μ.prod τ).map (fun z : Ω × B none => (fun i => X i z.1, z.2)) =
      (Measure.pi fun i => ν (some i)).prod (ν none) := by
    have hp' := (indepFun_prod (μ := μ) (ν := τ) hv measurable_id).map_prod_eq_prod_map_map
      (hv.comp measurable_fst).aemeasurable measurable_snd.aemeasurable
    simp only [Function.comp_def] at hp'
    rw [hp']
    change ((μ.prod τ).map ((fun ω i => X i ω) ∘ Prod.fst)).prod
      ((μ.prod τ).map Prod.snd) = _
    rw [← Measure.map_map hv measurable_fst, Measure.map_fst_prod, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [hInd.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
  have hm : (μ.prod τ).map (appendInput X) = Measure.pi ν := by
    calc
      _ = ((μ.prod τ).map (fun z : Ω × B none => (fun i => X i z.1, z.2))).map
          (MeasurableEquiv.piOptionEquivProd B).symm := by
        have hpmeas : Measurable (fun z : Ω × B none => (fun i => X i z.1, z.2)) :=
          (hv.comp measurable_fst).prodMk measurable_snd
        rw [Measure.map_map (MeasurableEquiv.piOptionEquivProd B).symm.measurable hpmeas]
        rfl
      _ = _ := by rw [hp]; exact Measure.pi_map_piOptionEquivProd ν
  have hmarg (i : Option I) : (μ.prod τ).map (fun z => appendInput X z i) = ν i := by
    calc
      _ = ((μ.prod τ).map (appendInput X)).map (fun z => z i) := by
        rw [Measure.map_map (measurable_pi_apply i) (appendInput_measurable X hX)]
        rfl
      _ = _ := by rw [hm]; exact (measurePreserving_eval ν i).map_eq
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((measurable_pi_apply i).comp (appendInput_measurable X hX)).aemeasurable)).mpr
  change (μ.prod τ).map (appendInput X) = Measure.pi (fun i => (μ.prod τ).map (fun z => appendInput X z i))
  rw [hm]
  congr 1
  funext i
  exact (hmarg i).symm

end MeraConstraints.Independent
