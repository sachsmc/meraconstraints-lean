import MeraConstraints.Probability.IndependentMap
import Mathlib.Probability.Independence.Basic

/-!
# Disjoint grouping of arbitrary measurable independent inputs

The original unobserved variables need not have finite state spaces. The
finite grouping identity therefore cannot by itself justify independence
of district response profiles for the manuscript's full model class.

This chapter proves the measure-theoretic grouping step. A finite family of
mutually independent measurable random variables may take values in arbitrary
measurable spaces. Grouping their coordinates by a block map preserves full
mutual independence. The proof promotes the earlier assignment equivalence
to a measurable equivalence and verifies that it transports product measures
correctly. Coordinate rectangles determine the product measure; regrouping
their probabilities uses the finite fiber-product identity.

Finally, the actual law of a mutually independent family is transported along
that equivalence, and the resulting block marginals are recovered by coordinate
evaluation. The output independence is a conclusion, not an assumption or a
replacement by pairwise independence. Measurability of the original inputs is
explicit, and no finiteness, countability, topology, or standard-Borel condition
is imposed on their state spaces.
-/

namespace MeraConstraints.Independent

open MeasureTheory ProbabilityTheory

variable {I D : Type*} (block : I → D) (A : I → Type*)
  [∀ i, MeasurableSpace (A i)]

/-- The coordinate-grouping equivalence is measurable in both directions. -/
def measurableGroupEquiv : (∀ i, A i) ≃ᵐ (∀ d, ∀ i : {i : I // block i = d}, A i) where
  toEquiv := groupEquiv block A
  measurable_toFun := measurable_pi_iff.mpr fun _ =>
    measurable_pi_iff.mpr fun i => measurable_pi_apply i.1
  measurable_invFun := measurable_pi_iff.mpr fun i =>
    (measurable_pi_apply (⟨i, rfl⟩ : {j : I // block j = block i})).comp
      (measurable_pi_apply (block i))

variable [Fintype I] [Fintype D] [DecidableEq D]

/-- Disjoint coordinate grouping preserves product measures. The coordinate
measures may be arbitrary sigma-finite measures, not just probability laws. -/
theorem measurePreserving_groupEquiv (ν : ∀ i, Measure (A i)) [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (measurableGroupEquiv block A) (Measure.pi ν)
      (Measure.pi fun d => Measure.pi fun i : {i : I // block i = d} => ν i) := by
  let e := measurableGroupEquiv block A
  refine MeasurePreserving.symm e.symm ?_
  refine ⟨e.symm.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  have hpre : e.symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi fun i : {i : I // block i = d} => s i) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h d i
      rcases i with ⟨i, hi⟩
      subst d
      exact h i
    · intro h i
      exact h (block i) ⟨i, rfl⟩
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Fintype.prod_fiberwise block (fun i => ν i (s i))

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- A disjoint grouping of mutually independent measurable random variables
is itself a mutually independent family, including empty blocks. The original
coordinate state spaces may be continuous, infinite, or multivariate. -/
theorem iIndepFun_grouped (X : ∀ i, Ω → A i) (hX : ∀ i, Measurable (X i))
    (hInd : iIndepFun X μ) :
    iIndepFun (fun d ω => fun i : {i : I // block i = d} => X i ω) μ := by
  letI : IsProbabilityMeasure μ := hInd.isProbabilityMeasure
  let ν := fun i => μ.map (X i)
  letI : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i => μ.isProbabilityMeasure_map (hX i).aemeasurable
  let F := fun d (ω : Ω) => fun i : {i : I // block i = d} => X i ω
  have hF : ∀ d, Measurable (F d) := fun _ =>
    measurable_pi_iff.mpr fun i => hX i
  have hvec : Measurable (fun ω i => X i ω) := measurable_pi_iff.mpr hX
  have hFvec : Measurable (fun ω d => F d ω) := measurable_pi_iff.mpr hF
  have hmap : μ.map (fun ω d => F d ω) =
      Measure.pi (fun d => Measure.pi fun i : {i : I // block i = d} => ν i) := by
    calc
      _ = (μ.map (fun ω i => X i ω)).map (measurableGroupEquiv block A) := by
        rw [Measure.map_map (measurableGroupEquiv block A).measurable hvec]
        rfl
      _ = (Measure.pi ν).map (measurableGroupEquiv block A) := by
        rw [hInd.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
      _ = _ := (measurePreserving_groupEquiv block A ν).map_eq
  have hmarginal : ∀ d, μ.map (F d) = Measure.pi (fun i : {i : I // block i = d} => ν i) := by
    intro d
    calc
      _ = (μ.map (fun ω e => F e ω)).map (fun z => z d) := by
        rw [Measure.map_map (measurable_pi_apply d) hFvec]
        rfl
      _ = _ := by
        rw [hmap]
        exact (measurePreserving_eval (fun e => Measure.pi fun i : {i : I // block i = e} => ν i) d).map_eq
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun d => (hF d).aemeasurable)).mpr
  rw [hmap]
  congr 1
  funext d
  exact (hmarginal d).symm

end RandomVariables
end MeraConstraints.Independent
