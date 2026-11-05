import MeraConstraints.HiddenGraph.Merging
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.MeasureRealization

/-!
# Remark 4 (`prop:merge`): merging unobserved variables

Let `𝒢'` be the merged graph of `HiddenGraph.Merging`, in which the unobserved
variables of each district are merged into one parent of all its members. The
marginal model of the original graph is contained in that of the merged graph,
`𝓜(𝒢) ⊆ 𝓜(𝒢')`: every observed distribution of a `ProbabilityModel` on `G` is
the observed distribution of one on the merged graph. Hence a constraint that
holds on the merged graph holds on the original graph. The reverse inclusion is
not claimed.

The proof starts from a `ProbabilityModel` on `G`. Its inputs and the probability
space may be infinite. The distributions of the response function variables of
its districts are independent. The merged graph has the same observed arrows and
the same districts, so these response functions can be relabeled as response
functions of the merged graph, keeping the observed distribution.
`probabilityModelOfProfiles` then gives a `ProbabilityModel` on the merged graph
with that observed distribution. Positivity and finite inputs are not needed.

The merged graph can lose conditional independencies of the original graph. The
independence step of an algorithm should therefore use the original graph (see
`sec:nonlin` in the manuscript).
-/

namespace MeraConstraints.Completeness

open MeasureTheory ProbabilityTheory HiddenGraph

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)

private theorem merged_member_original (d : DistrictId (Merging.mergedGraph G))
    (i : {i : Fin n // observedDistrict (Merging.mergedGraph G) i = d}) :
    observedDistrict G i = Merging.districtEquiv G d := by
  have h := congrArg (Merging.districtEquiv G) i.property
  simpa only [Merging.districtEquiv_observed] using h

/-- Relabel a profile of the original graph as a profile of the merged graph,
using the equivalence between their districts. Merging does not change the
observed parents, so the response functions are unchanged. -/
noncomputable def mergedProfileMap (d : DistrictId (Merging.mergedGraph G))
    (r : GlobalModel.Profile G.observed val (observedDistrict G) (Merging.districtEquiv G d)) :
    GlobalModel.Profile (Merging.mergedGraph G).observed val
      (observedDistrict (Merging.mergedGraph G)) d :=
  fun i => r ⟨i, merged_member_original G d i⟩

/-- Relabeling the profiles does not change the response functions of the
observed variables. -/
theorem assemble_mergedProfiles
    (r : ∀ d, GlobalModel.Profile G.observed val (observedDistrict G) d) :
    GlobalModel.assemble (Merging.mergedGraph G).observed val
      (observedDistrict (Merging.mergedGraph G))
      (fun d => mergedProfileMap G val d (r (Merging.districtEquiv G d))) =
      GlobalModel.assemble G.observed val (observedDistrict G) r := rfl

variable [DecidableEq (DistrictId G)] [DecidableEq (DistrictId (Merging.mergedGraph G))]
variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)]
variable [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]

omit [∀ i, Nonempty (val i)] in
/-- Every `ProbabilityModel` on `G` has, for each district of the merged graph, a
distribution of the response function variables, whose response function model
has the same observed distribution. -/
theorem original_probabilityModel_has_merged_profiles (P : ProbabilityModel G val) :
    ∃ q : ∀ d, GlobalModel.Profile (Merging.mergedGraph G).observed val
        (observedDistrict (Merging.mergedGraph G)) d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ
        (GlobalModel.Profile (Merging.mergedGraph G).observed val
          (observedDistrict (Merging.mergedGraph G)) d)) ∧
      P.observed = GlobalModel.observed (Merging.mergedGraph G).observed val
        (observedDistrict (Merging.mergedGraph G)) q := by
  classical
  letI := P.sampleSpace
  letI := P.inputSpaces
  letI := P.probability
  let Y := MeasureCanonicalization.profileMaps P.model P.inputs
  have hLocal := Measurability.localProfile_measurable P.model P.measurableMechanisms
  have hYmeas : ∀ d, Measurable (Y d) :=
    MeasureCanonicalization.profileMaps_measurable P.model P.inputs P.measurableInputs hLocal
  have hYind : iIndepFun Y P.measure :=
    MeasureCanonicalization.profileMaps_iIndepFun P.model P.measure P.inputs
      P.measurableInputs P.independent hLocal
  have hMap : ∀ d, Measurable (mergedProfileMap G val d) :=
    fun d => measurable_of_finite _
  let Z := fun d ω => mergedProfileMap G val d (Y (Merging.districtEquiv G d) ω)
  have hZmeas : ∀ d, Measurable (Z d) :=
    fun d => (hMap d).comp (hYmeas (Merging.districtEquiv G d))
  have hZind : iIndepFun Z P.measure :=
    (iIndepFun.precomp (Merging.districtEquiv G).injective hYind).comp
      (mergedProfileMap G val) hMap
  let q := fun d => MeasureFinite.law P.measure (Z d)
  have hq : ∀ d, q d ∈ stdSimplex ℝ
      (GlobalModel.Profile (Merging.mergedGraph G).observed val
        (observedDistrict (Merging.mergedGraph G)) d) :=
    fun d => MeasureFinite.law_mem_stdSimplex P.measure (Z d) (hZmeas d)
  refine ⟨q, hq, ?_⟩
  have hpoint : (fun ω => Canonicalization.evalInputs P.model (fun x => P.inputs x ω)) =
      (fun ω => evalR (GlobalModel.assemble (Merging.mergedGraph G).observed val
        (observedDistrict (Merging.mergedGraph G)) (fun d => Z d ω))) := by
    funext ω
    rw [Canonicalization.evalInputs_eq_assembled]
    change evalR (GlobalModel.assemble G.observed val (observedDistrict G) (fun d => Y d ω)) = _
    exact congrArg (fun r : RespAssign G.observed val => evalR r)
      (assemble_mergedProfiles G val (fun d => Y d ω)).symm
  change MeasureFinite.law P.measure
    (fun ω => Canonicalization.evalInputs P.model (fun x => P.inputs x ω)) = _
  rw [hpoint]
  exact MeasureFinite.law_eval_of_iIndepFun P.measure Z hZmeas hZind
    (fun r => evalR (GlobalModel.assemble (Merging.mergedGraph G).observed val
      (observedDistrict (Merging.mergedGraph G)) r))

omit [DecidableEq (DistrictId G)] [DecidableEq (DistrictId (Merging.mergedGraph G))] in
/-- Every `ProbabilityModel` on `G` has a `ProbabilityModel` on the merged graph
with the same observed distribution. The input spaces may be arbitrary. -/
theorem original_probabilityModel_realizable_merged (P : ProbabilityModel G val) :
    ∃ Q : ProbabilityModel (Merging.mergedGraph G) val, Q.observed = P.observed := by
  classical
  obtain ⟨q, hq, hP⟩ := original_probabilityModel_has_merged_profiles G val P
  refine ⟨probabilityModelOfProfiles (Merging.mergedGraph G) val q hq, ?_⟩
  calc
    _ = sourceObserved (Merging.mergedGraph G) val q :=
      probabilityModelOfProfiles_observed _ _ q hq
    _ = GlobalModel.observed (Merging.mergedGraph G).observed val
        (observedDistrict (Merging.mergedGraph G)) q :=
      sourceObserved_eq_observed _ _ (Merging.mergedGraph_cDegree_le_one G) q
    _ = P.observed := hP.symm

omit [DecidableEq (DistrictId G)] [DecidableEq (DistrictId (Merging.mergedGraph G))] in
/-- Remark 4 (`prop:merge`): the marginal model of the original graph `G` is
contained in that of the merged graph. -/
theorem original_model_subset_merged (p : FullAssign val → ℝ) :
    (∃ P : ProbabilityModel G val, P.observed = p) →
      ∃ Q : ProbabilityModel (Merging.mergedGraph G) val, Q.observed = p := by
  rintro ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := original_probabilityModel_realizable_merged G val P
  exact ⟨Q, hQ.trans hP⟩

omit [DecidableEq (DistrictId G)] [DecidableEq (DistrictId (Merging.mergedGraph G))] in
/-- A constraint on the observed distribution that holds on the marginal model of
the merged graph holds on that of the original graph. It may be an equality, an
inequality, or a collection of constraints. -/
theorem constraint_valid_on_original_of_merged
    (C : (FullAssign val → ℝ) → Prop)
    (hC : ∀ Q : ProbabilityModel (Merging.mergedGraph G) val, C Q.observed)
    (P : ProbabilityModel G val) : C P.observed := by
  obtain ⟨Q, hQ⟩ := original_probabilityModel_realizable_merged G val P
  simpa only [hQ] using hC Q

end MeraConstraints.Completeness
