import MeraConstraints.HiddenGraph.Merging
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.MeasureRealization

/-!
# Latent merging contains the original marginal model

For the graph actually constructed in `HiddenGraph.Merging`, this chapter
proves the probabilistic assertion of Remark `prop:merge` in the correct
direction: **every original observed law is realized on the merged graph**.

Start with an arbitrary original `ProbabilityModel`, whose latent/private
input spaces and probability space may be infinite. Its district response
maps are derived from its actual mechanisms and original independent inputs.
They are mutually independent by measurable disjoint canonicalization.

The merged graph has the same observed arrows and exactly the same observed
district partition. Relabel the derived profile maps through the proved
district equivalence, preserving their independence. Their actual finite
laws then reproduce the original observed distribution using the merged
graph's profiles. Finally, the earlier probability-space realization theorem
constructs an actual probability model on that merged graph.

No induced model or profile representation is assumed. No strict positivity
or original latent-state finiteness is required. We do not claim the reverse
inclusion: merging removes restrictions on the joint mechanisms within a
district, so the merged model may be strictly larger. Constraints valid on
the merged model are consequently valid on the original model.

Preserving the observed district partition and directed arrows does not
preserve every conditional independence: new shared-root arrows may remove
some independencies. As stated in `sec:nonlin`, the algorithm's independence
step must therefore still use the original graph.
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

/-- Relabel a response profile using the actual observed-district equivalence.
The observed parent sets are unchanged by merging, so no mechanism is altered. -/
noncomputable def mergedProfileMap (d : DistrictId (Merging.mergedGraph G))
    (r : GlobalModel.Profile G.observed val (observedDistrict G) (Merging.districtEquiv G d)) :
    GlobalModel.Profile (Merging.mergedGraph G).observed val
      (observedDistrict (Merging.mergedGraph G)) d :=
  fun i => r ⟨i, merged_member_original G d i⟩

/-- The assembled global mechanism is literally unchanged by relabeling. -/
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
/-- Derived merged-graph profile laws for an arbitrary original probability
model. Independence comes from original inputs, not from a profile premise. -/
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
/-- Every original probability model has an actual merged-graph probability
model with the same observed law. All original input spaces may be arbitrary. -/
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
/-- The marginal-model inclusion of Remark `prop:merge`, with original and
merged model names kept explicit to prevent reversing the inclusion. -/
theorem original_model_subset_merged (p : FullAssign val → ℝ) :
    (∃ P : ProbabilityModel G val, P.observed = p) →
      ∃ Q : ProbabilityModel (Merging.mergedGraph G) val, Q.observed = p := by
  rintro ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := original_probabilityModel_realizable_merged G val P
  exact ⟨Q, hQ.trans hP⟩

omit [DecidableEq (DistrictId G)] [DecidableEq (DistrictId (Merging.mergedGraph G))] in
/-- Every constraint valid on the merged model is valid on the original model.
The predicate may express an equality, inequality, or collection of constraints. -/
theorem constraint_valid_on_original_of_merged
    (C : (FullAssign val → ℝ) → Prop)
    (hC : ∀ Q : ProbabilityModel (Merging.mergedGraph G) val, C Q.observed)
    (P : ProbabilityModel G val) : C P.observed := by
  obtain ⟨Q, hQ⟩ := original_probabilityModel_realizable_merged G val P
  simpa only [hQ] using hC Q

end MeraConstraints.Completeness
