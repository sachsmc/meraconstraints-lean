import MeraConstraints.HiddenGraph.Model
import MeraConstraints.HiddenGraph.Realization

/-!
# An explicit original-graph SCM for the profile construction

`Realization.lean` assembles mechanisms from independent sources and proves
their generated law equals the district-profile law. Here those mechanisms
are packaged as an actual `HiddenGraph.SCM`, whose argument types enforce
the original observed and latent parent restrictions.

The root input of `u` is the profile of its graph district. An unconfounded
observed vertex receives its own private response function. Confounded
vertices also have private inputs in the SCM type, but they ignore them;
we set these unused inputs to fixed constants. Thus every varying original
input reads its **own** independent source coordinate. In a c-degree-one
graph, the source/district bijection proves no district profile is copied
between distinct latent roots.

Nonempty observed value types are explicit: they supply arbitrary constant
private response functions. This is a state-space assumption, not a positive
probability assumption. The identities below allow zero probabilities.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type*)

private theorem observedDistrict_eq_latent_of_parent (i : Fin n) (u : Fin ℓ)
    (hi : i ∈ G.children u) : observedDistrict G i = sourceDistrict G (.inl u) :=
  (districtOf_eq_iff G _ _).2 (Relation.EqvGen.symm _ _ (connected_child G u i hi))

private theorem source_profile_eval_transport (r : ∀ s, SourceProfile G val s)
    (i : Fin n) (s t : Source G) (hst : s = t)
    (hi : observedDistrict G i = sourceDistrict G s)
    (pa : PaAssign G.observed val i) :
    r s ⟨i, hi⟩ pa = r t ⟨i, hi.trans (congrArg (sourceDistrict G) hst)⟩ pa := by
  cases hst
  rfl

private theorem sourceMechanisms_at_latent (r : ∀ s, SourceProfile G val s)
    (i : Fin n) (hi : HasLatentParent G i) (pa : PaAssign G.observed val i) :
    sourceMechanisms G val r i pa = r (.inl (Classical.choose hi))
      ⟨i, observedDistrict_eq_latent_of_parent G i _ (Classical.choose_spec hi)⟩ pa := by
  have hs : sourceOf G i = .inl (Classical.choose hi) := by simp [sourceOf, hi]
  exact source_profile_eval_transport G val r i _ _ hs (sourceOf_district G i).symm pa

private theorem sourceMechanisms_at_private (r : ∀ s, SourceProfile G val s)
    (i : Fin n) (hi : ¬ HasLatentParent G i) (pa : PaAssign G.observed val i) :
    sourceMechanisms G val r i pa = r (.inr ⟨i, hi⟩) ⟨i, rfl⟩ pa := by
  have hs : sourceOf G i = .inr ⟨i, hi⟩ := by simp [sourceOf, hi]
  exact source_profile_eval_transport G val r i _ _ hs (sourceOf_district G i).symm pa

variable [∀ i, Nonempty (val i)]

noncomputable def defaultResponse (i : Fin n) : RespFun G.observed val i :=
  fun _ => Classical.choice (inferInstance : Nonempty (val i))

/-- Explicit graph-compatible SCM realizing the source mechanisms. -/
noncomputable def profileSCM : SCM G val where
  latentValue := fun u => SourceProfile G val (.inl u)
  latentNonempty := fun _ => inferInstance
  privateNoise := fun i => RespFun G.observed val i
  privateNonempty := fun _ => inferInstance
  F := by
    classical
    exact fun i pa lat ε =>
      if hi : HasLatentParent G i then
        lat ⟨Classical.choose hi, Classical.choose_spec hi⟩
          ⟨i, observedDistrict_eq_latent_of_parent G i _ (Classical.choose_spec hi)⟩ pa
      else ε pa

/-- Each latent root receives only its own independent source coordinate. -/
def sourceLatentInput (r : ∀ s, SourceProfile G val s) :
    ∀ u, (profileSCM G val).latentValue u := fun u => r (.inl u)

/-- Fixed private input at a confounded vertex; otherwise the singleton
district's response function at its own unique vertex. -/
noncomputable def sourcePrivateInput (r : ∀ s, SourceProfile G val s) :
    ∀ i, (profileSCM G val).privateNoise i := by
  classical
  exact fun i => if hi : HasLatentParent G i then
    defaultResponse G val i
  else r (.inr ⟨i, hi⟩) ⟨i, rfl⟩

theorem sourcePrivateInput_of_has_parent (r : ∀ s, SourceProfile G val s)
    (i : Fin n) (hi : HasLatentParent G i) :
    sourcePrivateInput G val r i = defaultResponse G val i := by
  simp [sourcePrivateInput, hi]

theorem sourcePrivateInput_of_no_parent (r : ∀ s, SourceProfile G val s)
    (i : Fin n) (hi : ¬ HasLatentParent G i) :
    sourcePrivateInput G val r i = r (.inr ⟨i, hi⟩) ⟨i, rfl⟩ := by
  simp [sourcePrivateInput, hi]

/-- The explicit SCM has exactly the source mechanisms, for every input
assignment. No probability or c-degree assumption is used in this identity. -/
theorem profileSCM_responseProfile (r : ∀ s, SourceProfile G val s) :
    (profileSCM G val).responseProfile
      (sourceLatentInput G val r) (sourcePrivateInput G val r) =
      sourceMechanisms G val r := by
  funext i pa
  by_cases hi : HasLatentParent G i
  · rw [sourceMechanisms_at_latent G val r i hi pa]
    simp [SCM.responseProfile, profileSCM, sourceLatentInput, hi]
  · rw [sourceMechanisms_at_private G val r i hi pa]
    simp [SCM.responseProfile, profileSCM, sourcePrivateInput, hi]

theorem profileSCM_eval (r : ∀ s, SourceProfile G val s) :
    (profileSCM G val).eval (sourceLatentInput G val r) (sourcePrivateInput G val r) =
      evalR (sourceMechanisms G val r) := by
  rw [SCM.eval_eq_evalR, profileSCM_responseProfile]

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [DecidableEq (DistrictId G)]

/-- The source-generated observed law is literally a pushforward of the
explicit original-graph SCM's evaluation under the independent source law. -/
theorem sourceObserved_eq_profileSCM
    (q : ∀ d, DistrictProfile G val d → ℝ) :
    sourceObserved G val q =
      pushforward
        (fun r => (profileSCM G val).eval
          (sourceLatentInput G val r) (sourcePrivateInput G val r))
        (Independent.joint (fun s => q (sourceDistrict G s))) := by
  classical
  simp only [profileSCM_eval]
  rfl

end MeraConstraints.HiddenGraph
