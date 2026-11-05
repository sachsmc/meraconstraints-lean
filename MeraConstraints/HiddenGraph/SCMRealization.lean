import MeraConstraints.HiddenGraph.Model
import MeraConstraints.HiddenGraph.Realization

/-!
# The structural model behind the realization

`Realization.lean` builds the response functions from independent inputs, one
per district. Here the same construction is given as a structural model
`HiddenGraph.SCM`, so the realization is by a structural model on the original
hidden variables DAG.

The value of an unobserved variable is the profile of its district. An observed
variable with no unobserved parent uses its private noise, which is its own
response function. The other observed variables ignore their private noise,
which is set to a fixed response function. Each input that varies is thus
a separate independent source. The observed values need to be nonempty so
that a fixed response function exists. No positivity of the distribution
is used.
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

/-- The structural model on `G` whose response functions are `sourceMechanisms`. -/
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

/-- The value of each unobserved variable is its own source coordinate. -/
def sourceLatentInput (r : ∀ s, SourceProfile G val s) :
    ∀ u, (profileSCM G val).latentValue u := fun u => r (.inl u)

/-- The private noise: a fixed response function if the variable has an
unobserved parent, and otherwise its own source coordinate. -/
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

/-- The response functions of `profileSCM` are `sourceMechanisms`, for every
value of the inputs. This needs no assumption on the c-degree. -/
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

/-- The observed distribution `sourceObserved` is the distribution of the values
of `profileSCM` when the sources are independent. -/
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
