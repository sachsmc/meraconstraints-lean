import MeraConstraints.HiddenGraph.Canonicalization
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Measurable structural equations give measurable profiles

For the unobserved variables to have arbitrary distributions, the structural
equations must be measurable functions of their inputs. This file shows that if
each structural equation is measurable in its inputs, for each fixed value of the
observed parents (`MechanismsMeasurable`), then the map from the inputs of a
district to the profile of response functions of its members is measurable
(`localProfile_measurable`), and so is the map to the profiles of all districts
(`canonicalProfiles_measurable`).

The inputs are those of `Canonicalization.InputValue`. Every unobserved parent
of an observed variable is in its district, so the inputs read by its
structural equation are coordinates of the inputs of the district. No finiteness
of the input types is assumed.
-/

namespace MeraConstraints.HiddenGraph.Measurability

open MeasureTheory Canonicalization

universe u v w

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [∀ i, MeasurableSpace (val i)]
variable [∀ x, MeasurableSpace (InputValue M x)]

/-- The inputs that the structural equation of `i` reads: its unobserved
parents and its private noise. -/
abbrev MechanismInput (i : Fin n) :=
  (∀ u : {u : Fin ℓ // i ∈ G.children u}, InputValue M (.inr u.val)) ×
    InputValue M (.inl i)

/-- Each structural equation is a measurable function of its inputs, for each
fixed value of the observed parents. -/
def MechanismsMeasurable : Prop :=
  ∀ (i : Fin n) (pa : PaAssign G.observed val i),
    Measurable (fun a : MechanismInput M i =>
      M.F i pa (fun u => (a.1 u).down) a.2.down)

private theorem latent_parent_district (d : DistrictId G)
    (i : {i : Fin n // observedDistrict G i = d})
    (u : {u : Fin ℓ // i.val ∈ G.children u}) : districtOf G (.inr u.val) = d :=
  ((districtOf_eq_iff G _ _).mpr (connected_child G u i u.2)).trans i.2

/-- The profile of a district is a measurable function of the inputs of the
district. -/
theorem localProfile_measurable (hM : MechanismsMeasurable M) (d : DistrictId G) :
    Measurable (Canonicalization.localProfile M d) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro pa
  have hlatent : Measurable (fun a : LocalInput M d =>
      fun u : {u : Fin ℓ // i.val ∈ G.children u} =>
        a ⟨.inr u.val, latent_parent_district d i u⟩) :=
    measurable_pi_iff.mpr fun u =>
      measurable_pi_apply (⟨.inr u.val, latent_parent_district d i u⟩ :
        {x : HiddenGraph.Vertex (n := n) (ℓ := ℓ) // districtOf G x = d})
  have hprivate : Measurable (fun a : LocalInput M d => a ⟨.inl i.val, i.2⟩) :=
    measurable_pi_apply (⟨.inl i.val, i.2⟩ :
      {x : HiddenGraph.Vertex (n := n) (ℓ := ℓ) // districtOf G x = d})
  exact (hM i pa).comp (hlatent.prodMk hprivate)

/-- The profiles of all districts are a measurable function of all inputs. -/
theorem canonicalProfiles_measurable (hM : MechanismsMeasurable M) :
    Measurable (Canonicalization.canonicalProfiles M) := by
  apply measurable_pi_iff.mpr
  intro d
  exact (localProfile_measurable M hM d).comp
    (measurable_pi_iff.mpr fun x => measurable_pi_apply x.val)

end MeraConstraints.HiddenGraph.Measurability
