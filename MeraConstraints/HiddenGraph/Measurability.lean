import MeraConstraints.HiddenGraph.Canonicalization
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Measurable structural mechanisms induce measurable response profiles

An NPSEM's structural functions must be measurable in their random inputs
so that their outputs have probability laws. The probability canonicalization
chapter exposes measurability of district response maps as an interface.
Here that interface is derived from ordinary per-node structural-mechanism
measurability, for each fixed assignment of observed parents.

The source coordinate spaces are exactly `Canonicalization.InputValue`: the
original latent and private input spaces, placed in a common universe using
`ULift`. A mechanism accepts only its actual latent parents and its own
private disturbance, and removes the lifts before calling the original `F`.
No additional source-coordinate restriction is introduced.

Every allowed latent parent belongs to the child's graph district. Thus
projecting a district input tuple to the mechanism's allowed inputs is a
measurable tuple of coordinate projections. Composing with each measurable
structural mechanism, then assembling the parent-assignment and member
coordinates, proves measurability of the complete local response profile.
No finiteness assumption on the original input types is used.
-/

namespace MeraConstraints.HiddenGraph.Measurability

open MeasureTheory Canonicalization

universe u v w

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
variable (M : HiddenGraph.SCM.{u, v, w} G val)
variable [∀ i, MeasurableSpace (val i)]
variable [∀ x, MeasurableSpace (InputValue M x)]

/-- Precisely the exogenous arguments permitted at a node, with the same
lifted coordinate spaces as the original-input probability construction. -/
abbrev MechanismInput (i : Fin n) :=
  (∀ u : {u : Fin ℓ // i ∈ G.children u}, InputValue M (.inr u.val)) ×
    InputValue M (.inl i)

/-- Standard NPSEM measurability in the exogenous inputs, at every fixed
observed-parent assignment. It makes no independence or causal-identification
claim about those inputs or about the resulting response profiles. -/
def MechanismsMeasurable : Prop :=
  ∀ (i : Fin n) (pa : PaAssign G.observed val i),
    Measurable (fun a : MechanismInput M i =>
      M.F i pa (fun u => (a.1 u).down) a.2.down)

private theorem latent_parent_district (d : DistrictId G)
    (i : {i : Fin n // observedDistrict G i = d})
    (u : {u : Fin ℓ // i.val ∈ G.children u}) : districtOf G (.inr u.val) = d :=
  ((districtOf_eq_iff G _ _).mpr (connected_child G u i u.2)).trans i.2

/-- Measurable local response profiles follow from measurable node mechanisms.
The district condition is used only to justify the allowed input projections. -/
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

/-- The full tuple of induced district profiles is measurable as well. -/
theorem canonicalProfiles_measurable (hM : MechanismsMeasurable M) :
    Measurable (Canonicalization.canonicalProfiles M) := by
  apply measurable_pi_iff.mpr
  intro d
  exact (localProfile_measurable M hM d).comp
    (measurable_pi_iff.mpr fun x => measurable_pi_apply x.val)

end MeraConstraints.HiddenGraph.Measurability
