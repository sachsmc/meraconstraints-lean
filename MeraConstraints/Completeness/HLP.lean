import MeraConstraints.HiddenGraph.HLPInputs

/-!
# HLP equivalence for actual original probability models

Proposition `prop:hlp`: adding or removing the specified observed edge
preserves the marginal model. Forward transport keeps the original inputs
and mechanisms ignore the added argument. Reverse transport groups the source
private input with one shared root, using the checked measurable absorption
construction. The sample space and probability measure remain the original
ones. Full mutual independence of the new original inputs is a conclusion
of disjoint grouping, and the pointwise evaluation identity gives equality
of observed laws, including zero-probability observations.

Observed state spaces are finite, as in the manuscript; original latent,
private and sample spaces may be arbitrary. No positivity or c-degree bound
is used. The graph presentation uses the common topological order of the
edge-added DAG. This theorem concerns observational marginal models.
-/

namespace MeraConstraints.Completeness

open MeasureTheory ProbabilityTheory HiddenGraph HiddenGraph.HLP HiddenGraph.Canonicalization

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
  (a b : Fin n) (hab : a < b) [∀ i, MeasurableSpace (val i)]

/-- Original-to-edge-added transport retains exactly the original random
inputs, their probability law, and their full mutual independence. -/
noncomputable def probabilityModel_ignoreEdge (P : ProbabilityModel G val) :
    ProbabilityModel (addEdge G a b hab) val where
  model := ignoreEdge P.model a b hab
  sample := P.sample
  sampleSpace := P.sampleSpace
  inputSpaces := P.inputSpaces
  measure := P.measure
  probability := P.probability
  inputs := P.inputs
  measurableInputs := P.measurableInputs
  independent := P.independent
  measurableMechanisms := by
    letI := P.inputSpaces
    intro i pa
    exact P.measurableMechanisms i (forgetParent i pa)

theorem probabilityModel_ignoreEdge_observed (P : ProbabilityModel G val) :
    (probabilityModel_ignoreEdge G val a b hab P).observed = P.observed := by
  letI := P.sampleSpace
  change MeasureFinite.law P.measure (fun ω => evalInputs (ignoreEdge P.model a b hab)
    (fun x => P.inputs x ω)) = MeasureFinite.law P.measure (fun ω => evalInputs P.model
      (fun x => P.inputs x ω))
  apply congrArg (MeasureFinite.law P.measure)
  funext ω
  exact eval_ignoreEdge P.model a b hab _ _

variable [∀ i, Fintype (val i)] [∀ i, MeasurableSingletonClass (val i)]
  (hLat : ∀ j : Fin ℓ, a ∈ G.children j → b ∈ G.children j)
  (s : Fin ℓ) (hsa : a ∈ G.children s) (hsb : b ∈ G.children s)

/-- Reverse HLP transport constructs a literal original probability model;
its fields contain the derived measurable and independent original inputs. -/
noncomputable def probabilityModel_absorb (P : ProbabilityModel (addEdge G a b hab) val) :
    ProbabilityModel G val := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  exact {
    model := liftedAbsorb P.model hLat s hsa hsb
    sample := P.sample
    sampleSpace := P.sampleSpace
    inputSpaces := fun x => liftedAbsorbInputSpace P.model hLat s hsa hsb x
    measure := P.measure
    probability := P.probability
    inputs := fun x ω => absorptionEncode P.model hLat s hsa hsb (fun y => P.inputs y ω) x
    measurableInputs := absorptionEncode_measurable P.model hLat s hsa hsb P.inputs P.measurableInputs
    independent := absorptionEncode_independent P.model hLat s hsa hsb P.measure
      P.inputs P.measurableInputs P.independent
    measurableMechanisms := liftedAbsorb_mechanisms P.model hLat s hsa hsb P.measurableMechanisms }

theorem probabilityModel_absorb_observed
    (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (P : ProbabilityModel (addEdge G a b hab) val) :
    (probabilityModel_absorb G val a b hab hLat s hsa hsb P).observed = P.observed := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  change MeasureFinite.law P.measure (fun ω => evalInputs (liftedAbsorb P.model hLat s hsa hsb)
    (absorptionEncode P.model hLat s hsa hsb (fun y => P.inputs y ω))) =
      MeasureFinite.law P.measure (fun ω => evalInputs P.model (fun y => P.inputs y ω))
  apply congrArg (MeasureFinite.law P.measure)
  funext ω
  exact eval_absorptionEncode P.model hLat s hsa hsb hpa _

include hLat s hsa hsb

/-- Proposition `prop:hlp`, equality of the original marginal-model classes,
including arbitrary original measurable input spaces and boundary laws. -/
theorem original_model_iff_HLP (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (p : FullAssign val → ℝ) :
    (∃ P : ProbabilityModel G val, P.observed = p) ↔
      ∃ Q : ProbabilityModel (addEdge G a b hab) val, Q.observed = p := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨probabilityModel_ignoreEdge G val a b hab P,
      (probabilityModel_ignoreEdge_observed G val a b hab P).trans hP⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨probabilityModel_absorb G val a b hab hLat s hsa hsb Q,
      (probabilityModel_absorb_observed G val a b hab hLat s hsa hsb hpa Q).trans hQ⟩

/-- Every observed-law constraint is valid on one HLP graph exactly when it
is valid on the other. This makes the manuscript's 'same constraints' precise. -/
theorem constraint_valid_iff_HLP (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (C : (FullAssign val → ℝ) → Prop) :
    (∀ P : ProbabilityModel G val, C P.observed) ↔
      ∀ Q : ProbabilityModel (addEdge G a b hab) val, C Q.observed := by
  constructor
  · intro h Q
    rw [← probabilityModel_absorb_observed G val a b hab hLat s hsa hsb hpa Q]
    exact h _
  · intro h P
    rw [← probabilityModel_ignoreEdge_observed G val a b hab P]
    exact h _

end MeraConstraints.Completeness
