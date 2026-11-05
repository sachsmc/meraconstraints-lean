import MeraConstraints.HiddenGraph.HLPInputs

/-!
# Proposition 5 (`prop:hlp`): adding an edge

Adding the edge `a → b` to a graph, when `Pa(a) ⊆ Pa(b)` and `a` and `b` share an
unobserved parent, does not change the marginal model.

To go from `G` to the graph with the edge, keep the unobserved inputs and let the
mechanism of `b` ignore the new parent `a`. To go back, group the private noise of
`a` with the shared unobserved variable into one input. Grouping disjoint inputs
keeps them mutually independent, and the observed distribution is unchanged. The
sample space and probability measure stay the same in both directions.

The observed variables are finite, as in the manuscript; the unobserved inputs
and the sample space may be arbitrary. Distributions with zero probabilities are
included. There are no positivity or c-degree assumptions.
-/

namespace MeraConstraints.Completeness

open MeasureTheory ProbabilityTheory HiddenGraph HiddenGraph.HLP HiddenGraph.Canonicalization

universe u

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type u)
  (a b : Fin n) (hab : a < b) [∀ i, MeasurableSpace (val i)]

/-- A model on `G` gives a model on the graph with the edge `a → b`: the inputs and
their joint distribution are unchanged, and the mechanism of `b` ignores `a`. -/
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

/-- A model on the graph with the edge `a → b` gives a model on `G`: the private
noise of `a` is grouped with the input of the shared unobserved variable `s`. -/
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

/-- Proposition 5 (`prop:hlp`): the graph with and without the edge `a → b` have
the same marginal model. Inputs may be in arbitrary measurable spaces, and
distributions with zero probabilities are included. -/
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

/-- A constraint on the observed distribution holds on the marginal model of one
graph exactly when it holds on that of the other. So the two graphs have the same
constraints. -/
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
