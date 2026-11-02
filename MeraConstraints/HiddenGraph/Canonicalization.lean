import MeraConstraints.HiddenGraph.Model
import MeraConstraints.GlobalModel
import MeraConstraints.Probability.IndependentMap

/-!
# Canonicalizing a finite-input original SCM

This chapter proves the probability-law direction of the response-variable
transformation from an actual parent-restricted `HiddenGraph.SCM`. Its inputs
are the latent roots together with every observed vertex's private disturbance.
The source law is the product of their original coordinate laws. In particular,
mutual independence is a premise about the original inputs, and is not imposed
on the response profiles after their construction.

Group the original inputs by their actual graph district. A mechanism may
read only its own private disturbance and its listed latent parents; all of
these belong to its district. It therefore induces a response profile from
the inputs of that district alone. The district profile law is defined as
the pushforward of the **original local input law** along that map.

Disjoint regrouping and coordinatewise pushforward transport the original
product law to the product of these derived district profile laws. The
pointwise response-reduction theorem then gives equality of the generated
observed laws. The profile representation is proved, not assumed.

The necessity construction works at **any c-degree**. At higher c-degree its
derived profile laws need not range over every simplex point; unrestricted
profile-law sufficiency is specific to the earlier c-degree-one realization.

The probability proof here assumes finite original input spaces. The maps and
the deterministic reduction do not. Universe lifts permit latent and private
input types to occupy different Lean universes; evaluation immediately removes
these lifts, so they change neither input values nor probability masses.
-/

namespace MeraConstraints.HiddenGraph.Canonicalization

universe u v w

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type u}
  (M : HiddenGraph.SCM.{u, v, w} G val)

/-- One coordinate per original private disturbance (`inl`) or latent root
(`inr`). Lifts place the two possibly different input universes together. -/
def InputValue : HiddenGraph.Vertex (n := n) (ℓ := ℓ) → Type (max v w)
  | .inl i => ULift.{v} (M.privateNoise i)
  | .inr j => ULift.{w} (M.latentValue j)

abbrev InputAssignment := ∀ x, InputValue M x

/-- The indexed lifted input tuple is just the native latent/private tuple.
Both directions are explicit; the universe lifts carry no extra information. -/
def nativeInputEquiv : InputAssignment M ≃
    ((∀ j, M.latentValue j) × (∀ i, M.privateNoise i)) where
  toFun a := (fun j => (a (.inr j)).down, fun i => (a (.inl i)).down)
  invFun a x := match x with
    | .inl i => ULift.up (a.2 i)
    | .inr j => ULift.up (a.1 j)
  left_inv a := by
    funext x
    cases x <;> rfl
  right_inv a := by
    cases a
    rfl

/-- Ordinary original latent/private masses, copied to the universe-lifted
coordinate types. No values are identified and no probabilities change. -/
def inputMass (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ) : ∀ x, InputValue M x → ℝ
  | .inl i, a => privateMass i a.down
  | .inr j, a => latentMass j a.down

abbrev LocalInput (d : HiddenGraph.DistrictId G) :=
  ∀ x : {x : HiddenGraph.Vertex (n := n) (ℓ := ℓ) // HiddenGraph.districtOf G x = d},
    InputValue M x

abbrev ResponseProfile (_M : HiddenGraph.SCM.{u, v, w} G val)
    (d : HiddenGraph.DistrictId G) :=
  GlobalModel.Profile G.observed val (HiddenGraph.observedDistrict G) d

/-- Restriction to the original inputs in one district. -/
def restrictInput (a : InputAssignment M) (d : HiddenGraph.DistrictId G) :
    LocalInput M d := fun x => a x

private theorem latent_parent_in_district (d : HiddenGraph.DistrictId G)
    (i : {i : Fin n // HiddenGraph.observedDistrict G i = d})
    (j : {j : Fin ℓ // i.val ∈ G.children j}) :
    HiddenGraph.districtOf G (.inr j.val) = d :=
  ((HiddenGraph.districtOf_eq_iff G _ _).2
    (HiddenGraph.connected_child G j i j.property)).trans i.property

/-- The actual structural mechanisms induce a local response profile from
only the original inputs belonging to that district. No other input is read. -/
def localProfile (d : HiddenGraph.DistrictId G) (a : LocalInput M d) :
    ResponseProfile M d :=
  fun i pa => M.F i pa
    (fun j => (a ⟨.inr j, latent_parent_in_district d i j⟩).down)
    ((a ⟨.inl i, i.property⟩).down)

/-- The complete profile tuple produced from the actual original input tuple. -/
def canonicalProfiles (a : InputAssignment M) : ∀ d, ResponseProfile M d :=
  fun d => localProfile M d (restrictInput M a d)

/-- Local reduction, followed by assembly, is the original response assignment.
Parent membership and district membership were enforced by `localProfile`. -/
theorem assemble_canonicalProfiles (a : InputAssignment M) :
    GlobalModel.assemble G.observed val (HiddenGraph.observedDistrict G)
      (canonicalProfiles M a) =
      M.responseProfile (fun j => (a (.inr j)).down) (fun i => (a (.inl i)).down) := rfl

/-- Evaluate the original SCM at its complete original input tuple. -/
def evalInputs (a : InputAssignment M) : FullAssign val :=
  M.eval (fun j => (a (.inr j)).down) (fun i => (a (.inl i)).down)

theorem evalInputs_eq_assembled (a : InputAssignment M) :
    evalInputs M a = evalR
      (GlobalModel.assemble G.observed val (HiddenGraph.observedDistrict G)
        (canonicalProfiles M a)) := by
  unfold evalInputs
  rw [HiddenGraph.SCM.eval_eq_evalR, assemble_canonicalProfiles]

variable [∀ j, Fintype (M.latentValue j)] [∀ i, Fintype (M.privateNoise i)]

instance inputValueFintype (x : HiddenGraph.Vertex (n := n) (ℓ := ℓ)) :
    Fintype (InputValue M x) := by
  cases x <;> dsimp [InputValue] <;> infer_instance

theorem inputMass_mem_stdSimplex
    (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ)
    (hlatent : ∀ j, latentMass j ∈ stdSimplex ℝ (M.latentValue j))
    (hprivate : ∀ i, privateMass i ∈ stdSimplex ℝ (M.privateNoise i))
    (x : HiddenGraph.Vertex (n := n) (ℓ := ℓ)) :
    inputMass M latentMass privateMass x ∈ stdSimplex ℝ (InputValue M x) := by
  cases x with
  | inl i =>
      refine ⟨fun a => (hprivate i).1 a.down, ?_⟩
      change (∑ a : ULift.{v} (M.privateNoise i), privateMass i a.down) = 1
      exact ((Equiv.ulift : ULift.{v} (M.privateNoise i) ≃ M.privateNoise i).sum_comp _).trans
        (hprivate i).2
  | inr j =>
      refine ⟨fun a => (hlatent j).1 a.down, ?_⟩
      change (∑ a : ULift.{w} (M.latentValue j), latentMass j a.down) = 1
      exact ((Equiv.ulift : ULift.{w} (M.latentValue j) ≃ M.latentValue j).sum_comp _).trans
        (hlatent j).2

omit [∀ j, Fintype (M.latentValue j)] [∀ i, Fintype (M.privateNoise i)] in
/-- The original coordinate product mass is unchanged by encoding the native
tuple as a family over the observed/latent disjoint union. -/
theorem joint_inputMass_eq_native
    (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ) (a : InputAssignment M) :
    Independent.joint (inputMass M latentMass privateMass) a =
      prodDist (Independent.joint latentMass) (Independent.joint privateMass)
        (nativeInputEquiv M a) := by
  simp only [Independent.joint, Fintype.prod_sum_type, inputMass, prodDist, nativeInputEquiv]
  exact mul_comm _ _

variable [DecidableEq (HiddenGraph.DistrictId G)]

/-- The original local input law, formed from the original coordinate masses
of the roots and private disturbances belonging to this district. -/
def districtInputLaw (μ : ∀ x, InputValue M x → ℝ)
    (d : HiddenGraph.DistrictId G) : LocalInput M d → ℝ :=
  Independent.joint (fun x => μ x.val)

theorem districtInputLaw_mem_stdSimplex (μ : ∀ x, InputValue M x → ℝ)
    (hμ : ∀ x, μ x ∈ stdSimplex ℝ (InputValue M x)) (d : HiddenGraph.DistrictId G) :
    districtInputLaw M μ d ∈ stdSimplex ℝ (LocalInput M d) :=
  Independent.joint_mem_stdSimplex _ (fun x => hμ x.val)

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The canonical district law is derived by pushing forward the original
inputs, rather than introduced as an unrestricted profile-law premise. -/
def canonicalLaw (μ : ∀ x, InputValue M x → ℝ) (d : HiddenGraph.DistrictId G) :
    ResponseProfile M d → ℝ :=
  pushforward (localProfile M d) (districtInputLaw M μ d)

theorem canonicalLaw_mem_stdSimplex (μ : ∀ x, InputValue M x → ℝ)
    (hμ : ∀ x, μ x ∈ stdSimplex ℝ (InputValue M x)) (d : HiddenGraph.DistrictId G) :
    canonicalLaw M μ d ∈ stdSimplex ℝ (ResponseProfile M d) :=
  pushforward_mem_stdSimplex _ _ (districtInputLaw_mem_stdSimplex M μ hμ d)

/-- Canonicalization preserves mutual district independence by transporting
the original product law through disjoint grouping and the local profile maps. -/
theorem canonicalProfiles_law (μ : ∀ x, InputValue M x → ℝ) :
    pushforward (canonicalProfiles M) (Independent.joint μ) =
      Independent.joint (canonicalLaw M μ) := by
  classical
  exact Independent.pushforward_grouped (HiddenGraph.districtOf G)
    (InputValue M) (localProfile M) μ

/-- The observed law generated by the original SCM under mutually independent
original inputs. This is defined using `M.eval`, not a canonical profile model. -/
def observedLaw (μ : ∀ x, InputValue M x → ℝ) : FullAssign val → ℝ :=
  pushforward (evalInputs M) (Independent.joint μ)

/-- The actual observed law on the original, unlifted latent/private types:
evaluate `M` under the product of all original input coordinate masses. -/
def nativeObservedLaw (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ) : FullAssign val → ℝ :=
  pushforward (fun a => M.eval a.1 a.2)
    (prodDist (Independent.joint latentMass) (Independent.joint privateMass))

omit [DecidableEq (HiddenGraph.DistrictId G)] [∀ i, Fintype (val i)] in
/-- The indexed encoding and the literal native SCM input law produce the
same observed distribution. This uses an input-tuple equivalence, not a
causal or independence assumption about the resulting response profiles. -/
theorem observedLaw_inputMass_eq_native
    (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ) :
    observedLaw M (inputMass M latentMass privateMass) =
      nativeObservedLaw M latentMass privateMass := by
  classical
  funext b
  unfold observedLaw nativeObservedLaw pushforward
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (nativeInputEquiv M)
  intro a
  change (if evalInputs M a = b then Independent.joint (inputMass M latentMass privateMass) a else 0) =
    if evalInputs M a = b then
      prodDist (Independent.joint latentMass) (Independent.joint privateMass) (nativeInputEquiv M a)
    else 0
  rw [joint_inputMass_eq_native]

omit [DecidableEq (HiddenGraph.DistrictId G)] in
theorem nativeObservedLaw_mem_stdSimplex
    (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ)
    (hlatent : ∀ j, latentMass j ∈ stdSimplex ℝ (M.latentValue j))
    (hprivate : ∀ i, privateMass i ∈ stdSimplex ℝ (M.privateNoise i)) :
    nativeObservedLaw M latentMass privateMass ∈ stdSimplex ℝ (FullAssign val) :=
  pushforward_mem_stdSimplex _ _ (prodDist_mem_stdSimplex _ _
    (Independent.joint_mem_stdSimplex _ hlatent) (Independent.joint_mem_stdSimplex _ hprivate))

omit [DecidableEq (HiddenGraph.DistrictId G)] in
theorem observedLaw_mem_stdSimplex (μ : ∀ x, InputValue M x → ℝ)
    (hμ : ∀ x, μ x ∈ stdSimplex ℝ (InputValue M x)) :
    observedLaw M μ ∈ stdSimplex ℝ (FullAssign val) :=
  pushforward_mem_stdSimplex _ _ (Independent.joint_mem_stdSimplex μ hμ)

/-- Probability-law faithfulness of finite-input response canonicalization.
The district laws on the right were constructed from the given original SCM
and its given independent input laws. No c-degree restriction is needed. -/
theorem observedLaw_eq_globalModel (μ : ∀ x, InputValue M x → ℝ) :
    observedLaw M μ =
      GlobalModel.observed G.observed val (HiddenGraph.observedDistrict G) (canonicalLaw M μ) := by
  classical
  unfold observedLaw GlobalModel.observed
  rw [← canonicalProfiles_law M μ, FiniteProbability.pushforward_comp]
  apply congrArg (fun f => pushforward f (Independent.joint μ))
  funext a
  exact evalInputs_eq_assembled M a

/-- Every finite-input original SCM with independent input laws has derived
simplex-valued district profile laws reproducing its observed distribution.
This is necessity, and does not require c-degree one. -/
theorem exists_canonicalLaws (μ : ∀ x, InputValue M x → ℝ)
    (hμ : ∀ x, μ x ∈ stdSimplex ℝ (InputValue M x)) :
    ∃ q : ∀ d, ResponseProfile M d → ℝ,
      (∀ d, q d ∈ stdSimplex ℝ (ResponseProfile M d)) ∧
      observedLaw M μ = GlobalModel.observed G.observed val
        (HiddenGraph.observedDistrict G) q :=
  ⟨canonicalLaw M μ, canonicalLaw_mem_stdSimplex M μ hμ,
    observedLaw_eq_globalModel M μ⟩

/-- Native-input version of probability-law faithfulness. The right-hand
profile laws are computed from the original native latent/private masses. -/
theorem nativeObservedLaw_eq_globalModel
    (latentMass : ∀ j, M.latentValue j → ℝ)
    (privateMass : ∀ i, M.privateNoise i → ℝ) :
    nativeObservedLaw M latentMass privateMass =
      GlobalModel.observed G.observed val (HiddenGraph.observedDistrict G)
        (canonicalLaw M (inputMass M latentMass privateMass)) := by
  rw [← observedLaw_inputMass_eq_native]
  exact observedLaw_eq_globalModel M _

/-- The original SCM law factors into the induced district structural-event
masses. Identifying these factors from observations is a separate theorem. -/
theorem observedLaw_eq_prod_factor (μ : ∀ x, InputValue M x → ℝ)
    (a : FullAssign val) :
    observedLaw M μ a = ∏ d, GlobalModel.factor G.observed val
      (HiddenGraph.observedDistrict G) (canonicalLaw M μ) d a := by
  rw [observedLaw_eq_globalModel]
  exact GlobalModel.observed_eq_prod_factor _ _ _ _ a

end MeraConstraints.HiddenGraph.Canonicalization
