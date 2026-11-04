import MeraConstraints.HiddenGraph.RootProbabilityModel

/-!
# Measurable independent-input transport from split to original

The common D input is grouped only with one selected anchor root. Other roots
receive their own C input and an ignored constant common component. Private
inputs keep their own groups. Disjoint grouping proves full mutual independence
of the actual original inputs; no random common input is duplicated.

The recovered permitted-root map and all bundled mechanisms are measurable.
The previously checked pointwise evaluation identity supplies observed-law
preservation on the source model's own arbitrary sample space.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe u

variable {n : ℕ} {K J : Type u} [Fintype K] [Fintype J] [DecidableEq K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) {val : Fin n → Type u}
  (M : RootSCM.{u,u,u,u} (splitGraph A C D other) val)
  [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

instance bundledRootMeasurableSpace (r : K ⊕ J) : MeasurableSpace (bundledRootValue A C D other M r) := by
  cases r <;> dsimp [bundledRootValue] <;> infer_instance

instance bundledModelRootMeasurableSpace (anchor : K) (r : K ⊕ J) :
    MeasurableSpace ((bundledModel A C D other M anchor).rootValue r) := bundledRootMeasurableSpace A C D other M r

instance bundledModelPrivateMeasurableSpace (anchor : K) (i : Fin n) :
    MeasurableSpace ((bundledModel A C D other M anchor).privateNoise i) :=
  show MeasurableSpace (M.privateNoise i) from inferInstance

def bundlingBlock (anchor : K) : ((Option K ⊕ J) ⊕ Fin n) → ((K ⊕ J) ⊕ Fin n)
  | .inl (.inl none) => .inl (.inl anchor)
  | .inl (.inl (some k)) => .inl (.inl k)
  | .inl (.inr j) => .inl (.inr j)
  | .inr i => .inr i

abbrev BundlingGroup (anchor : K) (t : (K ⊕ J) ⊕ Fin n) :=
  ∀ s : {s // bundlingBlock (J := J) (n := n) anchor s = t}, M.InputValue s.val

def bundlingGroupMap (anchor : K) (constant : M.rootValue (.inl none)) (t : (K ⊕ J) ⊕ Fin n) :
    BundlingGroup A C D other M anchor t → (bundledModel A C D other M anchor).InputValue t := by
  cases t with
  | inl r => cases r with
    | inl k =>
      intro z
      exact (z ⟨.inl (.inl (some k)), rfl⟩,
        if hk : k = anchor then z ⟨.inl (.inl none), by simp [bundlingBlock, hk]⟩ else constant)
    | inr j => exact fun z => z ⟨.inl (.inr j), rfl⟩
  | inr i => exact fun z => z ⟨.inr i, rfl⟩

def bundleEncode (anchor : K) (constant : M.rootValue (.inl none)) (x : M.NativeInputs) :
    (bundledModel A C D other M anchor).NativeInputs :=
  (encodeSplitInputs A C D other M anchor constant x.1, x.2)

omit [Fintype K] [Fintype J] [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)] in
theorem bundlingGroupMap_apply (anchor : K) (constant : M.rootValue (.inl none))
    (t : (K ⊕ J) ⊕ Fin n) (x : M.NativeInputs) :
    bundlingGroupMap A C D other M anchor constant t (fun s => M.input x s.val) =
      (bundledModel A C D other M anchor).input (bundleEncode A C D other M anchor constant x) t := by
  cases t with
  | inl r => cases r with
    | inl k => by_cases hk : k = anchor <;> simp [bundlingGroupMap, RootSCM.input, bundleEncode, encodeSplitInputs, hk]
    | inr j => rfl
  | inr i => rfl

omit [Fintype K] [Fintype J] in
theorem bundlingGroupMap_measurable (anchor : K) (constant : M.rootValue (.inl none))
    (t : (K ⊕ J) ⊕ Fin n) : Measurable (bundlingGroupMap A C D other M anchor constant t) := by
  cases t with
  | inl r => cases r with
    | inl k =>
      change Measurable (fun z : BundlingGroup A C D other M anchor (.inl (.inl k)) =>
        (z ⟨.inl (.inl (some k)), rfl⟩,
          if hk : k = anchor then z ⟨.inl (.inl none), by simp [bundlingBlock, hk]⟩ else constant))
      apply Measurable.prodMk (measurable_pi_apply _)
      split_ifs with hk
      · exact measurable_pi_apply _
      · exact measurable_const
    | inr j => exact measurable_pi_apply _
  | inr i => exact measurable_pi_apply _

omit [Fintype K] [Fintype J] in
theorem bundleEncode_measurable (anchor : K) (constant : M.rootValue (.inl none)) :
    Measurable (bundleEncode A C D other M anchor constant) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro r
    cases r with
    | inl k =>
      change Measurable (fun x : M.NativeInputs =>
        (x.1 (.inl (some k)), if k = anchor then x.1 (.inl none) else constant))
      apply Measurable.prodMk ((measurable_pi_apply (Sum.inl (some k) : Option K ⊕ J)).comp measurable_fst)
      split_ifs with hk
      · exact (measurable_pi_apply (Sum.inl none : Option K ⊕ J)).comp measurable_fst
      · exact measurable_const
    | inr j => exact (measurable_pi_apply (Sum.inr j : Option K ⊕ J)).comp measurable_fst
  · exact measurable_snd

theorem bundleEncode_independent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → M.NativeInputs) (hX : Measurable X)
    (hInd : iIndepFun (fun t ω => M.input (X ω) t) μ)
    (anchor : K) (constant : M.rootValue (.inl none)) :
    iIndepFun (fun t ω => (bundledModel A C D other M anchor).input
      (bundleEncode A C D other M anchor constant (X ω)) t) μ := by
  classical
  have hg := Independent.iIndepFun_grouped (bundlingBlock (J := J) (n := n) anchor) (M.InputValue) μ
    (fun t ω => M.input (X ω) t) (fun t => (M.input_measurable t).comp hX) hInd
  have hi := hg.comp (bundlingGroupMap A C D other M anchor constant)
    (bundlingGroupMap_measurable A C D other M anchor constant)
  simpa only [Function.comp_def, bundlingGroupMap_apply] using hi

omit [Fintype K] [Fintype J] [DecidableEq K] [∀ i, MeasurableSpace (M.privateNoise i)] in
theorem recoverLocalInputs_measurable (anchor : K) (i : Fin n) :
    Measurable (recoverLocalInputs A C D other M anchor i) := by
  apply measurable_pi_iff.mpr
  intro r
  rcases r with ⟨r, hr⟩
  cases r with
  | inl k => cases k with
    | none => exact (measurable_pi_apply (⟨.inl anchor, Finset.mem_union.mpr (Or.inr hr)⟩ :
        {r // i ∈ (originalGraph A C D other).children r})).snd
    | some k => exact (measurable_pi_apply (⟨.inl k, Finset.mem_union.mpr (Or.inl hr)⟩ :
        {r // i ∈ (originalGraph A C D other).children r})).fst
  | inr j =>
    exact measurable_pi_apply (⟨.inr j, hr⟩ : {r // i ∈ (originalGraph A C D other).children r})

variable [∀ i, MeasurableSpace (val i)]

omit [Fintype K] [Fintype J] [DecidableEq K] in
theorem bundledModel_mechanismsMeasurable (hF : M.MechanismsMeasurable) (anchor : K) :
    (bundledModel A C D other M anchor).MechanismsMeasurable := by
  intro i
  exact (hF i).comp (measurable_fst.prodMk
    (((recoverLocalInputs_measurable A C D other M anchor i).comp measurable_snd.fst).prodMk measurable_snd.snd))

end MeraConstraints.HiddenGraph.StrongFaceSplitting
