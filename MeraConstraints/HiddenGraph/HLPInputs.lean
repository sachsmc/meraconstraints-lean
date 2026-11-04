import MeraConstraints.HiddenGraph.HLPMeasure

/-!
# HLP input grouping preserves full mutual independence

Only the source private input moves: it joins the chosen shared root's
group. Every other original input stays in its own group. The now-empty
source-private group produces a constant, and extra coordinates at other
roots are constants. Thus no nonconstant random input is duplicated between
groups. Measurable local maps of these disjoint groups give the actual inputs
of the lifted absorption model, with full mutual independence derived from
the original family. All original state spaces may be infinite.
-/

namespace MeraConstraints.HiddenGraph.HLP

open MeasureTheory ProbabilityTheory Canonicalization

universe u

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {a b : Fin n} {hab : a < b}
  {val : Fin n → Type u} (M : HiddenGraph.SCM.{u,u,u} (addEdge G a b hab) val)
  (hLat : ∀ j : Fin ℓ, a ∈ G.children j → b ∈ G.children j)
  (s : Fin ℓ) (hsa : a ∈ G.children s) (hsb : b ∈ G.children s)

def absorptionBlock : Vertex (n := n) (ℓ := ℓ) → Vertex (n := n) (ℓ := ℓ)
  | .inl i => if i = a then .inr s else .inl i
  | .inr j => .inr j

abbrev AbsorptionGroup (x : Vertex (n := n) (ℓ := ℓ)) :=
  ∀ y : {y : Vertex (n := n) (ℓ := ℓ) // absorptionBlock (a := a) s y = x}, InputValue M y

/-- The actual new input uses only its own disjoint group. -/
noncomputable def absorptionGroupMap (x : Vertex (n := n) (ℓ := ℓ)) :
    AbsorptionGroup M s x → InputValue (liftedAbsorb M hLat s hsa hsb) x := by
  cases x with
  | inl i =>
    intro z
    exact ULift.up (if hi : i = a then ULift.up (Classical.choice (M.privateNonempty i))
      else z ⟨.inl i, by simp [absorptionBlock, hi]⟩)
  | inr j =>
    intro z
    exact ULift.up (z ⟨.inr j, rfl⟩,
      if hj : j = s then z ⟨.inl a, by simp [absorptionBlock, hj]⟩
      else ULift.up (Classical.choice (M.privateNonempty a)))

noncomputable def absorptionEncode (X : InputAssignment M) :
    InputAssignment (liftedAbsorb M hLat s hsa hsb) :=
  fun x => absorptionGroupMap M hLat s hsa hsb x (fun y => X y.val)

variable [∀ i, MeasurableSpace (val i)] [∀ x, MeasurableSpace (InputValue M x)]

omit [∀ i, MeasurableSpace (val i)] in
theorem absorptionGroupMap_measurable (x : Vertex (n := n) (ℓ := ℓ)) :
    Measurable (absorptionGroupMap M hLat s hsa hsb x) := by
  classical
  cases x with
  | inl i =>
    change Measurable (fun z : AbsorptionGroup M s (.inl i) =>
      (ULift.up (if hi : i = a then ULift.up (Classical.choice (M.privateNonempty i))
        else z ⟨.inl i, by simp [absorptionBlock, hi]⟩) : ULift (InputValue M (.inl i))))
    by_cases hi : i = a
    · simp only [dif_pos hi]
      exact measurable_const
    · simpa only [Function.comp_def, dif_neg hi] using measurable_up.comp
        (measurable_pi_apply (⟨.inl i, by simp [absorptionBlock, hi]⟩ :
          {y : Vertex (n := n) (ℓ := ℓ) // absorptionBlock (a := a) s y = .inl i}))
  | inr j =>
    change Measurable (fun z : AbsorptionGroup M s (.inr j) =>
      (ULift.up (z ⟨.inr j, rfl⟩,
        if hj : j = s then z ⟨.inl a, by simp [absorptionBlock, hj]⟩
        else ULift.up (Classical.choice (M.privateNonempty a))) :
          ULift (InputValue M (.inr j) × InputValue M (.inl a))))
    apply measurable_up.comp
    apply Measurable.prodMk (measurable_pi_apply (⟨.inr j, rfl⟩ :
      {y : Vertex (n := n) (ℓ := ℓ) // absorptionBlock (a := a) s y = .inr j}))
    by_cases hj : j = s
    · simpa only [dif_pos hj] using
        (measurable_pi_apply (⟨.inl a, by simp [absorptionBlock, hj]⟩ :
          {y : Vertex (n := n) (ℓ := ℓ) // absorptionBlock (a := a) s y = .inr j}))
    · simp only [dif_neg hj]
      exact measurable_const

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

omit [∀ i, MeasurableSpace (val i)] in
theorem absorptionEncode_measurable (X : ∀ x, Ω → InputValue M x)
    (hX : ∀ x, Measurable (X x)) (x : Vertex (n := n) (ℓ := ℓ)) :
    Measurable (fun ω => absorptionEncode M hLat s hsa hsb (fun y => X y ω) x) :=
  (absorptionGroupMap_measurable M hLat s hsa hsb x).comp
    (measurable_pi_iff.mpr fun y => hX y.val)

omit [∀ i, MeasurableSpace (val i)] in
theorem absorptionEncode_independent (X : ∀ x, Ω → InputValue M x)
    (hX : ∀ x, Measurable (X x)) (hInd : iIndepFun X μ) :
    iIndepFun (fun x ω => absorptionEncode M hLat s hsa hsb (fun y => X y ω) x) μ := by
  have hg := Independent.iIndepFun_grouped (absorptionBlock (a := a) s) (InputValue M) μ X hX hInd
  exact hg.comp (absorptionGroupMap M hLat s hsa hsb)
    (absorptionGroupMap_measurable M hLat s hsa hsb)

omit [∀ i, MeasurableSpace (val i)] [∀ x, MeasurableSpace (InputValue M x)] in
/-- Native inputs after erasing the wrapper lifts are precisely the checked
`absorbLatents` / `absorbPrivate` encoding of the original inputs. -/
theorem eval_absorptionEncode (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (X : InputAssignment M) :
    evalInputs (liftedAbsorb M hLat s hsa hsb) (absorptionEncode M hLat s hsa hsb X) =
      evalInputs M X := by
  classical
  let u := fun j => (X (.inr j)).down
  let ε := fun i => (X (.inl i)).down
  have hL : (fun j =>
      (((absorptionEncode M hLat s hsa hsb X (.inr j)).down).1.down,
       ((absorptionEncode M hLat s hsa hsb X (.inr j)).down).2.down)) =
      absorbLatents M s u ε := by
    funext j
    by_cases hj : j = s <;> simp [absorptionEncode, absorptionGroupMap, absorbLatents, hj, u, ε]
  have hP : (fun i => (absorptionEncode M hLat s hsa hsb X (.inl i)).down.down) =
      absorbPrivate M ε := by
    funext i
    by_cases hi : i = a <;> simp [absorptionEncode, absorptionGroupMap, absorbPrivate, hi, ε]
  change (liftedAbsorb M hLat s hsa hsb).eval _ _ = M.eval u ε
  rw [liftedAbsorb_eval, hL, hP, eval_absorb M hpa hLat s hsa hsb]

end MeraConstraints.HiddenGraph.HLP
