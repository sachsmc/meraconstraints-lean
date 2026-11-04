import MeraConstraints.HiddenGraph.HLPEvaluation
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# Measurable HLP absorption on arbitrary original input spaces

Original input spaces in `ProbabilityModel` are indexed universe lifts.
The wrapper below uses those very spaces as native input types, with only
product and lift measurable structures added. Removing these bookkeeping
lifts gives exactly the already checked absorption mechanisms and evaluation.

At the target vertex the reconstructed source value is random. Since the
observed state space is finite, measurability at every fixed parent assignment
implies measurability after this finite-valued choice of parent assignment.
No finiteness or standard-Borel assumption is placed on original exogenous
spaces. Independence is established separately by disjoint input grouping.
-/

namespace MeraConstraints.HiddenGraph.HLP

open MeasureTheory ProbabilityTheory Canonicalization Measurability

universe u

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {a b : Fin n} {hab : a < b}
  {val : Fin n → Type u} (M : HiddenGraph.SCM.{u,u,u} (addEdge G a b hab) val)
  (hLat : ∀ j : Fin ℓ, a ∈ G.children j → b ∈ G.children j)
  (s : Fin ℓ) (hsa : a ∈ G.children s) (hsb : b ∈ G.children s)

/-- The checked absorption SCM with original lifted input spaces as its
native inputs. Lifts are removed immediately before calling its mechanisms. -/
noncomputable def liftedAbsorb : HiddenGraph.SCM.{u,u,u} G val where
  latentValue := fun j => InputValue M (.inr j) × InputValue M (.inl a)
  latentNonempty := fun j => ⟨ULift.up (Classical.choice (M.latentNonempty j)),
    ULift.up (Classical.choice (M.privateNonempty a))⟩
  privateNoise := fun i => InputValue M (.inl i)
  privateNonempty := fun i => ⟨ULift.up (Classical.choice (M.privateNonempty i))⟩
  F := fun i pa lat ε => (absorb M hLat s hsa hsb).F i pa
    (fun j => ((lat j).1.down, (lat j).2.down)) ε.down

theorem liftedAbsorb_eval (lat : ∀ j, (liftedAbsorb M hLat s hsa hsb).latentValue j)
    (ε : ∀ i, (liftedAbsorb M hLat s hsa hsb).privateNoise i) :
    (liftedAbsorb M hLat s hsa hsb).eval lat ε =
      (absorb M hLat s hsa hsb).eval (fun j => ((lat j).1.down, (lat j).2.down))
        (fun i => (ε i).down) := by
  symm
  apply HiddenGraph.SCM.eval_unique
  intro i
  exact (absorb M hLat s hsa hsb).eval_eq _ _ i

variable [∀ i, MeasurableSpace (val i)] [∀ x, MeasurableSpace (InputValue M x)]

noncomputable instance liftedAbsorbInputSpace (x : Vertex (n := n) (ℓ := ℓ)) :
    MeasurableSpace (InputValue (liftedAbsorb M hLat s hsa hsb) x) := by
  cases x with
  | inl i => change MeasurableSpace (ULift (InputValue M (.inl i))); infer_instance
  | inr j => change MeasurableSpace (ULift (InputValue M (.inr j) × InputValue M (.inl a))); infer_instance

variable [∀ i, Fintype (val i)] [∀ i, MeasurableSingletonClass (val i)]

theorem liftedAbsorb_mechanisms (hM : MechanismsMeasurable M) :
    MechanismsMeasurable (liftedAbsorb M hLat s hsa hsb) := by
  classical
  let N := liftedAbsorb M hLat s hsa hsb
  letI (i : Fin n) : MeasurableSpace (N.privateNoise i) :=
    (inferInstance : MeasurableSpace (InputValue M (.inl i)))
  letI (j : Fin ℓ) : MeasurableSpace (N.latentValue j) :=
    (inferInstance : MeasurableSpace (InputValue M (.inr j) × InputValue M (.inl a)))
  have hL (i : Fin n) : Measurable (fun t : MechanismInput N i =>
      fun j : {j : Fin ℓ // i ∈ G.children j} => (t.1 j).down.1) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_fst.comp (measurable_down.comp ((measurable_pi_apply j).comp measurable_fst))
  have hP (i : Fin n) : Measurable (fun t : MechanismInput N i =>
      (t.2.down : InputValue M (.inl i))) :=
    (measurable_down : Measurable (ULift.down : ULift (InputValue M (.inl i)) →
      InputValue M (.inl i))).comp measurable_snd
  have hS (i : Fin n) (hsi : i ∈ G.children s) :
      Measurable (fun t : MechanismInput N i => (t.1 ⟨s, hsi⟩).down.2) :=
    measurable_snd.comp (measurable_down.comp ((measurable_pi_apply
      (⟨s, hsi⟩ : {j : Fin ℓ // i ∈ G.children j})).comp measurable_fst))
  intro i pa
  by_cases hia : i = a
  · subst i
    have h := (hM a (PaAssign.restrict (parentWitness M a pa) a)).comp ((hL a).prodMk (hS a hsa))
    simpa only [Function.comp_def, N, liftedAbsorb, absorb, dite_true, ite_true] using h
  · by_cases hib : i = b
    · subst i
      let z := parentWitness M b pa
      have hLA : Measurable (fun t : MechanismInput N b =>
          fun j : {j : Fin ℓ // a ∈ G.children j} => (t.1 ⟨j, hLat j j.property⟩).down.1) := by
        apply measurable_pi_iff.mpr
        intro j
        exact measurable_fst.comp (measurable_down.comp
          ((measurable_pi_apply (⟨j, hLat j j.property⟩ :
            {k : Fin ℓ // b ∈ G.children k})).comp measurable_fst))
      let va := fun t : MechanismInput N b => M.F a (PaAssign.restrict z a)
        (fun j => (t.1 ⟨j, hLat j j.property⟩).down.1.down) (t.1 ⟨s, hsb⟩).down.2.down
      have hva : Measurable va := (hM a _).comp (hLA.prodMk (hS b hsb))
      let f := fun x : val a => fun t : MechanismInput N b =>
        M.F b (PaAssign.restrict (Function.update z a x) b)
          (fun j => (t.1 j).down.1.down) t.2.down.down
      have hf (x : val a) : Measurable (f x) := (hM b _).comp ((hL b).prodMk (hP b))
      have hselect : Measurable (fun t : MechanismInput N b => f (va t) t) :=
        (measurable_from_prod_countable_left
          (f := fun z : MechanismInput N b × val a => f z.2 z.1) hf).comp (measurable_id.prodMk hva)
      simpa only [Function.comp_def, N, f, va, z, liftedAbsorb, absorb, dif_neg hia, dite_true] using hselect
    · have h := (hM i (PaAssign.restrict (parentWitness M i pa) i)).comp ((hL i).prodMk (hP i))
      simpa only [Function.comp_def, N, liftedAbsorb, absorb, dif_neg hia, dif_neg hib] using h

end MeraConstraints.HiddenGraph.HLP
