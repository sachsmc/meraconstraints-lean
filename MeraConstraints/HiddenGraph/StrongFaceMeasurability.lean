import MeraConstraints.HiddenGraph.StrongFaceSupport
import MeraConstraints.HiddenGraph.RootMeasurability

/-!
# The split model has measurable mechanisms

The acceptance event of `StrongFaceSupport` concerns evaluations of the original
model. A mechanism of `replayModel` at a vertex in `D` must instead be defined for
every value of its arguments, including observed parent values that no original
input produces, and streams with no accepted candidate. This chapter shows that
the local test and the selection of the first accepted candidate are jointly
measurable in all these arguments (`localFirstReplay_measurable`), including the
fallback. The test reads only the unobserved inputs available by the proposition's second numbered condition and the
observed values available by its first.

If the original mechanisms are measurable, composition shows that every mechanism
of `replayModel` is measurable (`replayModel_mechanismsMeasurable`), and hence so is
its evaluation (`replayModel_eval_measurable`). The observed variables may take
countably many values with measurable singletons; the unobserved and private input
spaces are arbitrary measurable spaces.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)
  [∀ i, MeasurableSpace (val i)]
  [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

instance replayRootValueMeasurableSpace (r : Option K ⊕ J) :
    MeasurableSpace (replayRootValue A C D other M r) := by
  cases r with
  | inl k => cases k <;> dsimp [replayRootValue] <;> infer_instance
  | inr j => dsimp [replayRootValue]; infer_instance

include h in
instance replayModelRootValueMeasurableSpace (r : Option K ⊕ J) :
    MeasurableSpace ((replayModel A C D other h M).rootValue r) :=
  replayRootValueMeasurableSpace A C D other M r

include h in
instance replayModelPrivateMeasurableSpace (i : Fin n) :
    MeasurableSpace ((replayModel A C D other h M).privateNoise i) :=
  show MeasurableSpace (M.privateNoise i) from inferInstance

abbrev SplitRootArgs (i : Fin n) :=
  ∀ r : {r // i ∈ (splitGraph A C D other).children r}, replayRootValue A C D other M r.val

abbrev LocalReplayContext (i : Fin n) := PaAssign A val i × SplitRootArgs A C D other M i

omit [Fintype K] [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)] in
theorem replayWitness_measurable (d : Fin n) : Measurable (replayWitness A C D other M d) := by
  classical
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j ∈ A.parents d
  · simpa only [replayWitness, dif_pos hj] using
      (measurable_pi_apply (⟨j, hj⟩ : {j // j ∈ A.parents d}))
  · simp only [replayWitness, dif_neg hj]
    exact measurable_const

include h in
omit [∀ i, MeasurableSpace (val i)] in
theorem checkerRootInputs_measurable (d : Fin n) (hd : d ∈ D) (c : Fin n) (hc : c ∈ unionC C) :
    Measurable (fun z : ReplayCandidate A C D other M × SplitRootArgs A C D other M d =>
      checkerRootInputs A C D other h M d hd c hc z.1 z.2) := by
  classical
  apply measurable_pi_iff.mpr
  intro r
  rcases r with ⟨k | j, hr⟩
  · exact (measurable_pi_apply (Sum.inl k : K ⊕ J)).comp measurable_fst.fst
  · by_cases hj : other j ⊆ unionC C
    · simpa only [checkerRootInputs, dif_pos hj, Function.comp_def] using
        (measurable_pi_apply (Sum.inr j : K ⊕ J)).comp measurable_fst.fst
    · simpa only [checkerRootInputs, dif_neg hj, Function.comp_def] using
        measurable_down.comp ((measurable_pi_apply
          (⟨Sum.inr j, crossing_root_at_D A C D other h hd hc j hr hj⟩ :
            {r // d ∈ (splitGraph A C D other).children r})).comp measurable_snd)

omit [Fintype K] [∀ i, MeasurableSpace (val i)] in
theorem targetRootInputs_measurable (i : Fin n) :
    Measurable (fun z : ReplayCandidate A C D other M × SplitRootArgs A C D other M i =>
      targetRootInputs A C D other M i z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro r
  rcases r with ⟨k | j, hr⟩
  · exact (measurable_pi_apply (Sum.inl k : K ⊕ J)).comp measurable_fst.fst
  · exact measurable_down.comp ((measurable_pi_apply
      (⟨Sum.inr j, hr⟩ : {r // i ∈ (splitGraph A C D other).children r})).comp measurable_snd)

omit [Fintype K] [∀ i, MeasurableSpace (val i)] in
theorem outsideRootInputs_measurable (i : Fin n) (hi : i ∉ D) :
    Measurable (outsideRootInputs A C D other M i hi) := by
  apply measurable_pi_iff.mpr
  intro r
  rcases r with ⟨k | j, hr⟩
  · exact measurable_down.comp (measurable_pi_apply
      (⟨Sum.inl (some k), (Finset.mem_union.mp hr).resolve_right hi⟩ :
        {r // i ∈ (splitGraph A C D other).children r}))
  · exact measurable_down.comp (measurable_pi_apply
      (⟨Sum.inr j, hr⟩ : {r // i ∈ (splitGraph A C D other).children r}))

include h in
def localAcceptanceEvent (d : Fin n) (hd : d ∈ D) :
    Set (LocalReplayContext A C D other M d × ReplayCandidate A C D other M) :=
  {z | localReplayAccept A C D other h M d hd z.1.1 z.1.2 z.2}

variable [∀ i, MeasurableSingletonClass (val i)] [∀ i, Countable (val i)]

include h in
theorem localAcceptanceEvent_measurable (hF : RootMechanismsMeasurable A C D other M)
    (d : Fin n) (hd : d ∈ D) : MeasurableSet (localAcceptanceEvent A C D other h M d hd) := by
  change MeasurableSet {z : LocalReplayContext A C D other M d × ReplayCandidate A C D other M |
    ∀ c (hc : c ∈ unionC C), M.F c
      (PaAssign.restrict (G := A) (replayWitness A C D other M d z.1.1) c)
      (checkerRootInputs A C D other h M d hd c hc z.2 z.1.2) (z.2.2 c) =
        replayWitness A C D other M d z.1.1 c}
  simp_rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro c
  apply MeasurableSet.iInter
  intro hc
  have hw : Measurable (fun z : LocalReplayContext A C D other M d × ReplayCandidate A C D other M =>
      replayWitness A C D other M d z.1.1) :=
    (replayWitness_measurable A C D other M d).comp measurable_fst.fst
  have hp : Measurable (fun z : LocalReplayContext A C D other M d × ReplayCandidate A C D other M =>
      PaAssign.restrict (G := A) (replayWitness A C D other M d z.1.1) c) :=
    measurable_pi_iff.mpr fun j => (measurable_pi_apply j.val).comp hw
  have hr : Measurable (fun z : LocalReplayContext A C D other M d × ReplayCandidate A C D other M =>
      checkerRootInputs A C D other h M d hd c hc z.2 z.1.2) :=
    (checkerRootInputs_measurable A C D other h M d hd c hc).comp
      (measurable_snd.prodMk measurable_fst.snd)
  exact Replay.measurableSet_observation_eq
    ((hF c).comp (hp.prodMk (hr.prodMk ((measurable_pi_apply c).comp measurable_snd.snd))))
    ((measurable_pi_apply c).comp hw)

include h in
/-- The candidate selected at a vertex of `D` is a measurable function of its
observed parents and its unobserved inputs, for all values of these, including
those where no candidate is accepted. -/
theorem localFirstReplay_measurable (hF : RootMechanismsMeasurable A C D other M)
    (d : Fin n) (hd : d ∈ D) :
    Measurable (fun z : LocalReplayContext A C D other M d =>
      firstReplay (z.2 ⟨Sum.inl none, hd⟩) (localReplayAccept A C D other h M d hd z.1 z.2)) := by
  have hm := Replay.contextReplay_measurable_comp (localAcceptanceEvent A C D other h M d hd)
    (localAcceptanceEvent_measurable A C D other h M hF d hd)
    (id : LocalReplayContext A C D other M d → _) (fun z => z.2 ⟨Sum.inl none, hd⟩)
    measurable_id ((measurable_pi_apply
      (⟨Sum.inl none, hd⟩ : {r // d ∈ (splitGraph A C D other).children r})).comp measurable_snd)
  exact hm

include h in
theorem replayModel_mechanismsMeasurable (hF : RootMechanismsMeasurable A C D other M) :
    (replayModel A C D other h M).MechanismsMeasurable := by
  classical
  intro i
  by_cases hi : i ∈ D
  · simp only [replayModel, dif_pos hi]
    change Measurable (fun z : PaAssign A val i × (SplitRootArgs A C D other M i × M.privateNoise i) =>
      M.F i z.1 (targetRootInputs A C D other M i
        (firstReplay (z.2.1 ⟨Sum.inl none, hi⟩)
          (localReplayAccept A C D other h M i hi z.1 z.2.1)) z.2.1) z.2.2)
    have hq : Measurable (fun z : PaAssign A val i × (SplitRootArgs A C D other M i × M.privateNoise i) =>
        firstReplay (z.2.1 ⟨Sum.inl none, hi⟩)
          (localReplayAccept A C D other h M i hi z.1 z.2.1)) :=
      (localFirstReplay_measurable A C D other h M hF i hi).comp
      (measurable_fst.prodMk measurable_snd.fst)
    have hr := (targetRootInputs_measurable A C D other M i).comp (hq.prodMk measurable_snd.fst)
    exact (hF i).comp (measurable_fst.prodMk (hr.prodMk measurable_snd.snd))
  · simp only [replayModel, dif_neg hi]
    change Measurable (fun z : PaAssign A val i × (SplitRootArgs A C D other M i × M.privateNoise i) =>
      M.F i z.1 (outsideRootInputs A C D other M i hi z.2.1) z.2.2)
    exact (hF i).comp (measurable_fst.prodMk
      (((outsideRootInputs_measurable A C D other M i hi).comp measurable_snd.fst).prodMk measurable_snd.snd))

include h in
theorem replayModel_eval_measurable (hF : RootMechanismsMeasurable A C D other M) :
    Measurable (fun x : (∀ r, replayRootValue A C D other M r) × (∀ i, M.privateNoise i) =>
      (replayModel A C D other h M).eval x.1 x.2) :=
  RootSCM.eval_measurable _ (replayModel_mechanismsMeasurable A C D other h M hF)

end MeraConstraints.HiddenGraph.StrongFaceSplitting
