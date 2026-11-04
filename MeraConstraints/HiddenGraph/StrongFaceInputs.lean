import MeraConstraints.HiddenGraph.StrongFaceFibers
import MeraConstraints.Probability.IndependentGroupingMeasure

/-!
# The original inputs split into independent replay blocks

The local block contains selected roots, other roots whose children lie
entirely in C, and private inputs at C. All remaining inputs form the external
block. These are disjoint groups of the original mutually independent family.
Unused coordinates are filled with fixed constants to keep both blocks in the
native candidate type; the constants do not copy any random input.

Reassembling external and local blocks is precisely `resampleInputs`. Thus its
independence premise will follow from the original full mutual independence,
rather than being assumed for a transformed output.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

open MeasureTheory ProbabilityTheory

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

abbrev ReplayInputIndex := (K ⊕ J) ⊕ Fin n

def ReplayInputValue : ReplayInputIndex (K := K) (J := J) (n := n) → Type (max uK uJ uR uP)
  | .inl r => ULift.{max uK uJ uP} (M.rootValue r)
  | .inr i => ULift.{max uK uJ uR} (M.privateNoise i)

def replayInput (x : ReplayCandidate A C D other M) : ∀ t, ReplayInputValue A C D other M t
  | .inl r => ULift.up (x.1 r)
  | .inr i => ULift.up (x.2 i)

noncomputable def replayInputBlock : ReplayInputIndex (K := K) (J := J) (n := n) → Bool := by
  classical
  exact fun t => match t with
    | .inl (.inl _) => true
    | .inl (.inr j) => decide (other j ⊆ unionC C)
    | .inr i => decide (i ∈ unionC C)

noncomputable def defaultCandidate : ReplayCandidate A C D other M :=
  (fun r => Classical.choice (M.rootNonempty r), fun i => Classical.choice (M.privateNonempty i))

noncomputable def maskInputs (b : Bool) (x : ReplayCandidate A C D other M) :
    ReplayCandidate A C D other M := by
  classical
  exact (fun r => if replayInputBlock C other (.inl r) = b then x.1 r else (defaultCandidate A C D other M).1 r,
    fun i => if replayInputBlock C other (.inr i) = b then x.2 i else (defaultCandidate A C D other M).2 i)

abbrev ReplayInputGroup (b : Bool) :=
  ∀ t : {t : ReplayInputIndex (K := K) (J := J) (n := n) // replayInputBlock C other t = b},
    ReplayInputValue A C D other M t.val

noncomputable def replayGroupMap (b : Bool) (z : ReplayInputGroup A C D other M b) :
    ReplayCandidate A C D other M := by
  classical
  exact (fun r => if hb : replayInputBlock C other (.inl r) = b then (z ⟨.inl r, hb⟩).down
      else (defaultCandidate A C D other M).1 r,
    fun i => if hb : replayInputBlock C other (.inr i) = b then (z ⟨.inr i, hb⟩).down
      else (defaultCandidate A C D other M).2 i)

theorem replayGroupMap_eq_maskInputs (b : Bool) (x : ReplayCandidate A C D other M) :
    replayGroupMap A C D other M b (fun t => replayInput A C D other M x t.val) =
      maskInputs A C D other M b x := by
  classical
  apply Prod.ext
  · funext r
    by_cases hb : replayInputBlock C other (.inl r) = b <;>
      simp [replayGroupMap, maskInputs, hb, replayInput]
  · funext i
    by_cases hb : replayInputBlock C other (.inr i) = b <;>
      simp [replayGroupMap, maskInputs, hb, replayInput]

theorem resampleInputs_mask (x q : ReplayCandidate A C D other M) :
    resampleInputs A C D other M (maskInputs A C D other M false x)
      (maskInputs A C D other M true q) = resampleInputs A C D other M x q := by
  classical
  apply Prod.ext
  · funext r
    cases r with
    | inl k => simp [resampleInputs, replayRoots, maskInputs, replayInputBlock]
    | inr j =>
      by_cases hj : other j ⊆ unionC C <;>
        simp [resampleInputs, replayRoots, encodeOriginalInputs, maskInputs, replayInputBlock, hj]
  · funext i
    by_cases hi : i ∈ unionC C <;>
      simp [resampleInputs, replayPrivate, maskInputs, replayInputBlock, hi]

theorem resampleInputs_self (x : ReplayCandidate A C D other M) :
    resampleInputs A C D other M x x = x := by
  classical
  apply Prod.ext
  · exact replayRoots_encoded A C D other M x.1 x.2
  · funext i
    simp [resampleInputs, replayPrivate]

variable [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

instance replayInputValueMeasurableSpace (t : ReplayInputIndex (K := K) (J := J) (n := n)) :
    MeasurableSpace (ReplayInputValue A C D other M t) := by
  cases t <;> dsimp [ReplayInputValue] <;> infer_instance

omit [Fintype K] in
theorem replayInput_measurable (t : ReplayInputIndex (K := K) (J := J) (n := n)) :
    Measurable (fun x => replayInput A C D other M x t) := by
  cases t with
  | inl r => exact measurable_up.comp ((measurable_pi_apply r).comp measurable_fst)
  | inr i => exact measurable_up.comp ((measurable_pi_apply i).comp measurable_snd)

theorem replayGroupMap_measurable (b : Bool) : Measurable (replayGroupMap A C D other M b) := by
  classical
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro r
    change Measurable (fun z : ReplayInputGroup A C D other M b =>
      if hb : replayInputBlock C other (.inl r) = b then (z ⟨.inl r, hb⟩).down
      else (defaultCandidate A C D other M).1 r)
    split_ifs with hb
    · exact measurable_down.comp (measurable_pi_apply
        (⟨.inl r, hb⟩ : {t : ReplayInputIndex (K := K) (J := J) (n := n) // replayInputBlock C other t = b}))
    · exact measurable_const
  · apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun z : ReplayInputGroup A C D other M b =>
      if hb : replayInputBlock C other (.inr i) = b then (z ⟨.inr i, hb⟩).down
      else (defaultCandidate A C D other M).2 i)
    split_ifs with hb
    · exact measurable_down.comp (measurable_pi_apply
        (⟨.inr i, hb⟩ : {t : ReplayInputIndex (K := K) (J := J) (n := n) // replayInputBlock C other t = b}))
    · exact measurable_const

theorem maskInputs_measurable (b : Bool) : Measurable (maskInputs A C D other M b) := by
  have hm := (replayGroupMap_measurable A C D other M b).comp
    (measurable_pi_iff.mpr fun t => replayInput_measurable A C D other M t.val)
  simpa only [Function.comp_def, replayGroupMap_eq_maskInputs] using hm

theorem resampleInputs_measurable : Measurable (fun z :
    ReplayCandidate A C D other M × ReplayCandidate A C D other M =>
      resampleInputs A C D other M z.1 z.2) := by
  classical
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro r
    cases r with
    | inl k => exact (measurable_pi_apply (Sum.inl k : K ⊕ J)).comp measurable_snd.fst
    | inr j =>
      by_cases hj : other j ⊆ unionC C
      · simpa only [resampleInputs, replayRoots, if_pos hj, Function.comp_def] using
          (measurable_pi_apply (Sum.inr j : K ⊕ J)).comp measurable_snd.fst
      · simpa only [resampleInputs, replayRoots, if_neg hj, encodeOriginalInputs, Function.comp_def] using
          (measurable_pi_apply (Sum.inr j : K ⊕ J)).comp measurable_fst.fst
  · apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i ∈ unionC C
    · simpa only [resampleInputs, replayPrivate, if_pos hi, Function.comp_def] using
        (measurable_pi_apply i).comp measurable_snd.snd
    · simpa only [resampleInputs, replayPrivate, if_neg hi, Function.comp_def] using
        (measurable_pi_apply i).comp measurable_fst.snd

variable [Fintype J]

/-- Full original mutual independence implies independence of the actual
external and C-local replay blocks, even for arbitrary measurable input types. -/
theorem replayBlocks_independent (ν : Measure (ReplayCandidate A C D other M))
    (hInd : iIndepFun (fun t x => replayInput A C D other M x t) ν) :
    IndepFun (maskInputs A C D other M false) (maskInputs A C D other M true) ν := by
  have hg := Independent.iIndepFun_grouped (replayInputBlock C other)
    (ReplayInputValue A C D other M) ν (fun t x => replayInput A C D other M x t)
      (replayInput_measurable A C D other M) hInd
  have hi := (hg.indepFun (i := false) (j := true) Bool.false_ne_true).comp
    (replayGroupMap_measurable A C D other M false)
    (replayGroupMap_measurable A C D other M true)
  simpa only [Function.comp_def, replayGroupMap_eq_maskInputs] using hi

end MeraConstraints.HiddenGraph.StrongFaceSplitting
