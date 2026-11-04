import MeraConstraints.HiddenGraph.StrongFaceSplitting

/-!
# Strong splitting: locally available conditional replay

Write `C` for the union of the selected `C_i`. Each `D` vertex observes all
of `C` and its observed parents by Condition 1. An unselected root that
touches `C` and also leaves `C` is available at every `D` vertex by Condition 2.
Thus every `D` vertex can check the same candidate hidden inputs against
all original structural equations on `C`, using only permitted arguments.

The new common root supplies a sequence of candidates. All `D` vertices
select its first consistent candidate, with a specified fallback if none
exists. This chapter proves local checks equal one global consistency test,
so the selected replay is shared. Candidate spaces may be infinite.
Universe lifts on the unchanged root types are erased immediately when
calling an original mechanism; root and private input universes may differ.

This is deterministic infrastructure for conditional replay. A pointwise
encoding of the old inputs is not an independence argument: the probability
step must use independent candidate trials. `Probability.ReplayLaw` and
`Probability.ReplayTrials` prove the measurable first-replay conditional law
and supply an actual independent stream for each fixed positive acceptance
set. Applying those results to random graph-dependent fibers remains separate.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n))

def unionC : Finset (Fin n) := Finset.univ.biUnion C

theorem mem_unionC (c : Fin n) : c ∈ unionC C ↔ ∃ k, c ∈ C k := by simp [unionC]

variable (h : Conditions A C D other)

include h in
theorem unionC_not_D {c : Fin n} (hc : c ∈ unionC C) : c ∉ D := by
  obtain ⟨k, hk⟩ := (mem_unionC C c).mp hc
  exact fun hd => Finset.disjoint_left.mp (h.disjoint_common k) hk hd

include h in
theorem unionC_parent {d c : Fin n} (hd : d ∈ D) (hc : c ∈ unionC C) : c ∈ A.parents d := by
  obtain ⟨k, hk⟩ := (mem_unionC C c).mp hc
  exact h.observed_coverage k d hd (Finset.mem_union_left _ hk)

include h in
theorem unionC_parent_parent {d c j : Fin n} (hd : d ∈ D) (hc : c ∈ unionC C)
    (hj : j ∈ A.parents c) : j ∈ A.parents d := by
  obtain ⟨k, hk⟩ := (mem_unionC C c).mp hc
  exact h.observed_coverage k d hd (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hk, hj⟩))

include h in
theorem crossing_root_at_D {d c : Fin n} (hd : d ∈ D) (hc : c ∈ unionC C)
    (j : J) (hj : c ∈ other j) (hout : ¬ other j ⊆ unionC C) : d ∈ other j :=
  h.crossing_coverage j ⟨c, Finset.mem_inter.mpr ⟨hj, hc⟩⟩ hout hd

include h in
theorem root_at_D_not_internal {d : Fin n} (hd : d ∈ D) (j : J) (hj : d ∈ other j) :
    ¬ other j ⊆ unionC C := fun hs => unionC_not_D A C D other h (hs hj) hd

variable {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

abbrev ReplayCandidate := (∀ r, M.rootValue r) × (∀ i, M.privateNoise i)

def replayRootValue : Option K ⊕ J → Type (max uK uJ uR uP)
  | .inl none => ℕ → ReplayCandidate A C D other M
  | .inl (some k) => ULift.{max uK uJ uP} (M.rootValue (.inl k))
  | .inr j => ULift.{max uK uJ uP} (M.rootValue (.inr j))

noncomputable def replayBaseline : FullAssign val :=
  M.eval (fun r => Classical.choice (M.rootNonempty r)) (fun i => Classical.choice (M.privateNonempty i))

noncomputable def replayWitness (d : Fin n) (pa : PaAssign A val d) : FullAssign val := by
  classical
  exact fun j => if hj : j ∈ A.parents d then pa ⟨j, hj⟩ else replayBaseline A C D other M j

omit [Fintype K] in
theorem replayWitness_value (w : FullAssign val) {d c : Fin n} (hc : c ∈ A.parents d) :
    replayWitness A C D other M d (PaAssign.restrict w d) c = w c := by
  simp [replayWitness, hc, PaAssign.restrict]

include h in
theorem replayWitness_restrict (w : FullAssign val) {d c : Fin n}
    (hd : d ∈ D) (hc : c ∈ unionC C) :
    PaAssign.restrict (G := A) (replayWitness A C D other M d (PaAssign.restrict w d)) c =
      PaAssign.restrict (G := A) w c := by
  funext j
  exact replayWitness_value A C D other M w (unionC_parent_parent A C D other h hd hc j.property)

/-- A global description for proofs: resample selected and internal-C roots,
while retaining all roots which reach outside C. Mechanisms use the local
implementation below, not this unrestricted tuple. -/
noncomputable def replayRoots
    (u : ∀ r, replayRootValue A C D other M r) (q : ReplayCandidate A C D other M) :
    ∀ r, M.rootValue r := by
  classical
  exact fun r => match r with
    | .inl k => q.1 (.inl k)
    | .inr j => if other j ⊆ unionC C then q.1 (.inr j) else (u (.inr j)).down

include h in
/-- Check a C equation using only the root arguments permitted at d. -/
noncomputable def checkerRootInputs (d : Fin n) (hd : d ∈ D) (c : Fin n) (hc : c ∈ unionC C)
    (q : ReplayCandidate A C D other M)
    (lat : ∀ r : {r // d ∈ (splitGraph A C D other).children r}, replayRootValue A C D other M r) :
    ∀ r : {r // c ∈ (originalGraph A C D other).children r}, M.rootValue r := by
  classical
  intro r
  rcases r with ⟨k | j, hr⟩
  · exact q.1 (.inl k)
  · exact if hj : other j ⊆ unionC C then q.1 (.inr j)
      else (lat ⟨.inr j, crossing_root_at_D A C D other h hd hc j hr hj⟩).down

theorem checkerRootInputs_global (d : Fin n) (hd : d ∈ D) (c : Fin n) (hc : c ∈ unionC C)
    (u : ∀ r, replayRootValue A C D other M r) (q : ReplayCandidate A C D other M) :
    checkerRootInputs A C D other h M d hd c hc q (fun r => u r.val) =
      (fun r : {r // c ∈ (originalGraph A C D other).children r} =>
        replayRoots A C D other M u q r.val) := by
  classical
  funext r
  rcases r with ⟨k | j, hr⟩
  · rfl
  · by_cases hj : other j ⊆ unionC C <;> simp [checkerRootInputs, replayRoots, hj]

include h in
noncomputable def localReplayAccept (d : Fin n) (hd : d ∈ D) (pa : PaAssign A val d)
    (lat : ∀ r : {r // d ∈ (splitGraph A C D other).children r}, replayRootValue A C D other M r)
    (q : ReplayCandidate A C D other M) : Prop :=
  ∀ c (hc : c ∈ unionC C),
    M.F c (PaAssign.restrict (replayWitness A C D other M d pa) c)
      (checkerRootInputs A C D other h M d hd c hc q lat) (q.2 c) =
        replayWitness A C D other M d pa c

noncomputable def globalReplayAccept (w : FullAssign val)
    (u : ∀ r, replayRootValue A C D other M r) (q : ReplayCandidate A C D other M) : Prop :=
  ∀ c ∈ unionC C, M.F c (PaAssign.restrict w c)
    (fun r => replayRoots A C D other M u q r.val) (q.2 c) = w c

/-- Both manuscript coverage hypotheses are used to identify each allowed
local test with one common global consistency predicate. -/
theorem localReplayAccept_iff_global (d : Fin n) (hd : d ∈ D) (w : FullAssign val)
    (u : ∀ r, replayRootValue A C D other M r) (q : ReplayCandidate A C D other M) :
    localReplayAccept A C D other h M d hd (PaAssign.restrict w d) (fun r => u r.val) q ↔
      globalReplayAccept A C D other M w u q := by
  unfold localReplayAccept globalReplayAccept
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  have hp : PaAssign.restrict (G := (originalGraph A C D other).observed)
      (replayWitness A C D other M d (PaAssign.restrict w d)) c =
      PaAssign.restrict (G := (originalGraph A C D other).observed) w c :=
    replayWitness_restrict A C D other h M w hd hc
  rw [hp,
    checkerRootInputs_global A C D other h M,
    replayWitness_value A C D other M w (unionC_parent A C D other h hd hc)]

noncomputable def firstReplay {T : Type*} (trials : ℕ → T) (P : T → Prop) : T := by
  classical
  exact if ht : ∃ t, P (trials t) then trials (Nat.find ht) else trials 0

theorem firstReplay_const {T : Type*} (q : T) (P : T → Prop) :
    firstReplay (fun _ => q) P = q := by
  classical
  unfold firstReplay
  split <;> rfl

theorem firstReplay_congr {T : Type*} (trials : ℕ → T) (P Q : T → Prop)
    (hPQ : ∀ q, P q ↔ Q q) : firstReplay trials P = firstReplay trials Q := by
  have he : P = Q := funext (fun q => propext (hPQ q))
  rw [he]

theorem firstReplay_accept {T : Type*} (trials : ℕ → T) (P : T → Prop) (ht : ∃ t, P (trials t)) :
    P (firstReplay trials P) := by
  classical
  rw [firstReplay, dif_pos ht]
  exact Nat.find_spec ht

/-- All D vertices use exactly the same replay from their common root. -/
theorem firstReplay_shared (d e : Fin n) (hd : d ∈ D) (he : e ∈ D)
    (w : FullAssign val) (u : ∀ r, replayRootValue A C D other M r) :
    firstReplay (u (.inl none))
        (localReplayAccept A C D other h M d hd (PaAssign.restrict w d) (fun r => u r.val)) =
      firstReplay (u (.inl none))
        (localReplayAccept A C D other h M e he (PaAssign.restrict w e) (fun r => u r.val)) := by
  apply firstReplay_congr
  intro q
  exact (localReplayAccept_iff_global A C D other h M d hd w u q).trans
    (localReplayAccept_iff_global A C D other h M e he w u q).symm

end MeraConstraints.HiddenGraph.StrongFaceSplitting
