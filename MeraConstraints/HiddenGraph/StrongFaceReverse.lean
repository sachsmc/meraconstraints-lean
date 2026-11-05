import MeraConstraints.HiddenGraph.StrongFaceReplay

/-!
# The split model built from an original model

From a structural model `M` on the original graph, `replayModel` defines a
structural model on the split graph. A vertex outside `D` is computed as in `M`,
from the `C_i`-copies of the selected variables and from the other unobserved
variables. A vertex in `D` is computed as in `M`, with the values of the selected
variables taken from the candidate chosen by conditional replay
(`StrongFaceReplay`), and its other unobserved inputs unchanged. The new
unobserved variable with children `D` holds a stream of candidates.

If the stream is constant at the original inputs `(u, ε)`, then the first candidate
is accepted and the split model computes the same observed values as `M`
(`original_eval_reproduced`). This concerns one value of the inputs only, and
says nothing about the distribution: a constant stream is not a random input
independent of the others. The distribution is treated with an independent
stream in the chapters from `StrongFaceFibers` on. For a general stream,
`replayModel_eval_of_consistent` gives the output whenever some candidate is
accepted.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting

universe uK uJ uV uR uP

variable {n : ℕ} {K : Type uK} {J : Type uJ} [Fintype K]
  (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n))
  (other : J → Finset (Fin n)) (h : Conditions A C D other)
  {val : Fin n → Type uV}
  (M : RootSCM.{max uK uJ, uV, uR, uP} (originalGraph A C D other) val)

/-- The original unobserved inputs read by a vertex outside `D`: the selected
variables through their `C_i`-copies, the others unchanged. -/
def outsideRootInputs (i : Fin n) (hi : i ∉ D)
    (lat : ∀ r : {r // i ∈ (splitGraph A C D other).children r}, replayRootValue A C D other M r) :
    ∀ r : {r // i ∈ (originalGraph A C D other).children r}, M.rootValue r := by
  intro r
  rcases r with ⟨k | j, hr⟩
  · exact (lat ⟨.inl (some k), (Finset.mem_union.mp hr).resolve_right hi⟩).down
  · exact (lat ⟨.inr j, hr⟩).down

/-- The original unobserved inputs read by a vertex in `D`: the selected variables
from the shared candidate `q`, the others unchanged. -/
def targetRootInputs (i : Fin n) (q : ReplayCandidate A C D other M)
    (lat : ∀ r : {r // i ∈ (splitGraph A C D other).children r}, replayRootValue A C D other M r) :
    ∀ r : {r // i ∈ (originalGraph A C D other).children r}, M.rootValue r := by
  intro r
  rcases r with ⟨k | j, hr⟩
  · exact q.1 (.inl k)
  · exact (lat ⟨.inr j, hr⟩).down

include h in
/-- The split model built from the original model `M`. It uses `h : Conditions` to
define the local test of conditional replay. -/
noncomputable def replayModel :
    RootSCM.{max uK uJ, uV, max uK uJ uR uP, uP} (splitGraph A C D other) val where
  rootValue := replayRootValue A C D other M
  rootNonempty r := by
    cases r with
    | inl k =>
      cases k with
      | none => exact ⟨fun _ =>
          (fun r => Classical.choice (M.rootNonempty r), fun i => Classical.choice (M.privateNonempty i))⟩
      | some k => exact ⟨ULift.up (Classical.choice (M.rootNonempty (.inl k)))⟩
    | inr j => exact ⟨ULift.up (Classical.choice (M.rootNonempty (.inr j)))⟩
  privateNoise := M.privateNoise
  privateNonempty := M.privateNonempty
  F i pa lat ε := if hi : i ∈ D then
    let q := firstReplay (lat ⟨.inl none, hi⟩) (localReplayAccept A C D other h M i hi pa lat)
    M.F i pa (targetRootInputs A C D other M i q lat) ε
    else M.F i pa (outsideRootInputs A C D other M i hi lat) ε

/-- Split inputs for original inputs `(u, ε)`: the stream is constant at `(u, ε)`.
This is for a single value of the inputs; it is not a distribution of independent
inputs. -/
def encodeOriginalInputs (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    ∀ r, replayRootValue A C D other M r
  | .inl none => fun _ => (u, ε)
  | .inl (some k) => ULift.up (u (.inl k))
  | .inr j => ULift.up (u (.inr j))

omit [Fintype K] in
theorem outsideRootInputs_encoded (i : Fin n) (hi : i ∉ D)
    (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    outsideRootInputs A C D other M i hi (fun r => encodeOriginalInputs A C D other M u ε r.val) =
      (fun r : {r // i ∈ (originalGraph A C D other).children r} => u r.val) := by
  funext r
  rcases r with ⟨k | j, hr⟩ <;> rfl

omit [Fintype K] in
theorem targetRootInputs_encoded (i : Fin n)
    (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    targetRootInputs A C D other M i (u, ε)
        (fun r => encodeOriginalInputs A C D other M u ε r.val) =
      (fun r : {r // i ∈ (originalGraph A C D other).children r} => u r.val) := by
  funext r
  rcases r with ⟨k | j, hr⟩ <;> rfl

theorem replayRoots_encoded (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    replayRoots A C D other M (encodeOriginalInputs A C D other M u ε) (u, ε) = u := by
  classical
  funext r
  cases r with
  | inl k => rfl
  | inr j => simp [replayRoots, encodeOriginalInputs]

include h in
/-- The original inputs pass the local test at every vertex of `D`. -/
theorem encoded_replay_accepts (d : Fin n) (hd : d ∈ D)
    (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    localReplayAccept A C D other h M d hd (PaAssign.restrict (M.eval u ε) d)
      (fun r => encodeOriginalInputs A C D other M u ε r.val) (u, ε) := by
  apply (localReplayAccept_iff_global A C D other h M d hd _ _ _).mpr
  intro c hc
  rw [replayRoots_encoded]
  exact (M.eval_eq u ε c).symm

include h in
/-- At the encoded inputs, the split model computes the same observed values as
the original model. -/
theorem original_eval_reproduced (u : ∀ r, M.rootValue r) (ε : ∀ i, M.privateNoise i) :
    (replayModel A C D other h M).eval (encodeOriginalInputs A C D other M u ε) ε = M.eval u ε := by
  classical
  symm
  apply RootSCM.eval_unique
  intro i
  by_cases hi : i ∈ D
  · simp only [replayModel, dif_pos hi]
    change M.eval u ε i = M.F i (PaAssign.restrict (M.eval u ε) i)
      (targetRootInputs A C D other M i
        (firstReplay (fun _ => (u, ε)) _) (fun r => encodeOriginalInputs A C D other M u ε r.val)) (ε i)
    rw [firstReplay_const, targetRootInputs_encoded]
    exact M.eval_eq u ε i
  · simp only [replayModel, dif_neg hi]
    rw [outsideRootInputs_encoded]
    exact M.eval_eq u ε i

include h in
theorem targetRootInputs_global (i : Fin n) (hi : i ∈ D)
    (u : ∀ r, replayRootValue A C D other M r) (q : ReplayCandidate A C D other M) :
    targetRootInputs A C D other M i q (fun r => u r.val) =
      (fun r : {r // i ∈ (originalGraph A C D other).children r} =>
        replayRoots A C D other M u q r.val) := by
  classical
  funext r
  rcases r with ⟨k | j, hr⟩
  · rfl
  · have hj := root_at_D_not_internal A C D other h hi j hr
    simp [targetRootInputs, replayRoots, hj]

theorem outsideRootInputs_global (i : Fin n) (hc : i ∉ unionC C) (hi : i ∉ D)
    (u : ∀ r, replayRootValue A C D other M r) (q : ReplayCandidate A C D other M) :
    outsideRootInputs A C D other M i hi (fun r => u r.val) =
      (fun r : {r // i ∈ (originalGraph A C D other).children r} =>
        replayRoots A C D other M u q r.val) := by
  classical
  funext r
  rcases r with ⟨k | j, hr⟩
  · obtain hk | hd := Finset.mem_union.mp hr
    · exact (hc ((mem_unionC C i).mpr ⟨k, hk⟩)).elim
    · exact (hi hd).elim
  · have hj : ¬ other j ⊆ unionC C := fun hs => hc (hs hr)
    simp [outsideRootInputs, replayRoots, hj]

/-- Private noise after replay: the candidate's value at vertices of `C`, and `ε`
elsewhere. -/
def replayPrivate (q : ReplayCandidate A C D other M) (ε : ∀ i, M.privateNoise i) :
    ∀ i, M.privateNoise i := fun i => if i ∈ unionC C then q.2 i else ε i

include h in
/-- For any stream, suppose some candidate passes the global test for the split
model's own output `w`. Then `w` is the original evaluation in which the selected
variables, the unselected variables with all children in `C`, and the private noise
at `C` are replaced by the first accepted candidate. That some candidate is accepted
holds almost surely under independent draws, by the probability chapters. -/
theorem replayModel_eval_of_consistent
    (u : ∀ r, replayRootValue A C D other M r) (ε : ∀ i, M.privateNoise i)
    (ht : ∃ t, globalReplayAccept A C D other M ((replayModel A C D other h M).eval u ε) u
      (u (.inl none) t)) :
    let w := (replayModel A C D other h M).eval u ε
    let q := firstReplay (u (.inl none)) (globalReplayAccept A C D other M w u)
    w = M.eval (replayRoots A C D other M u q) (replayPrivate A C D other M q ε) := by
  classical
  let w := (replayModel A C D other h M).eval u ε
  let q := firstReplay (u (.inl none)) (globalReplayAccept A C D other M w u)
  have hq : globalReplayAccept A C D other M w u q := firstReplay_accept _ _ ht
  have hlocal (i : Fin n) (hi : i ∈ D) :
      firstReplay (u (.inl none))
        (localReplayAccept A C D other h M i hi (PaAssign.restrict w i) (fun r => u r.val)) = q :=
    firstReplay_congr _ _ _ (localReplayAccept_iff_global A C D other h M i hi w u)
  apply RootSCM.eval_unique
  intro i
  by_cases hc : i ∈ unionC C
  · simpa only [replayPrivate, if_pos hc] using (hq i hc).symm
  · have heq := (replayModel A C D other h M).eval_eq u ε i
    by_cases hi : i ∈ D
    · simp only [replayModel, dif_pos hi] at heq
      change w i = M.F i (PaAssign.restrict w i)
        (targetRootInputs A C D other M i
          (firstReplay (u (.inl none))
            (localReplayAccept A C D other h M i hi (PaAssign.restrict w i) (fun r => u r.val)))
          (fun r => u r.val)) (ε i) at heq
      rw [hlocal, targetRootInputs_global A C D other h M i hi] at heq
      simpa only [replayPrivate, if_neg hc] using heq
    · simp only [replayModel, dif_neg hi] at heq
      change w i = M.F i (PaAssign.restrict w i)
        (outsideRootInputs A C D other M i hi (fun r => u r.val)) (ε i) at heq
      rw [outsideRootInputs_global A C D other M i hc hi] at heq
      simpa only [replayPrivate, if_neg hc] using heq

end MeraConstraints.HiddenGraph.StrongFaceSplitting
