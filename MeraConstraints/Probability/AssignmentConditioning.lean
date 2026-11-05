import MeraConstraints.Probability.AssignmentPartition
import MeraConstraints.Probability.Pushforward

/-!
# Dropping conditioning variables by averaging

Let `p` be a strictly positive distribution of the observed variables, `S` a set
of observed variables, `T ⊆ S`, and `i ∉ S`. Suppose the conditional probability
of `V_i = w_i` given the values of `S` depends only on `w_i` and the values of
`T`. Then averaging over the values of `S \ T` shows that it equals the
conditional probability given `T` (`conditional_assignment_eq_of_congr`).
`condIndependent_assignment_of_congr` gives the matching conditional
independence of `V_i` and `S` given `T`.

These are used in `GlobalModel.AncestralMarkov` and
`GlobalModel.OrderingInvariance`, where the dependence hypothesis comes from the
conditional independencies implied by the graph.
-/

namespace MeraConstraints.FiniteProbability

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

abbrev AssignmentOn (S : Finset (Fin n)) := ∀ j : {j : Fin n // j ∈ S}, val j

def assignmentRepresentative (w : FullAssign val) (S : Finset (Fin n))
    (b : AssignmentOn val S) : FullAssign val :=
  fun j => if hj : j ∈ S then b ⟨j, hj⟩ else w j

theorem assignment_fiber_eq_event (w : FullAssign val) (S : Finset (Fin n)) (b : AssignmentOn val S) :
    fiber (fun z : FullAssign val => fun j : {j : Fin n // j ∈ S} => z j) b =
      assignmentEvent val (assignmentRepresentative val w S b) S := by
  ext z
  simp only [fiber, assignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j hj
    simpa only [assignmentRepresentative, dif_pos hj] using congrFun h ⟨j, hj⟩
  · intro h
    funext j
    simpa only [assignmentRepresentative, dif_pos j.2] using h j j.2

/-- If the conditional probability of `V_i` given `S` depends only on `V_i` and
`T ⊆ S`, it equals the conditional probability given `T`. -/
theorem conditional_assignment_eq_of_congr (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (S T : Finset (Fin n)) (hTS : T ⊆ S) (i : Fin n) (hi : i ∉ S)
    (hcongr : ∀ w v : FullAssign val, (∀ j ∈ T, w j = v j) → w i = v i →
      conditional p (valueEvent val w i) (assignmentEvent val w S) =
        conditional p (valueEvent val v i) (assignmentEvent val v S)) (w : FullAssign val) :
    conditional p (valueEvent val w i) (assignmentEvent val w S) =
      conditional p (valueEvent val w i) (assignmentEvent val w T) := by
  classical
  let E := valueEvent val w i
  let C := assignmentEvent val w T
  let Z := fun z : FullAssign val => fun j : {j : Fin n // j ∈ S} => z j
  have hCpos : mass p C ≠ 0 := (mass_pos_of_mem hpos (self_mem_assignmentEvent val w T)).ne'
  symm
  apply conditional_eq_of_fiberwise_mass p E C Z _ hCpos
  intro b
  let v := assignmentRepresentative val w S b
  have hcur : v i = w i := by simp [v, assignmentRepresentative, hi]
  have hB : fiber Z b = assignmentEvent val v S := assignment_fiber_eq_event val w S b
  by_cases hvC : v ∈ C
  · have hvC' : ∀ j ∈ T, v j = w j := (Finset.mem_filter.mp hvC).2
    have hBC : assignmentEvent val v S ⊆ C := by
      intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      exact ((Finset.mem_filter.mp hz).2 j (hTS hj)).trans (hvC' j hj)
    have hCB : C ∩ fiber Z b = assignmentEvent val v S := by
      rw [hB, Finset.inter_eq_right.mpr hBC]
    have hE : E = valueEvent val v i := by
      ext z
      simp only [E, valueEvent, Finset.mem_filter, Finset.mem_univ, true_and, hcur]
    have hcond : conditional p (valueEvent val v i) (assignmentEvent val v S) =
        conditional p (valueEvent val w i) (assignmentEvent val w S) :=
      (hcongr w v (fun j hj => (hvC' j hj).symm) hcur.symm).symm
    rw [Finset.inter_assoc, hCB, hE]
    have hm := conditional_mul_mass p (valueEvent val v i) (assignmentEvent val v S)
      (mass_pos_of_mem hpos (self_mem_assignmentEvent val v S)).ne'
    rw [hcond] at hm
    exact hm.symm
  · have hCB : C ∩ fiber Z b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzC, hzB⟩ := Finset.mem_inter.mp hz
      apply hvC
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      have hzB' : z ∈ assignmentEvent val v S := hB ▸ hzB
      have hzv := (Finset.mem_filter.mp hzB').2 j (hTS hj)
      exact hzv.symm.trans ((Finset.mem_filter.mp hzC).2 j hj)
    rw [Finset.inter_assoc, hCB]
    simp [mass]

/-- Under the same hypotheses, the event `V_i = w_i` is conditionally independent
of the event fixing `S`, given the event fixing `T`. -/
theorem condIndependent_assignment_of_congr (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w)
    (S T : Finset (Fin n)) (hTS : T ⊆ S) (i : Fin n) (hi : i ∉ S)
    (hcongr : ∀ w v : FullAssign val, (∀ j ∈ T, w j = v j) → w i = v i →
      conditional p (valueEvent val w i) (assignmentEvent val w S) =
        conditional p (valueEvent val v i) (assignmentEvent val v S)) (w : FullAssign val) :
    CondIndependent p (valueEvent val w i) (assignmentEvent val w S) (assignmentEvent val w T) := by
  let E := valueEvent val w i
  let B := assignmentEvent val w S
  let C := assignmentEvent val w T
  have hB : mass p B ≠ 0 := (mass_pos_of_mem hpos (self_mem_assignmentEvent val w S)).ne'
  have hC : mass p C ≠ 0 := (mass_pos_of_mem hpos (self_mem_assignmentEvent val w T)).ne'
  have hBC : B ∩ C = B := Finset.inter_eq_left.mpr (assignmentEvent_antitone val w hTS)
  have h := conditional_assignment_eq_of_congr val p hpos S T hTS i hi hcongr w
  change mass p (E ∩ B) / mass p B = mass p (E ∩ C) / mass p C at h
  change mass p ((E ∩ B) ∩ C) * mass p C = mass p (E ∩ C) * mass p (B ∩ C)
  rw [Finset.inter_assoc, hBC]
  exact (div_eq_div_iff hB hC).mp h

end MeraConstraints.FiniteProbability
