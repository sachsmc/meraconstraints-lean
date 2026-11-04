import MeraConstraints.Probability.AssignmentConditioning
import MeraConstraints.Probability.FactorizedFibers

/-!
# From a coordinate cut factorization to conditional independence

The observed variables retained in a marginal are partitioned into `L`,
`R` and a conditioning set `Z`. If that marginal is `F(L,Z) * H(R,Z)`,
then all coordinate events in `L` and `R` are conditionally independent
given `Z`. The proof partitions the original mass into joint assignment
fibers on `L` and `R`; it does not assume a normalized marginal or an
independence conclusion. Signed real masses are allowed.
-/

namespace MeraConstraints.FiniteProbability

variable {n : ℕ} (val : Fin n → Type*)
  [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Random-vector conditional independence, stated at every observed
assignment using the literal event cross-product equation. -/
def CoordinateCI (p : FullAssign val → ℝ) (X Y Z : Finset (Fin n)) : Prop :=
  ∀ w : FullAssign val, CondIndependent p (assignmentEvent val w X)
    (assignmentEvent val w Y) (assignmentEvent val w Z)

def cutRepresentative (w : FullAssign val) (L R : Finset (Fin n))
    (a : AssignmentOn val L) (b : AssignmentOn val R) : FullAssign val :=
  assignmentRepresentative val (assignmentRepresentative val w R b) L a

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem cutRepresentative_left (w : FullAssign val) (L R : Finset (Fin n))
    (a : AssignmentOn val L) (b : AssignmentOn val R) (j : Fin n) (hj : j ∈ L) :
    cutRepresentative val w L R a b j = a ⟨j, hj⟩ := by
  simp [cutRepresentative, assignmentRepresentative, hj]

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem cutRepresentative_right (w : FullAssign val) (L R : Finset (Fin n)) (hLR : Disjoint L R)
    (a : AssignmentOn val L) (b : AssignmentOn val R) (j : Fin n) (hj : j ∈ R) :
    cutRepresentative val w L R a b j = b ⟨j, hj⟩ := by
  have hjL : j ∉ L := fun hjL => Finset.disjoint_left.mp hLR hjL hj
  simp [cutRepresentative, assignmentRepresentative, hj, hjL]

omit [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)] in
theorem cutRepresentative_outside (w : FullAssign val) (L R : Finset (Fin n))
    (a : AssignmentOn val L) (b : AssignmentOn val R) (j : Fin n) (hjL : j ∉ L) (hjR : j ∉ R) :
    cutRepresentative val w L R a b j = w j := by
  simp [cutRepresentative, assignmentRepresentative, hjL, hjR]

theorem assignment_cut_fiber (w : FullAssign val) (L R Z : Finset (Fin n))
    (hLR : Disjoint L R) (hLZ : Disjoint L Z) (hRZ : Disjoint R Z)
    (a : AssignmentOn val L) (b : AssignmentOn val R) :
    assignmentEvent val w Z ∩ fiber (fun z : FullAssign val =>
      ((fun j : {j : Fin n // j ∈ L} => z j), (fun j : {j : Fin n // j ∈ R} => z j))) (a, b) =
      assignmentEvent val (cutRepresentative val w L R a b) (L ∪ R ∪ Z) := by
  classical
  ext z
  simp only [assignmentEvent, fiber, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  have hrepZ (j : Fin n) (hj : j ∈ Z) : cutRepresentative val w L R a b j = w j :=
    cutRepresentative_outside val w L R a b j
      (fun hjL => Finset.disjoint_left.mp hLZ hjL hj)
      (fun hjR => Finset.disjoint_left.mp hRZ hjR hj)
  constructor
  · rintro ⟨hz, ha, hb⟩ j hj
    rcases Finset.mem_union.mp hj with hjLR | hjZ
    · rcases Finset.mem_union.mp hjLR with hjL | hjR
      · exact (congrFun ha ⟨j, hjL⟩).trans (cutRepresentative_left val w L R a b j hjL).symm
      · exact (congrFun hb ⟨j, hjR⟩).trans (cutRepresentative_right val w L R hLR a b j hjR).symm
    · exact (hz j hjZ).trans (hrepZ j hjZ).symm
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact (h j (Finset.mem_union_right _ hj)).trans (hrepZ j hj)
    · funext j
      exact (h j (Finset.mem_union_left _ (Finset.mem_union_left _ j.2))).trans
        (cutRepresentative_left val w L R a b j j.2)
    · funext j
      exact (h j (Finset.mem_union_left _ (Finset.mem_union_right _ j.2))).trans
        (cutRepresentative_right val w L R hLR a b j j.2)

/-- A marginal with two factors on the two sides of a coordinate cut gives
conditional independence of all sub-vectors on those sides. -/
theorem coordinateCI_of_cut_factorization (p : FullAssign val → ℝ)
    (L R Z : Finset (Fin n)) (hLR : Disjoint L R) (hLZ : Disjoint L Z) (hRZ : Disjoint R Z)
    (F H : FullAssign val → ℝ)
    (hfact : ∀ w : FullAssign val, mass p (assignmentEvent val w (L ∪ R ∪ Z)) = F w * H w)
    (hF : ∀ w v : FullAssign val, (∀ j ∈ L ∪ Z, w j = v j) → F w = F v)
    (hH : ∀ w v : FullAssign val, (∀ j ∈ R ∪ Z, w j = v j) → H w = H v)
    (X Y : Finset (Fin n)) (hX : X ⊆ L) (hY : Y ⊆ R) : CoordinateCI val p X Y Z := by
  classical
  intro w
  let C := assignmentEvent val w Z
  let QL := fun z : FullAssign val => fun j : {j : Fin n // j ∈ L} => z j
  let QR := fun z : FullAssign val => fun j : {j : Fin n // j ∈ R} => z j
  let a₀ : AssignmentOn val L := fun j => w j
  let b₀ : AssignmentOn val R := fun j => w j
  let f := fun a : AssignmentOn val L => F (cutRepresentative val w L R a b₀)
  let g := fun b : AssignmentOn val R => H (cutRepresentative val w L R a₀ b)
  have hrepZ (a : AssignmentOn val L) (b : AssignmentOn val R) (j : Fin n) (hj : j ∈ Z) :
      cutRepresentative val w L R a b j = w j :=
    cutRepresentative_outside val w L R a b j
      (fun hjL => Finset.disjoint_left.mp hLZ hjL hj)
      (fun hjR => Finset.disjoint_left.mp hRZ hjR hj)
  have hfg (a : AssignmentOn val L) (b : AssignmentOn val R) :
      mass p (C ∩ fiber (fun z => (QL z, QR z)) (a, b)) = f a * g b := by
    rw [show C ∩ fiber (fun z => (QL z, QR z)) (a, b) =
      assignmentEvent val (cutRepresentative val w L R a b) (L ∪ R ∪ Z) from
        assignment_cut_fiber val w L R Z hLR hLZ hRZ a b, hfact]
    congr 1
    · apply hF
      intro j hj
      rcases Finset.mem_union.mp hj with hjL | hjZ
      · rw [cutRepresentative_left val w L R a b j hjL, cutRepresentative_left val w L R a b₀ j hjL]
      · rw [hrepZ a b j hjZ, hrepZ a b₀ j hjZ]
    · apply hH
      intro j hj
      rcases Finset.mem_union.mp hj with hjR | hjZ
      · rw [cutRepresentative_right val w L R hLR a b j hjR, cutRepresentative_right val w L R hLR a₀ b j hjR]
      · rw [hrepZ a b j hjZ, hrepZ a₀ b j hjZ]
  let SX : Finset (AssignmentOn val L) := Finset.univ.filter fun a => ∀ j (hj : j ∈ X), a ⟨j, hX hj⟩ = w j
  let SY : Finset (AssignmentOn val R) := Finset.univ.filter fun b => ∀ j (hj : j ∈ Y), b ⟨j, hY hj⟩ = w j
  have hSX : preimage QL SX = assignmentEvent val w X := by ext z; simp [preimage, SX, QL, assignmentEvent]
  have hSY : preimage QR SY = assignmentEvent val w Y := by ext z; simp [preimage, SY, QR, assignmentEvent]
  have h := condIndependent_of_factorized_fibers p C QL QR f g hfg SX SY
  rw [hSX, hSY] at h
  exact h

end MeraConstraints.FiniteProbability
