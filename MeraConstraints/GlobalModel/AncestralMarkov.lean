import MeraConstraints.GlobalModel.AncestralKernels
import MeraConstraints.HiddenGraph.AncestralBlanket
import MeraConstraints.Probability.AssignmentConditioning

/-!
# Local Markov equations on every ancestral set

After equation `eqn:ancmargin`, Appendix Step 2 divides the marginal on an
ancestral set `A` by the marginal on `A \ {i}`, for an observed sink `i`.
All other districts cancel. Equations (O) make the remaining ratio depend
only on `i`, the other retained district members, and their external parents.
Finite averaging then proves the literal conditional-independence equation.

At c-degree at most one, `RetainedDistrictConnected` and the graph theorem
`inducedAncestralBlanket_eq` identify these members with the actual district
in the retained latent graph. The final result therefore uses its actual
induced blanket, not an assumed unchanged district partition.

We prove the local equations simultaneously for every ancestral set and sink.
This is the ordered-local formulation used in the appendix. A separate
separation theorem relating it to every graphical d-separation or m-separation statement
has not been assumed or proved by defining that global predicate here.
-/

namespace MeraConstraints.GlobalModel.KernelReconstruction

open FiniteProbability HiddenGraph

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

omit [∀ i, DecidableEq (val i)] in
theorem setMargin_pos (K : Kernels G val) (hK : Positive G val K)
    (d : DistrictId G) (A : Finset (Fin n)) (w : FullAssign val) : 0 < setMargin G val K d A w := by
  classical
  unfold setMargin
  apply Finset.sum_pos'
  · intro out _
    split
    · exact (hK d _).le
    · exact le_refl _
  · refine ⟨fun j => w j.val, Finset.mem_univ _, ?_⟩
    have hm : SetMatch G val d A w (fun j => w j.val) := fun _ _ => rfl
    simpa only [if_pos hm] using hK d ((fun j => w j.val), fun j => w j)

private theorem ratio_products (f g : DistrictId G → ℝ) (d : DistrictId G)
    (hg : (∏ e, g e) ≠ 0) (heq : ∀ e, e ≠ d → f e = g e) :
    (∏ e, f e) / (∏ e, g e) = f d / g d := by
  classical
  have hgd : g d ≠ 0 := (Finset.prod_ne_zero_iff.mp hg) d (Finset.mem_univ d)
  have hrest : (∏ e ∈ Finset.univ.erase d, f e) = ∏ e ∈ Finset.univ.erase d, g e :=
    Finset.prod_congr rfl fun e he => heq e (Finset.ne_of_mem_erase he)
  apply (div_eq_div_iff hg hgd).2
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ d),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ d), hrest]
  ring

/-- The conditional at an ancestral sink is the ratio of its own district's
two ordinary margins; no other district remains in the formula. -/
theorem ancestral_sink_conditional_eq_ratio (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (w : FullAssign val) :
    conditional (joint G val K) (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      setMargin G val K (observedDistrict G i) A w /
        setMargin G val K (observedDistrict G i) (A.erase i) w := by
  have hevent : valueEvent val w i ∩ assignmentEvent val w (A.erase i) = assignmentEvent val w A := by
    rw [← assignmentEvent_insert, Finset.insert_erase hs.1]
  rw [conditional, hevent, joint_ancestral_mass G val K hNO A hA,
    joint_ancestral_mass G val K hNO _ (observedAncestral_erase G A hA i hs)]
  apply ratio_products G _ _ _
  · exact Finset.prod_ne_zero_iff.mpr fun d _ => (setMargin_pos G val K hK d _ w).ne'
  · intro d hd
    exact setMargin_erase_of_ne G val K d A i w hd

/-- Agreement on the blanket and current value fixes the sink conditional,
even if all other retained observed values change. -/
theorem ancestral_sink_conditional_congr (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (w v : FullAssign val)
    (hB : ∀ j ∈ ancestralBlanket G A i, w j = v j) (hi : w i = v i) :
    conditional (joint G val K) (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      conditional (joint G val K) (valueEvent val v i) (assignmentEvent val v (A.erase i)) := by
  have hm (T : Finset (Fin n)) (hT : ObservedAncestral G T) (hTA : T ⊆ A) :
      setMargin G val K (observedDistrict G i) T w = setMargin G val K (observedDistrict G i) T v := by
    apply setMargin_congr G val K hNO _ T hT w v
    · intro j hj hjd
      by_cases hji : j = i
      · subst j
        exact hi
      · exact hB j (member_mem_ancestralBlanket G A i j (hTA hj) hji hjd)
    · intro l hl hld j hjl hjd
      exact hB j (parent_mem_ancestralBlanket G A hA i l j (hTA hl) hld hjl hjd)
  rw [ancestral_sink_conditional_eq_ratio G val K hNO hK A hA i hs,
    ancestral_sink_conditional_eq_ratio G val K hNO hK A hA i hs,
    hm A hA (Finset.Subset.refl _),
    hm (A.erase i) (observedAncestral_erase G A hA i hs) (Finset.erase_subset _ _)]

/-- Blanket reduction is proved by averaging over the unused coordinates. -/
theorem ancestral_sink_conditional_eq_blanket (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (w : FullAssign val) :
    conditional (joint G val K) (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      conditional (joint G val K) (valueEvent val w i) (assignmentEvent val w (ancestralBlanket G A i)) :=
  conditional_assignment_eq_of_congr val _ (joint_pos G val K hK) _ _
    (ancestralBlanket_subset_erase G A i) i (Finset.notMem_erase _ _)
    (ancestral_sink_conditional_congr G val K hNO hK A hA i hs) w

/-- Event-level local independence on every observed ancestral set. -/
theorem joint_ancestral_local_equation (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (w : FullAssign val) :
    CondIndependent (joint G val K) (valueEvent val w i) (assignmentEvent val w (A.erase i))
      (assignmentEvent val w (ancestralBlanket G A i)) :=
  condIndependent_assignment_of_congr val _ (joint_pos G val K hK) _ _
    (ancestralBlanket_subset_erase G A i) i (Finset.notMem_erase _ _)
    (ancestral_sink_conditional_congr G val K hNO hK A hA i hs) w

/-- All ancestral-set sink equations, using the actual retained-graph
district and its parents. This is not a definition by global separation. -/
def AncestralLocalMarkov (p : FullAssign val → ℝ) : Prop :=
  ∀ (A : Finset (Fin n)), ObservedAncestral G A → ∀ i : Fin n, ObservedSink G A i →
    ∀ w : FullAssign val, CondIndependent p (valueEvent val w i)
      (assignmentEvent val w (A.erase i)) (assignmentEvent val w (inducedAncestralBlanket G A i))

/-- At the manuscript's degree bound, the reconstructed law satisfies every
ancestral local equation with the genuine induced district blanket. -/
theorem joint_ancestralLocalMarkov (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (hdegree : ∀ x, cDegree G x ≤ 1) :
    AncestralLocalMarkov G val (joint G val K) := by
  intro A hA i hs w
  rw [inducedAncestralBlanket_eq G A i hs.1 hdegree]
  exact joint_ancestral_local_equation G val K hNO hK A hA i hs w

end MeraConstraints.GlobalModel.KernelReconstruction
