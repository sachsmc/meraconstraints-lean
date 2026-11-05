import MeraConstraints.GlobalModel.AncestralKernels
import MeraConstraints.HiddenGraph.AncestralBlanket
import MeraConstraints.Probability.AssignmentConditioning

/-!
# Local Markov equations on every ancestral set

After equation (`eqn:ancmargin`), Step 2 of the proof of Proposition 4
(`prop:nontrivial`) divides the probability of an ancestral set `A` by the
probability of `A \ {V}`, for a variable `V` with no children in `A`. The factors of
the other districts cancel, and (O) shows that the remaining ratio depends only on
`V`, the other members of its district that lie in `A`, and their external parents.
Averaging over the other variables gives the conditional independence of `V` from
the rest of `A` given these variables (`joint_ancestral_local_equation`).

At c-degree at most 1, these members form the district of `V` in the subgraph
induced by `A` (`inducedAncestralBlanket_eq`). So, for positive kernels, `joint K`
satisfies the ordered local Markov property on the subgraph induced by every
ancestral set (`joint_ancestralLocalMarkov`). That the conditional independencies implied by the
graph (`GlobalMarkov`) give the same equations is shown in `GlobalModel.GlobalToLocal`.
The converse for an arbitrary distribution is not formalized (see the Scope chapter);
for `joint K`, `GlobalMarkov` is proved directly in `GlobalModel.MoralMarkov`.
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

/-- For `V_i` with no children in `A`, the conditional of `V_i` given `A \ {V_i}` under
`joint K` is the ratio of the margins of its own district for `A` and for `A \ {V_i}`. -/
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

/-- The conditional of `V_i` given `A \ {V_i}` depends only on the value of `V_i` and
the values on its blanket in `A`: the other members of its district in `A` and their
external parents. -/
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

/-- The conditional of `V_i` given `A \ {V_i}` equals its conditional given its
blanket. -/
theorem ancestral_sink_conditional_eq_blanket (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (w : FullAssign val) :
    conditional (joint G val K) (valueEvent val w i) (assignmentEvent val w (A.erase i)) =
      conditional (joint G val K) (valueEvent val w i) (assignmentEvent val w (ancestralBlanket G A i)) :=
  conditional_assignment_eq_of_congr val _ (joint_pos G val K hK) _ _
    (ancestralBlanket_subset_erase G A i) i (Finset.notMem_erase _ _)
    (ancestral_sink_conditional_congr G val K hNO hK A hA i hs) w

/-- The value of `V_i` is independent of the values on `A \ {V_i}` given the values on
its blanket in `A`, for every ancestral set `A`. -/
theorem joint_ancestral_local_equation (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) (w : FullAssign val) :
    CondIndependent (joint G val K) (valueEvent val w i) (assignmentEvent val w (A.erase i))
      (assignmentEvent val w (ancestralBlanket G A i)) :=
  condIndependent_assignment_of_congr val _ (joint_pos G val K hK) _ _
    (ancestralBlanket_subset_erase G A i) i (Finset.notMem_erase _ _)
    (ancestral_sink_conditional_congr G val K hNO hK A hA i hs) w

/-- The ordered local Markov property on every ancestral set `A`: for each `V_i` with
no children in `A`, the value of `V_i` is independent of the values on `A \ {V_i}` given
its blanket in the subgraph induced by `A`. -/
def AncestralLocalMarkov (p : FullAssign val → ℝ) : Prop :=
  ∀ (A : Finset (Fin n)), ObservedAncestral G A → ∀ i : Fin n, ObservedSink G A i →
    ∀ w : FullAssign val, CondIndependent p (valueEvent val w i)
      (assignmentEvent val w (A.erase i)) (assignmentEvent val w (inducedAncestralBlanket G A i))

/-- At c-degree at most 1, `joint K` satisfies `AncestralLocalMarkov`. -/
theorem joint_ancestralLocalMarkov (K : Kernels G val) (hNO : NormalizedOrdered G val K)
    (hK : Positive G val K) (hdegree : ∀ x, cDegree G x ≤ 1) :
    AncestralLocalMarkov G val (joint G val K) := by
  intro A hA i hs w
  rw [inducedAncestralBlanket_eq G A i hs.1 hdegree]
  exact joint_ancestral_local_equation G val K hNO hK A hA i hs w

end MeraConstraints.GlobalModel.KernelReconstruction
