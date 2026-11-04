import MeraConstraints.Examples.InstrumentalAppendix

/-!
# Exact Appendix B IV H-representation

Every feasible printed H vector is reconstructed as a simplex mixture of
the printed response columns. Seven independent margin equations express
twelve distinct-column weights in terms of five free weights t0,...,t4.
The other four profile weights are zero. All twelve retained weights must
be nonnegative.

The finite Fourier–Motzkin certificate below eliminates the free weights
in order and reconstructs them in reverse order as maxima of lower bounds.
Every lower/upper comparison is checked by linear arithmetic in Lean.
The final inequalities follow from the literal twelve H inequalities and
two normalizations. No strict positivity, division by a probability, or
external solver is used; boundary points are included.

The certificate is generated reproducibly by scripts/generate-iv-hrep.mjs.
The generator is outside the proof kernel: all its output is an explicit
Lean proof. The resulting HRep has exactly the manuscript matrices.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

set_option maxHeartbeats 4000000 in
/-- Reverse H inclusion, with explicit nonnegative response-profile weights. -/
theorem printed_feasible_mixture {p : Fin 8 → ℝ} (hp : PrintedFeasible p) :
    p ∈ Polytope.mixture printedB := by
  have hpvec : p = ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7] := by
    funext i
    fin_cases i <;> rfl
  have hi0 := hp.1 (0 : Fin 12)
  have hi1 := hp.1 (1 : Fin 12)
  have hi2 := hp.1 (2 : Fin 12)
  have hi3 := hp.1 (3 : Fin 12)
  have hi4 := hp.1 (4 : Fin 12)
  have hi5 := hp.1 (5 : Fin 12)
  have hi6 := hp.1 (6 : Fin 12)
  have hi7 := hp.1 (7 : Fin 12)
  have hi8 := hp.1 (8 : Fin 12)
  have hi9 := hp.1 (9 : Fin 12)
  have hi10 := hp.1 (10 : Fin 12)
  have hi11 := hp.1 (11 : Fin 12)
  have he0 := hp.2 (0 : Fin 2)
  have he1 := hp.2 (1 : Fin 2)
  change (∑ i : Fin 8, ![0,0,0,0,-1,0,0,0] i * p i) ≤ 0 at hi0
  change (∑ i : Fin 8, ![-1,-1,-1,0,0,1,0,0] i * p i) ≤ 0 at hi1
  change (∑ i : Fin 8, ![0,1,0,0,-1,-1,-1,0] i * p i) ≤ 0 at hi2
  change (∑ i : Fin 8, ![-1,0,0,0,0,0,0,0] i * p i) ≤ 0 at hi3
  change (∑ i : Fin 8, ![0,0,1,0,1,0,0,0] i * p i) ≤ 1 at hi4
  change (∑ i : Fin 8, ![1,0,0,0,0,0,1,0] i * p i) ≤ 1 at hi5
  change (∑ i : Fin 8, ![0,0,0,0,0,-1,0,0] i * p i) ≤ 0 at hi6
  change (∑ i : Fin 8, ![0,0,0,0,1,1,1,0] i * p i) ≤ 1 at hi7
  change (∑ i : Fin 8, ![0,-1,0,0,0,0,0,0] i * p i) ≤ 0 at hi8
  change (∑ i : Fin 8, ![1,1,1,0,0,0,0,0] i * p i) ≤ 1 at hi9
  change (∑ i : Fin 8, ![0,0,0,0,0,0,-1,0] i * p i) ≤ 0 at hi10
  change (∑ i : Fin 8, ![0,0,-1,0,0,0,0,0] i * p i) ≤ 0 at hi11
  change (∑ i : Fin 8, ![-1,-1,-1,-1,0,0,0,0] i * p i) = -1 at he0
  change (∑ i : Fin 8, ![0,0,0,0,-1,-1,-1,-1] i * p i) = -1 at he1
  rw [hpvec] at hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9 hi10 hi11 he0 he1
  norm_num [Fin.sum_univ_succ] at hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9 hi10 hi11 he0 he1
  -- Fully eliminated inequalities: consequences of the printed H rows.
  have h5_0 : 0 ≤ p 0 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_1 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_2 : 0 ≤ p 4 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_3 : 0 ≤ p 3 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_4 : 0 ≤ p 5 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_5 : 0 ≤ p 1 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_6 : 0 ≤ 2 * p 0 + p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_7 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 5 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_8 : 0 ≤ p 0 + p 3 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_9 : 0 ≤ p 3 + p 4 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_10 : 0 ≤ p 2 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_11 : 0 ≤ p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_12 : 0 ≤ p 0 + p 2 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_13 : 0 ≤ p 0 + p 1 + p 2 - p 5 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_14 : 0 ≤ -p 1 + p 4 + p 5 + p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_15 : 0 ≤ p 4 + p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_16 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 4 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_17 : 0 ≤ p 0 + p 1 + p 3 - p 4 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_18 : 0 ≤ 2 * p 0 + p 1 + p 2 + p 3 - p 4 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_19 : 0 ≤ 2 * p 0 + 2 * p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_20 : 0 ≤ p 0 + p 3 + p 5 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_21 : 0 ≤ p 0 + p 1 + p 3 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_22 : 0 ≤ p 1 + p 2 + p 3 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_23 : 0 ≤ p 1 + p 3 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_24 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_25 : 0 ≤ p 0 + 2 * p 1 + p 2 + p 3 - p 5 - p 6 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_26 : 0 ≤ p 3 + p 4 + p 5 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  have h5_27 : 0 ≤ p 1 + p 3 + p 4 := by linarith only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, he0, he1]
  -- Reconstruct free column weight t4 from its interval of feasible values.
  let t4 : ℝ := max (-(0)) (max (-(p 0 + p 1 + p 3 - p 4 - p 6)) (-(p 1 + p 3 - p 6)))
  have l4_0 : (-(0)) ≤ t4 := le_max_left _ _
  have l4_1 : (-(p 0 + p 1 + p 3 - p 4 - p 6)) ≤ t4 := le_trans (le_max_left _ _) (le_max_right _ _)
  have l4_2 : (-(p 1 + p 3 - p 6)) ≤ t4 := le_trans (le_trans (le_rfl) (le_max_right _ _)) (le_max_right _ _)
  have u4_0 : t4 ≤ ((p 2)) := by
    dsimp only [t4]
    exact (max_le (by linarith only [h5_10]) (max_le (by linarith only [h5_16]) (by linarith only [h5_22])))
  have u4_1 : t4 ≤ ((p 6)) := by
    dsimp only [t4]
    exact (max_le (by linarith only [h5_11]) (max_le (by linarith only [h5_17]) (by linarith only [h5_23])))
  have u4_2 : t4 ≤ ((p 0 + p 2)) := by
    dsimp only [t4]
    exact (max_le (by linarith only [h5_12]) (max_le (by linarith only [h5_18]) (by linarith only [h5_24])))
  have u4_3 : t4 ≤ ((p 0 + p 1 + p 2 - p 5)) := by
    dsimp only [t4]
    exact (max_le (by linarith only [h5_13]) (max_le (by linarith only [h5_19]) (by linarith only [h5_25])))
  have u4_4 : t4 ≤ ((-p 1 + p 4 + p 5 + p 6)) := by
    dsimp only [t4]
    exact (max_le (by linarith only [h5_14]) (max_le (by linarith only [h5_20]) (by linarith only [h5_26])))
  have u4_5 : t4 ≤ ((p 4 + p 6)) := by
    dsimp only [t4]
    exact (max_le (by linarith only [h5_15]) (max_le (by linarith only [h5_21]) (by linarith only [h5_27])))
  have h4_0 : 0 ≤ t4 := by linarith only [l4_0]
  have h4_1 : 0 ≤ p 0 := by linarith only [h5_0]
  have h4_2 : 0 ≤ -t4 + p 2 := by linarith only [u4_0]
  have h4_3 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [h5_1]
  have h4_4 : 0 ≤ p 4 := by linarith only [h5_2]
  have h4_5 : 0 ≤ -t4 + p 6 := by linarith only [u4_1]
  have h4_6 : 0 ≤ p 3 := by linarith only [h5_3]
  have h4_7 : 0 ≤ p 5 := by linarith only [h5_4]
  have h4_8 : 0 ≤ t4 + p 0 + p 1 + p 3 - p 4 - p 6 := by linarith only [l4_1]
  have h4_9 : 0 ≤ p 1 := by linarith only [h5_5]
  have h4_10 : 0 ≤ t4 + p 1 + p 3 - p 6 := by linarith only [l4_2]
  have h4_11 : 0 ≤ -t4 + p 0 + p 2 := by linarith only [u4_2]
  have h4_12 : 0 ≤ 2 * p 0 + p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [h5_6]
  have h4_13 : 0 ≤ -t4 + p 0 + p 1 + p 2 - p 5 := by linarith only [u4_3]
  have h4_14 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 5 - p 6 := by linarith only [h5_7]
  have h4_15 : 0 ≤ -t4 - p 1 + p 4 + p 5 + p 6 := by linarith only [u4_4]
  have h4_16 : 0 ≤ p 0 + p 3 := by linarith only [h5_8]
  have h4_17 : 0 ≤ -t4 + p 4 + p 6 := by linarith only [u4_5]
  have h4_18 : 0 ≤ p 3 + p 4 := by linarith only [h5_9]
  -- Reconstruct free column weight t3 from its interval of feasible values.
  let t3 : ℝ := max (-(0)) (max (-(-t4 + p 0 + p 2 - p 5)) (-(-t4 - p 1 + p 4 + p 6)))
  have l3_0 : (-(0)) ≤ t3 := le_max_left _ _
  have l3_1 : (-(-t4 + p 0 + p 2 - p 5)) ≤ t3 := le_trans (le_max_left _ _) (le_max_right _ _)
  have l3_2 : (-(-t4 - p 1 + p 4 + p 6)) ≤ t3 := le_trans (le_trans (le_rfl) (le_max_right _ _)) (le_max_right _ _)
  have u3_0 : t3 ≤ ((p 5)) := by
    dsimp only [t3]
    exact (max_le (by linarith only [h4_7]) (max_le (by linarith only [h4_11]) (by linarith only [h4_15])))
  have u3_1 : t3 ≤ ((t4 + p 0 + p 1 + p 3 - p 4 - p 6)) := by
    dsimp only [t3]
    exact (max_le (by linarith only [h4_8]) (max_le (by linarith only [h4_12]) (by linarith only [h4_16])))
  have u3_2 : t3 ≤ ((p 1)) := by
    dsimp only [t3]
    exact (max_le (by linarith only [h4_9]) (max_le (by linarith only [h4_13]) (by linarith only [h4_17])))
  have u3_3 : t3 ≤ ((t4 + p 1 + p 3 - p 6)) := by
    dsimp only [t3]
    exact (max_le (by linarith only [h4_10]) (max_le (by linarith only [h4_14]) (by linarith only [h4_18])))
  have h3_0 : 0 ≤ t3 := by linarith only [l3_0]
  have h3_1 : 0 ≤ t4 := by linarith only [h4_0]
  have h3_2 : 0 ≤ -t3 + p 5 := by linarith only [u3_0]
  have h3_3 : 0 ≤ p 0 := by linarith only [h4_1]
  have h3_4 : 0 ≤ -t3 + t4 + p 0 + p 1 + p 3 - p 4 - p 6 := by linarith only [u3_1]
  have h3_5 : 0 ≤ -t4 + p 2 := by linarith only [h4_2]
  have h3_6 : 0 ≤ t3 - t4 + p 0 + p 2 - p 5 := by linarith only [l3_1]
  have h3_7 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [h4_3]
  have h3_8 : 0 ≤ -t3 + p 1 := by linarith only [u3_2]
  have h3_9 : 0 ≤ p 4 := by linarith only [h4_4]
  have h3_10 : 0 ≤ -t3 + t4 + p 1 + p 3 - p 6 := by linarith only [u3_3]
  have h3_11 : 0 ≤ -t4 + p 6 := by linarith only [h4_5]
  have h3_12 : 0 ≤ t3 - t4 - p 1 + p 4 + p 6 := by linarith only [l3_2]
  have h3_13 : 0 ≤ p 3 := by linarith only [h4_6]
  -- Reconstruct free column weight t2 from its interval of feasible values.
  let t2 : ℝ := max (-(0)) (-(t3 - t4 - p 1 + p 6))
  have l2_0 : (-(0)) ≤ t2 := le_max_left _ _
  have l2_1 : (-(t3 - t4 - p 1 + p 6)) ≤ t2 := le_trans (le_rfl) (le_max_right _ _)
  have u2_0 : t2 ≤ ((-t3 + p 1)) := by
    dsimp only [t2]
    exact (max_le (by linarith only [h3_8]) (by linarith only [h3_11]))
  have u2_1 : t2 ≤ ((p 4)) := by
    dsimp only [t2]
    exact (max_le (by linarith only [h3_9]) (by linarith only [h3_12]))
  have u2_2 : t2 ≤ ((-t3 + t4 + p 1 + p 3 - p 6)) := by
    dsimp only [t2]
    exact (max_le (by linarith only [h3_10]) (by linarith only [h3_13]))
  have h2_0 : 0 ≤ t2 := by linarith only [l2_0]
  have h2_1 : 0 ≤ t3 := by linarith only [h3_0]
  have h2_2 : 0 ≤ t4 := by linarith only [h3_1]
  have h2_3 : 0 ≤ -t2 - t3 + p 1 := by linarith only [u2_0]
  have h2_4 : 0 ≤ t2 + t3 - t4 - p 1 + p 6 := by linarith only [l2_1]
  have h2_5 : 0 ≤ -t2 + p 4 := by linarith only [u2_1]
  have h2_6 : 0 ≤ -t2 - t3 + t4 + p 1 + p 3 - p 6 := by linarith only [u2_2]
  have h2_7 : 0 ≤ -t3 + p 5 := by linarith only [h3_2]
  have h2_8 : 0 ≤ p 0 := by linarith only [h3_3]
  have h2_9 : 0 ≤ -t3 + t4 + p 0 + p 1 + p 3 - p 4 - p 6 := by linarith only [h3_4]
  have h2_10 : 0 ≤ -t4 + p 2 := by linarith only [h3_5]
  have h2_11 : 0 ≤ t3 - t4 + p 0 + p 2 - p 5 := by linarith only [h3_6]
  have h2_12 : 0 ≤ p 0 + p 1 + p 2 + p 3 - p 4 - p 5 - p 6 := by linarith only [h3_7]
  -- Reconstruct free column weight t1 from its interval of feasible values.
  let t1 : ℝ := max (-(0)) (-(t3 - t4 + p 2 - p 5))
  have l1_0 : (-(0)) ≤ t1 := le_max_left _ _
  have l1_1 : (-(t3 - t4 + p 2 - p 5)) ≤ t1 := le_trans (le_rfl) (le_max_right _ _)
  have u1_0 : t1 ≤ ((-t3 + p 5)) := by
    dsimp only [t1]
    exact (max_le (by linarith only [h2_7]) (by linarith only [h2_10]))
  have u1_1 : t1 ≤ ((p 0)) := by
    dsimp only [t1]
    exact (max_le (by linarith only [h2_8]) (by linarith only [h2_11]))
  have u1_2 : t1 ≤ ((-t3 + t4 + p 0 + p 1 + p 3 - p 4 - p 6)) := by
    dsimp only [t1]
    exact (max_le (by linarith only [h2_9]) (by linarith only [h2_12]))
  have h1_0 : 0 ≤ t1 := by linarith only [l1_0]
  have h1_1 : 0 ≤ t2 := by linarith only [h2_0]
  have h1_2 : 0 ≤ t3 := by linarith only [h2_1]
  have h1_3 : 0 ≤ t4 := by linarith only [h2_2]
  have h1_4 : 0 ≤ -t2 - t3 + p 1 := by linarith only [h2_3]
  have h1_5 : 0 ≤ -t1 - t3 + p 5 := by linarith only [u1_0]
  have h1_6 : 0 ≤ t1 + t3 - t4 + p 2 - p 5 := by linarith only [l1_1]
  have h1_7 : 0 ≤ t2 + t3 - t4 - p 1 + p 6 := by linarith only [h2_4]
  have h1_8 : 0 ≤ -t1 + p 0 := by linarith only [u1_1]
  have h1_9 : 0 ≤ -t2 + p 4 := by linarith only [h2_5]
  have h1_10 : 0 ≤ -t1 - t3 + t4 + p 0 + p 1 + p 3 - p 4 - p 6 := by linarith only [u1_2]
  have h1_11 : 0 ≤ -t2 - t3 + t4 + p 1 + p 3 - p 6 := by linarith only [h2_6]
  -- Reconstruct free column weight t0 from its interval of feasible values.
  let t0 : ℝ := max (-(0)) (-(-t3 + t4 + p 1 + p 3 - p 4 - p 6))
  have l0_0 : (-(0)) ≤ t0 := le_max_left _ _
  have l0_1 : (-(-t3 + t4 + p 1 + p 3 - p 4 - p 6)) ≤ t0 := le_trans (le_rfl) (le_max_right _ _)
  have u0_0 : t0 ≤ ((-t1 + p 0)) := by
    dsimp only [t0]
    exact (max_le (by linarith only [h1_8]) (by linarith only [h1_10]))
  have u0_1 : t0 ≤ ((-t2 + p 4)) := by
    dsimp only [t0]
    exact (max_le (by linarith only [h1_9]) (by linarith only [h1_11]))
  have h0_0 : 0 ≤ t0 := by linarith only [l0_0]
  have h0_1 : 0 ≤ t1 := by linarith only [h1_0]
  have h0_2 : 0 ≤ t2 := by linarith only [h1_1]
  have h0_3 : 0 ≤ t3 := by linarith only [h1_2]
  have h0_4 : 0 ≤ t4 := by linarith only [h1_3]
  have h0_5 : 0 ≤ -t0 - t1 + p 0 := by linarith only [u0_0]
  have h0_6 : 0 ≤ -t2 - t3 + p 1 := by linarith only [h1_4]
  have h0_7 : 0 ≤ -t1 - t3 + p 5 := by linarith only [h1_5]
  have h0_8 : 0 ≤ t1 + t3 - t4 + p 2 - p 5 := by linarith only [h1_6]
  have h0_9 : 0 ≤ -t0 - t2 + p 4 := by linarith only [u0_1]
  have h0_10 : 0 ≤ t2 + t3 - t4 - p 1 + p 6 := by linarith only [h1_7]
  have h0_11 : 0 ≤ t0 - t3 + t4 + p 1 + p 3 - p 4 - p 6 := by linarith only [l0_1]
  -- Four duplicate-column profiles receive zero; all margins are preserved.
  let q : Fin 16 → ℝ :=
    ![t0, t1, 0, p 0 - t0 - t1, t2, t3, p 1 - t2 - t3, 0,
      t4, p 5 - t1 - t3, 0, p 2 - p 5 + t1 + t3 - t4,
      p 4 - t0 - t2, p 3 - p 4 - p 6 + p 1 + t0 - t3 + t4,
      p 6 - p 1 + t2 + t3 - t4, 0]
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [q] <;>
      linarith only [h0_0, h0_1, h0_2, h0_3, h0_4, h0_5, h0_6, h0_7, h0_8, h0_9, h0_10, h0_11]
  · norm_num [q, Fin.sum_univ_succ]
    linarith only [he0]
  · funext i
    conv_rhs => rw [hpvec]
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, printedB, q, Fin.sum_univ_succ] <;>
      linarith only [he0, he1]

theorem printed_mixture_iff_feasible (p : Fin 8 → ℝ) :
    p ∈ Polytope.mixture printedB ↔ PrintedFeasible p :=
  ⟨printed_mixture_feasible, printed_feasible_mixture⟩

/-- Literal Appendix B H data, now with kernel-checked V-to-H exactness. -/
noncomputable def printedHRep : Polytope.HRep printedB (Fin 12) (Fin 2) where
  inequalities := printedHi
  upper := printedUpper
  equalities := printedHe
  target := printedTarget
  exact_representation := printed_mixture_iff_feasible

end MeraConstraints.Examples.Instrumental.Appendix
