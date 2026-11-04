import MeraConstraints.HiddenGraph.CanonicalOrder
import Mathlib.Data.Finset.Max

/-!
# An elimination order for every retained vertex set

The largest remaining observed label is a sink, since labels are
topological. This gives a valid order for every subset, including ancestral
sets which are not numeric prefixes. The chosen order is only an auxiliary
representative: the probabilistic product is independent of this choice.
-/

namespace MeraConstraints.HiddenGraph.EliminationOrder

variable {n ℓ : ℕ} (G : Graph n ℓ)

theorem exists_valid (A : Finset (Fin n)) : ∃ s, Valid G A s := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.Nonempty
    · let i := A.max' hA
      have hi : i ∈ A := Finset.max'_mem A hA
      obtain ⟨s, hs⟩ := ih (A.erase i) (Finset.erase_ssubset hi)
      refine ⟨i :: s, ⟨hi, ?_⟩, hs⟩
      intro j hj hij
      have hji : j ≤ i := Finset.le_max' A j hj
      exact (not_lt_of_ge hji) (G.observed.parents_lt hij)
    · exact ⟨[], Finset.not_nonempty_iff_eq_empty.mp hA⟩

noncomputable def selectedOrder (A : Finset (Fin n)) : List (Fin n) :=
  Classical.choose (exists_valid G A)

theorem selectedOrder_valid (A : Finset (Fin n)) : Valid G A (selectedOrder G A) :=
  Classical.choose_spec (exists_valid G A)

end MeraConstraints.HiddenGraph.EliminationOrder
