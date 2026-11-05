import MeraConstraints.HiddenGraph.CanonicalOrder
import Mathlib.Data.Finset.Max

/-!
# An elimination order for every set of observed variables

Because the numbering is topological, the variable with the largest index in a
set is a sink of it. Removing it repeatedly gives a valid order for every set of
observed variables, including ancestral sets that are not initial segments of the
numbering (`exists_valid`). `selectedOrder` is one such order, chosen for each
set. By `products_eq`, the product along it does not depend on the choice.
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
