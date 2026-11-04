import MeraConstraints.HiddenGraph.AncestralSets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Reverse topological orders and multiplicative diamond identities

An order is a literal list of vertices, removing an available observed sink
at each step until no vertex remains. Its validity is checked against the
original directed graph. A product assigns a weight to each removal.

If the two ways of removing any pair of available sinks have the same
two-step product, then every valid removal order has the same product.
The proof deletes a chosen sink from a second order and commutes it through
that order one step at a time. This is a finite graph/algebra theorem, not
an assumed invariance property of the manuscript's observed products.
-/

namespace MeraConstraints.HiddenGraph.EliminationOrder

variable {n ℓ : ℕ} (G : Graph n ℓ)

def Valid : Finset (Fin n) → List (Fin n) → Prop
  | A, [] => A = ∅
  | A, i :: s => ObservedSink G A i ∧ Valid (A.erase i) s

variable {M : Type*} [CommMonoid M]

def product (W : Finset (Fin n) → Fin n → M) : Finset (Fin n) → List (Fin n) → M
  | _, [] => 1
  | A, i :: s => W A i * product W (A.erase i) s

theorem erase_twice_comm (A : Finset (Fin n)) (i j : Fin n) :
    (A.erase i).erase j = (A.erase j).erase i := by
  ext k
  simp [Finset.mem_erase, and_left_comm]

/-- Deleting a vertex from a valid sink order leaves a valid order on the
remaining set, without making any claim about its product. -/
theorem valid_erase (A : Finset (Fin n)) (s : List (Fin n)) (hs : Valid G A s) (i : Fin n) :
    Valid G (A.erase i) (s.erase i) := by
  induction s generalizing A with
  | nil =>
    have hA : A = ∅ := hs
    subst A
    rfl
  | cons j s ih =>
    by_cases hji : j = i
    · subst j
      simpa only [List.erase_cons_head] using hs.2
    · rw [List.erase_cons_tail (by simpa using hji)]
      refine ⟨⟨Finset.mem_erase.mpr ⟨hji, hs.1.1⟩, ?_⟩, ?_⟩
      · intro k hk
        exact hs.1.2 k (Finset.mem_erase.mp hk).2
      · simpa only [erase_twice_comm] using ih (A.erase j) hs.2

theorem product_empty (W : Finset (Fin n) → Fin n → M) (s : List (Fin n))
    (hs : Valid G ∅ s) : product W ∅ s = 1 := by
  cases s with
  | nil => rfl
  | cons i s => exact (Finset.notMem_empty i hs.1.1).elim

def Diamonds (W : Finset (Fin n) → Fin n → M) : Prop :=
  ∀ A, ObservedAncestral G A → ∀ i j, ObservedSink G A i → ObservedSink G A j → i ≠ j →
    W A i * W (A.erase i) j = W A j * W (A.erase j) i

/-- Move any available sink to the first position using the two-step
diamond equation. The remaining list is its literal deletion. -/
theorem product_extract (W : Finset (Fin n) → Fin n → M) (hW : Diamonds G W)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (s : List (Fin n)) (hs : Valid G A s)
    (i : Fin n) (hi : ObservedSink G A i) :
    product W A s = W A i * product W (A.erase i) (s.erase i) := by
  induction s generalizing A with
  | nil =>
    have hAe : A = ∅ := hs
    subst A
    exact (Finset.notMem_empty i hi.1).elim
  | cons j s ih =>
    by_cases hji : j = i
    · subst j
      simp only [product, List.erase_cons_head]
    · have hi' : ObservedSink G (A.erase j) i :=
        ⟨Finset.mem_erase.mpr ⟨Ne.symm hji, hi.1⟩,
          fun k hk => hi.2 k (Finset.mem_erase.mp hk).2⟩
      have htail := ih (A.erase j) (observedAncestral_erase G A hA j hs.1) hs.2 hi'
      rw [product, List.erase_cons_tail (by simpa using hji), product, htail]
      rw [show (A.erase j).erase i = (A.erase i).erase j from erase_twice_comm _ _ _]
      rw [← mul_assoc, hW A hA j i hs.1 hi hji, mul_assoc]

/-- Every two valid reverse topological orders give the same product when
all available-sink diamonds commute. -/
theorem products_eq (W : Finset (Fin n) → Fin n → M) (hW : Diamonds G W)
    (A : Finset (Fin n)) (hA : ObservedAncestral G A) (s t : List (Fin n))
    (hs : Valid G A s) (ht : Valid G A t) : product W A s = product W A t := by
  induction t generalizing A s with
  | nil =>
    have hAe : A = ∅ := ht
    subst A
    exact product_empty G W s hs
  | cons i t ih =>
    rw [product_extract G W hW A hA s hs i ht.1, product]
    congr 1
    exact ih (A.erase i) (observedAncestral_erase G A hA i ht.1) (s.erase i) (valid_erase G A s hs i) ht.2

end MeraConstraints.HiddenGraph.EliminationOrder
