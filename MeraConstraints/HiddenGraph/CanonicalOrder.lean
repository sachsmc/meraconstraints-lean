import MeraConstraints.HiddenGraph.EliminationOrder

/-!
# The topological order as an elimination order

The observed variables are numbered in a topological order. Removing the
variables `k-1`, `k-2`, …, `0` in turn is a valid order for the set of the first
`k` variables (`prefixOrder_valid`), and the product along it is the product over
those variables of the weight at the set of variables up to and including each
one (`prefixOrder_product`). With `k = n` this gives the product over all
variables (`fullOrder_product`).
-/

namespace MeraConstraints.HiddenGraph.EliminationOrder

variable {n ℓ : ℕ} (G : Graph n ℓ)

abbrev before (k : ℕ) : Finset (Fin n) := ancestralExtension (∅ : Finset (Fin n)) k

def prefixOrder : (k : ℕ) → k ≤ n → List (Fin n)
  | 0, _ => []
  | k + 1, hk => ⟨k, Nat.lt_of_succ_le hk⟩ :: prefixOrder k (Nat.le_of_succ_le hk)

theorem before_erase (i : Fin n) : (before (i.val + 1)).erase i = before i.val := by
  have hi : i ∉ before i.val := by simp [before]
  change (ancestralExtension (∅ : Finset (Fin n)) (i.val + 1)).erase i =
    ancestralExtension ∅ i.val
  rw [ancestralExtension_succ]
  exact Finset.erase_insert hi

theorem prefixOrder_valid (k : ℕ) (hk : k ≤ n) : Valid G (before k) (prefixOrder k hk) := by
  induction k with
  | zero => simp [prefixOrder, Valid, before]
  | succ k ih =>
    let i : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
    change ObservedSink G (before (k + 1)) i ∧ Valid G ((before (k + 1)).erase i) _
    constructor
    · exact ancestralExtension_sink G ∅ (by simp [ObservedAncestral]) i (by simp)
    · rw [show (before (k + 1)).erase i = before k from before_erase i]
      exact ih (Nat.le_of_succ_le hk)

variable {M : Type*} [CommMonoid M]

theorem prefixOrder_product (W : Finset (Fin n) → Fin n → M) (k : ℕ) (hk : k ≤ n) :
    product W (before k) (prefixOrder k hk) = ∏ i ∈ before k, W (before (i.val + 1)) i := by
  induction k with
  | zero => simp [prefixOrder, product, before]
  | succ k ih =>
    let i : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
    change W (before (k + 1)) i * product W ((before (k + 1)).erase i)
      (prefixOrder k (Nat.le_of_succ_le hk)) = _
    rw [show (before (k + 1)).erase i = before k from before_erase i, ih]
    have hset : before (k + 1) = insert i (before k) := ancestralExtension_succ ∅ i
    have hnot : i ∉ before k := by simp [before, i]
    conv_rhs => rw [hset, Finset.prod_insert hnot]

theorem fullOrder_valid : Valid G Finset.univ (prefixOrder n (Nat.le_refl n)) := by
  simpa only [before, ancestralExtension_full] using prefixOrder_valid G n (Nat.le_refl n)

theorem fullOrder_product (W : Finset (Fin n) → Fin n → M) :
    product W Finset.univ (prefixOrder n (Nat.le_refl n)) = ∏ i, W (before (i.val + 1)) i := by
  simpa only [before, ancestralExtension_full] using prefixOrder_product W n (Nat.le_refl n)

end MeraConstraints.HiddenGraph.EliminationOrder
