import MeraConstraints.HiddenGraph.Ancestry

/-!
# Ancestral sets of observed variables

In the proof of Proposition 4 (`prop:nontrivial`) in the Supplementary Materials
(equation `eqn:ancmargin`), `A` is a set of observed variables that contains all
observed ancestors of its elements. `ObservedAncestral` is this condition,
including ancestors reached by paths that leave a district. Its intersection with
a district is a closed set (`ancestral_district_fullClosed`), which is what
equations (O) require.

To sum out the variables outside `A` one at a time, add to `A` the first `k`
variables in the topological order (`ancestralExtension`). The result is again
an ancestral set (`ancestralExtension_ancestral`), and the variable with index
`k`, if not in `A`, is a sink of the extension by `k + 1` variables
(`ancestralExtension_sink`).
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

def ObservedAncestral (A : Finset (Fin n)) : Prop :=
  ∀ i ∈ A, ∀ j, ObservedAncestor G j i → j ∈ A

/-- `i` is in `A` and has no child in `A`. -/
def ObservedSink (A : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ A ∧ ∀ j ∈ A, i ∉ G.observed.parents j

theorem observedAncestral_iff_parents (A : Finset (Fin n)) :
    ObservedAncestral G A ↔ ∀ i ∈ A, ∀ j ∈ G.observed.parents i, j ∈ A := by
  constructor
  · intro h i hi j hj
    exact h i hi j (observedAncestor_of_parent G hj)
  · intro h i hi j hji
    induction hji using Relation.ReflTransGen.head_induction_on with
    | refl => exact hi
    | @head j k hjk _ ih => exact h k ih j hjk

theorem observedAncestral_univ : ObservedAncestral G Finset.univ :=
  fun _ _ _ _ => Finset.mem_univ _

theorem observedAncestral_erase (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hs : ObservedSink G A i) : ObservedAncestral G (A.erase i) := by
  apply (observedAncestral_iff_parents G _).mpr
  intro j hj k hkj
  obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
  exact Finset.mem_erase.mpr ⟨fun hki => hs.2 j hjA (hki ▸ hkj),
    hA j hjA k (observedAncestor_of_parent G hkj)⟩

/-- The members of a district that lie in an ancestral set form a closed set. -/
theorem ancestral_district_fullClosed [DecidableEq (DistrictId G)]
    (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (d : DistrictId G) : FullClosed G d (A.filter (fun j => observedDistrict G j = d)) := by
  constructor
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hji hjd
    exact Finset.mem_filter.mpr ⟨hA i (Finset.mem_filter.mp hi).1 j hji, hjd⟩

/-- The set `A` together with the first `k` variables in the topological
order. -/
def ancestralExtension (A : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  A ∪ Finset.univ.filter (fun j => j.val < k)

@[simp] theorem mem_ancestralExtension (A : Finset (Fin n)) (k : ℕ) (j : Fin n) :
    j ∈ ancestralExtension A k ↔ j ∈ A ∨ j.val < k := by
  simp [ancestralExtension]

@[simp] theorem ancestralExtension_zero (A : Finset (Fin n)) : ancestralExtension A 0 = A := by
  ext j
  simp

@[simp] theorem ancestralExtension_full (A : Finset (Fin n)) : ancestralExtension A n = Finset.univ := by
  ext j
  simp [j.isLt]

theorem ancestralExtension_succ (A : Finset (Fin n)) (i : Fin n) :
    ancestralExtension A (i.val + 1) = insert i (ancestralExtension A i.val) := by
  ext j
  simp only [mem_ancestralExtension, Finset.mem_insert]
  constructor
  · rintro (hjA | hj)
    · exact Or.inr (Or.inl hjA)
    · by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (Or.inr (by
          have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
          omega))
  · rintro (hji | hjA | hj)
    · subst j
      exact Or.inr (Nat.lt_succ_self _)
    · exact Or.inl hjA
    · exact Or.inr (by omega)

theorem ancestralExtension_ancestral (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (k : ℕ) : ObservedAncestral G (ancestralExtension A k) := by
  intro i hi j hji
  apply (mem_ancestralExtension A k j).mpr
  rcases (mem_ancestralExtension A k i).mp hi with hiA | hik
  · exact Or.inl (hA i hiA j hji)
  · exact Or.inr (lt_of_le_of_lt (show j.val ≤ i.val from observedAncestor_le G hji) hik)

theorem ancestralExtension_sink (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (i : Fin n) (hi : i ∉ A) : ObservedSink G (ancestralExtension A (i.val + 1)) i := by
  refine ⟨(mem_ancestralExtension A _ i).mpr (Or.inr (Nat.lt_succ_self _)), ?_⟩
  intro j hj hij
  rcases (mem_ancestralExtension A _ j).mp hj with hjA | hjk
  · exact hi (hA j hjA i (observedAncestor_of_parent G hij))
  · have hlt := G.observed.parents_lt hij
    omega

end MeraConstraints.HiddenGraph
