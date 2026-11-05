import MeraConstraints.Probability.Finite
import Mathlib.Tactic.NormNum

/-!
# Pairwise independence is not mutual independence

The proof of Proposition 3 (`prop:complete`) needs the response function
variables of different districts to be mutually independent. Pairwise
independence is not enough. This chapter gives a small example of the
difference.

Draw two independent fair bits `X` and `Y` and let `Z = X xor Y`. Each of `X`,
`Y`, `Z` is a fair bit, and each pair of them is independent. Their joint
distribution is nevertheless not the product of the three marginals:
`(false, false, true)` has probability zero, whereas the product gives it
probability `1/8`.

This does not contradict Proposition 3, whose hypothesis is mutual independence.
-/

namespace MeraConstraints.Examples.PairwiseIndependence

abbrev Sample := Bool × Bool

noncomputable def source : Sample → ℝ := uniformDist Sample
noncomputable def bitLaw : Bool → ℝ := uniformDist Bool

def X (s : Sample) : Bool := s.1
def Y (s : Sample) : Bool := s.2
def Z (s : Sample) : Bool := Bool.xor s.1 s.2

theorem source_mem_stdSimplex : source ∈ stdSimplex ℝ Sample :=
  uniformDist_mem_stdSimplex Sample

theorem marginal_X : pushforward X source = bitLaw := by
  funext b
  simp only [pushforward, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;>
    norm_num [pushforward, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, X, source, bitLaw, uniformDist]

theorem marginal_Y : pushforward Y source = bitLaw := by
  funext b
  simp only [pushforward, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;>
    norm_num [pushforward, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, Y, source, bitLaw, uniformDist]

theorem marginal_Z : pushforward Z source = bitLaw := by
  funext b
  simp only [pushforward, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;>
    norm_num [pushforward, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, Z, source, bitLaw, uniformDist]

theorem independent_XY :
    pushforward (fun s => (X s, Y s)) source = prodDist bitLaw bitLaw := by
  funext p
  simp only [pushforward, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [pushforward, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, X, Y, source, bitLaw, uniformDist, prodDist]

theorem independent_XZ :
    pushforward (fun s => (X s, Z s)) source = prodDist bitLaw bitLaw := by
  funext p
  simp only [pushforward, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [pushforward, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, X, Z, source, bitLaw, uniformDist, prodDist]

theorem independent_YZ :
    pushforward (fun s => (Y s, Z s)) source = prodDist bitLaw bitLaw := by
  funext p
  simp only [pushforward, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [pushforward, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, Y, Z, source, bitLaw, uniformDist, prodDist]

noncomputable def joint : (Bool × Bool × Bool) → ℝ :=
  pushforward (fun s => (X s, Y s, Z s)) source

theorem impossible_configuration : joint (false, false, true) = 0 := by
  norm_num [joint, pushforward, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, X, Y, Z]

theorem not_mutually_independent : joint ≠ prodDist bitLaw (prodDist bitLaw bitLaw) := by
  intro h
  have hh := congrFun h (false, false, true)
  rw [impossible_configuration] at hh
  norm_num [prodDist, bitLaw, uniformDist] at hh

end MeraConstraints.Examples.PairwiseIndependence
