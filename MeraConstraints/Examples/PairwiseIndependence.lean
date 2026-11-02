import MeraConstraints.Probability.Finite
import Mathlib.Tactic.NormNum

/-!
# Pairwise independence does not imply district-vector independence

The response-variable explanation at `main-revised.tex:305` gives pairwise
independence equations, while the completeness proof at `appendix.tex:270`
uses mutual independence of whole district vectors. The latter is the
intended graphical-model condition; the displayed pairwise equations alone
are insufficient.

This exact finite example makes the distinction checkable. Draw two fair
independent bits `X,Y` and put `Z = X xor Y`. Each of the three marginal
laws is fair, and each pair has the product of those laws. Their joint law
is nevertheless not the product: `(false,false,true)` is impossible but
the product assigns it probability `1/8`.

This is a counterexample to replacing the manuscript's intended mutual
independence by pairwise equations, not a counterexample to its completeness
theorem under the usual independent-district semantics.
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
