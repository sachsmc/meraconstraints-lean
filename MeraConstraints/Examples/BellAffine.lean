import MeraConstraints.Examples.Bell
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# The PR box lies in the affine hull of the Bell polytope

The proof of Remark 3 (`prop:ineqstructure`) for type (ii) uses a signed
combination of the sixteen deterministic profiles. Profiles that meet three of
the four parity tests (see `Bell`) receive weight `3/16`, and profiles that meet
one receive weight `-1/16`. This chapter proves that these weights sum to one and
that the combination of the columns of `matrix` is the PR box at every row. So
the PR box lies in the affine hull of the district polytope, while `Bell` shows
that it lies outside the polytope. `prBox_affine_witness` states the three
facts: the PR box is a probability vector at each input, it is in the affine
hull, and it is not in the polytope.

This is the binary core of type (ii) of Remark 3. The general case, with paths in
a larger district, is in `CompactDistrict`.
-/

namespace MeraConstraints.Examples.Bell

/-- A binary response function corresponds to its pair of values at `false` and
`true`. This lists the sixteen profiles. -/
def responseEquiv : (Bool → Bool) ≃ Bool × Bool where
  toFun f := (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv f := by funext b; cases b <;> rfl
  right_inv p := by rcases p with ⟨a, b⟩; rfl

def profileEquiv : ((Bool × Bool) × (Bool × Bool)) ≃ Profile :=
  Equiv.prodCongr responseEquiv.symm responseEquiv.symm

theorem sum_profiles (F : Profile → ℝ) :
    (∑ r, F r) = ∑ p : ((Bool × Bool) × (Bool × Bool)), F (profileEquiv p) :=
  (profileEquiv.sum_comp F).symm

/-- Every profile meets either three or one of the four tests. -/
theorem score_three_or_one (r : Profile) : score r = 3 ∨ score r = 1 := by
  cases ha : r.1 false <;> cases hb : r.1 true <;>
    cases hc : r.2 false <;> cases hd : r.2 true <;>
    norm_num [score, win, ha, hb, hc, hd]

/-- The signed weights: `3/16` on profiles that meet three tests and `-1/16` on
the others. -/
noncomputable def affineWeight (r : Profile) : ℝ :=
  if score r = 3 then 3 / 16 else -(1 / 16)

theorem sum_affineWeight : (∑ r, affineWeight r) = 1 := by
  rw [sum_profiles]
  norm_num [affineWeight, profileEquiv, responseEquiv, score, win,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- The signed combination of the columns of `matrix` is the PR box. -/
theorem signed_mixture_eq_prBox (row : Row) :
    (∑ r, affineWeight r * matrix row r) = prBox row.1 row.2 := by
  rcases row with ⟨⟨x, y⟩, ⟨a, b⟩⟩
  cases x <;> cases y <;> cases a <;> cases b <;>
    rw [sum_profiles] <;>
    norm_num [affineWeight, profileEquiv, responseEquiv, score, win, matrix,
      prBox, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The PR box is in the affine span of the columns of `matrix`. The weights sum
to one but half of them are negative, so they do not place it in the convex hull. -/
theorem prBox_mem_affineSpan :
    (fun row : Row => prBox row.1 row.2) ∈
      affineSpan ℝ (Set.range fun r : Profile => fun row : Row => matrix row r) := by
  have hw : ∑ r ∈ (Finset.univ : Finset Profile), affineWeight r = 1 :=
    sum_affineWeight
  have hm := affineCombination_mem_affineSpan hw
    (fun r : Profile => fun row : Row => matrix row r)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hm
  convert hm using 1
  funext row
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (signed_mixture_eq_prBox row).symm

/-- The PR box is in the affine hull of the district polytope, which equals the
affine span of the columns. -/
theorem prBox_mem_affineSpan_mixture :
    (fun row : Row => prBox row.1 row.2) ∈ affineSpan ℝ (Polytope.mixture matrix) := by
  rw [Polytope.mixture_eq_convexHull, affineSpan_convexHull]
  exact prBox_mem_affineSpan

/-- The PR box is a probability vector at each input, lies in the affine hull of
the district polytope, and is not in the polytope. -/
theorem prBox_affine_witness :
    (∀ e, prBox e ∈ stdSimplex ℝ Output) ∧
    ((fun row : Row => prBox row.1 row.2) ∈ affineSpan ℝ (Polytope.mixture matrix)) ∧
    (fun row : Row => prBox row.1 row.2) ∉ Polytope.mixture matrix :=
  ⟨prBox_mem_stdSimplex, prBox_mem_affineSpan_mixture, prBox_not_mem_mixture⟩

end MeraConstraints.Examples.Bell
