import MeraConstraints.Examples.Bell
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# The exact PR-box affine witness

Step 3(ii) of the proof of Remark `prop:ineqstructure`,
`appendix.tex:338--342`, uses a normalized signed mixture of the sixteen
deterministic Bell profiles. Profiles winning three of the four parity
tests receive weight `3/16`; profiles winning one receive weight `-1/16`.

Here these are exact rational expressions in `ℝ`. We prove both required
identities: the weights sum to one, and their combination of compatibility
columns is the PR box at every input/output row. Thus the PR box lies in
the affine span of the Bell columns while the existing CHSH theorem proves
it lies outside their convex hull. Together with block normalization this
is the binary affine witness used by the manuscript, without yet lifting
the construction along paths inside a larger district.
-/

namespace MeraConstraints.Examples.Bell

/-- Enumerate a binary response function by its outputs at false and true.
This equivalence lets the proof expose all sixteen deterministic profiles
to the kernel instead of trusting an external enumeration. -/
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

/-- Every binary local profile wins either three or one of the four tests. -/
theorem score_three_or_one (r : Profile) : score r = 3 ∨ score r = 1 := by
  cases ha : r.1 false <;> cases hb : r.1 true <;>
    cases hc : r.2 false <;> cases hd : r.2 true <;>
    norm_num [score, win, ha, hb, hc, hd]

/-- The manuscript's signed affine weights; negativity is essential. -/
noncomputable def affineWeight (r : Profile) : ℝ :=
  if score r = 3 then 3 / 16 else -(1 / 16)

theorem sum_affineWeight : (∑ r, affineWeight r) = 1 := by
  rw [sum_profiles]
  norm_num [affineWeight, profileEquiv, responseEquiv, score, win,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- Direct verification of the signed mixture identity in the appendix. -/
theorem signed_mixture_eq_prBox (row : Row) :
    (∑ r, affineWeight r * matrix row r) = prBox row.1 row.2 := by
  rcases row with ⟨⟨x, y⟩, ⟨a, b⟩⟩
  cases x <;> cases y <;> cases a <;> cases b <;>
    rw [sum_profiles] <;>
    norm_num [affineWeight, profileEquiv, responseEquiv, score, win, matrix,
      prBox, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The exact weights certify affine-hull membership, although they do not
certify convex-hull membership because half of them are negative. -/
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

/-- Affine span of the columns equals the affine hull of their polytope. -/
theorem prBox_mem_affineSpan_mixture :
    (fun row : Row => prBox row.1 row.2) ∈ affineSpan ℝ (Polytope.mixture matrix) := by
  rw [Polytope.mixture_eq_convexHull, affineSpan_convexHull]
  exact prBox_mem_affineSpan

/-- The three properties required by the binary witness in Step 2/3(ii) of
the appendix: block probabilities, affine membership, and incompatibility. -/
theorem prBox_affine_witness :
    (∀ e, prBox e ∈ stdSimplex ℝ Output) ∧
    ((fun row : Row => prBox row.1 row.2) ∈ affineSpan ℝ (Polytope.mixture matrix)) ∧
    (fun row : Row => prBox row.1 row.2) ∉ Polytope.mixture matrix :=
  ⟨prBox_mem_stdSimplex, prBox_mem_affineSpan_mixture, prBox_not_mem_mixture⟩

end MeraConstraints.Examples.Bell
