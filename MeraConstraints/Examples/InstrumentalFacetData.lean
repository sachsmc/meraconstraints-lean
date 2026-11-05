import MeraConstraints.Examples.InstrumentalHull

/-!
# Integer data for the twelve facets of the instrumental variable polytope

For each row of the printed `H_i`, the script `scripts/generate-iv-facets.mjs`
produces the following tables, and Lean checks them on integer matrices:

- six columns of `printedB` that lie on the face defined by the row (the slack
  is zero), with an integer matrix `facetReader` that is a left inverse of the
  eight-by-six matrix of these columns, so the six columns are independent;
- a column off the face (positive slack), so the face is a proper subset of
  the polytope;
- for each other row, a column on this row's face and off the other row's face,
  so the two faces differ.

The casts from the integer matrices to the real matrices `printedB`, `printedHi`
are proved entry by entry. The dimension arguments that use these tables are in
`InstrumentalFacets`.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

def facetIntegerB : Matrix (Fin 8) (Fin 16) ℤ :=
  !![1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0;
     0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0;
     0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1;
     1,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0;
     0,1,0,0,0,1,0,1,0,1,0,0,0,0,0,0;
     0,0,0,0,0,0,1,0,1,0,1,0,0,0,1,0;
     0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,1]

def facetIntegerHi : Matrix (Fin 12) (Fin 8) ℤ :=
  !![0,0,0,0,-1,0,0,0;
     -1,-1,-1,0,0,1,0,0;
     0,1,0,0,-1,-1,-1,0;
     -1,0,0,0,0,0,0,0;
     0,0,1,0,1,0,0,0;
     1,0,0,0,0,0,1,0;
     0,0,0,0,0,-1,0,0;
     0,0,0,0,1,1,1,0;
     0,-1,0,0,0,0,0,0;
     1,1,1,0,0,0,0,0;
     0,0,0,0,0,0,-1,0;
     0,0,-1,0,0,0,0,0]

def facetIntegerUpper : Fin 12 → ℤ := ![0,0,0,0,1,1,0,1,0,1,0,0]

/-- For each row of `H_i`, six columns of `printedB` (zero-based indices) that
lie on the face defined by the row. -/
def facetColumn : Fin 12 → Fin 6 → Fin 16 :=
  ![![1,3,5,6,8,13],
    ![1,5,9,12,13,14],
    ![3,4,5,6,11,13],
    ![4,5,6,8,11,12],
    ![0,4,8,9,11,12],
    ![0,1,3,6,8,14],
    ![0,3,4,6,8,12],
    ![0,1,4,6,8,12],
    ![0,1,3,8,9,12],
    ![0,1,3,4,6,8],
    ![0,1,3,4,9,12],
    ![0,1,3,4,6,12]]

def facetReader : Fin 12 → Matrix (Fin 6) (Fin 8) ℤ :=
  ![!![0,-1,-1,0,0,1,1,0;
     1,1,1,0,0,-1,-1,0;
     0,1,1,0,0,0,-1,0;
     0,0,-1,0,0,0,1,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0],
    !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,1,-1,0,-1,0;
     0,0,0,0,0,0,1,0],
    !![1,0,0,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,1,0,0,-1,-1,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0],
    !![0,0,0,-1,1,0,0,0;
     0,0,0,0,0,1,0,0;
     0,1,0,1,-1,-1,0,0;
     0,-1,0,-1,1,1,1,0;
     0,1,1,1,-1,-1,-1,0;
     0,0,0,1,0,0,0,0],
    !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,1,0,0;
     0,0,1,0,0,-1,-1,0;
     0,0,0,1,0,0,0,0],
    !![0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0;
     1,0,0,0,-1,-1,0,0;
     0,1,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0],
    !![0,-1,-1,-1,1,0,1,0;
     1,1,1,1,-1,0,-1,0;
     0,1,1,0,0,0,-1,0;
     0,0,-1,0,0,0,1,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0],
    !![1,0,0,0,0,-1,0,0;
     0,0,0,0,0,1,0,0;
     -1,0,0,-1,1,1,0,0;
     1,1,0,1,-1,-1,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0],
    !![0,0,0,-1,1,0,0,0;
     0,0,-1,0,0,1,1,0;
     1,0,1,1,-1,-1,-1,0;
     0,0,0,0,0,0,1,0;
     0,0,1,0,0,0,-1,0;
     0,0,0,1,0,0,0,0],
    !![0,-1,-1,0,1,0,1,0;
     0,0,0,0,0,1,0,0;
     1,1,1,0,-1,-1,-1,0;
     0,1,1,0,0,0,-1,0;
     0,0,-1,0,0,0,1,0;
     0,0,1,0,0,0,0,0],
    !![0,-1,0,-1,1,0,0,0;
     0,0,-1,0,0,1,0,0;
     1,1,1,1,-1,-1,0,0;
     0,1,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0],
    !![0,-1,0,-1,1,0,1,0;
     0,0,0,0,0,1,0,0;
     1,1,0,1,-1,-1,-1,0;
     0,1,0,0,0,0,-1,0;
     0,0,0,0,0,0,1,0;
     0,0,0,1,0,0,0,0]]

def facetProperColumn : Fin 12 → Fin 16 := ![0,0,0,0,1,4,1,3,4,12,6,8]

def facetSeparatingColumn : Matrix (Fin 12) (Fin 12) (Fin 16) :=
  !![0,3,1,1,1,5,1,3,5,13,6,8;
     12,0,1,1,1,5,1,13,5,12,14,9;
     4,3,0,3,3,4,5,3,4,13,6,11;
     4,4,8,0,5,4,5,11,4,12,6,8;
     0,0,0,0,0,4,9,11,4,12,8,8;
     0,0,0,0,1,0,1,3,6,14,6,8;
     0,0,0,0,3,4,0,3,4,12,6,8;
     0,0,0,0,1,4,1,0,4,12,6,8;
     0,0,0,0,1,9,1,3,0,12,8,8;
     0,0,0,0,1,4,1,3,4,0,6,8;
     0,0,0,0,1,4,1,3,4,12,0,9;
     0,0,0,0,1,4,1,3,4,12,6,0]

def facetIntegerSlack (f : Fin 12) (j : Fin 16) : ℤ :=
  facetIntegerUpper f - ∑ i, facetIntegerHi f i * facetIntegerB i j

set_option maxHeartbeats 2000000 in
theorem facetIntegerB_cast (i : Fin 8) (j : Fin 16) :
    (facetIntegerB i j : ℝ) = printedB i j := by
  fin_cases i <;> fin_cases j <;> norm_num [facetIntegerB, printedB]

set_option maxHeartbeats 2000000 in
theorem facetIntegerHi_cast (f : Fin 12) (i : Fin 8) :
    (facetIntegerHi f i : ℝ) = printedHi f i := by
  fin_cases f <;> fin_cases i <;> norm_num [facetIntegerHi, printedHi]

theorem facetIntegerUpper_cast (f : Fin 12) : (facetIntegerUpper f : ℝ) = printedUpper f := by
  fin_cases f <;> norm_num [facetIntegerUpper, printedUpper]

theorem facetIntegerSlack_cast (f : Fin 12) (j : Fin 16) :
    (facetIntegerSlack f j : ℝ) = Geometry.slack (printedHi f) (printedUpper f) (fun i => printedB i j) := by
  unfold facetIntegerSlack Geometry.slack
  push_cast
  simp only [facetIntegerUpper_cast, facetIntegerHi_cast, facetIntegerB_cast]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem facet_reader_integer_identity : ∀ (f : Fin 12) (i j : Fin 6),
    (∑ k, facetReader f i k * facetIntegerB k (facetColumn f j)) = if i = j then 1 else 0 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem facet_selected_integer_tight : ∀ (f : Fin 12) (j : Fin 6),
    facetIntegerSlack f (facetColumn f j) = 0 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem facet_proper_integer_positive : ∀ f : Fin 12,
    0 < facetIntegerSlack f (facetProperColumn f) := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem facet_separation_integer : ∀ f g : Fin 12, f ≠ g →
    facetIntegerSlack f (facetSeparatingColumn f g) = 0 ∧
      0 < facetIntegerSlack g (facetSeparatingColumn f g) := by decide

noncomputable def facetColumnMatrix (f : Fin 12) : Matrix (Fin 8) (Fin 6) ℝ :=
  fun i j => printedB i (facetColumn f j)

noncomputable def facetReaderMatrix (f : Fin 12) : Matrix (Fin 6) (Fin 8) ℝ :=
  fun j i => (facetReader f j i : ℝ)

theorem facet_reader_mul_columns (f : Fin 12) :
    facetReaderMatrix f * facetColumnMatrix f = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.one_apply, facetReaderMatrix, facetColumnMatrix]
  simp_rw [← facetIntegerB_cast]
  exact_mod_cast facet_reader_integer_identity f i j

end MeraConstraints.Examples.Instrumental.Appendix
