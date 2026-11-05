import MeraConstraints.Examples.InstrumentalFacets
import MeraConstraints.FacetCriterion.RankCriterion

/-!
# Eight trivial and four nontrivial inequalities for the instrumental variable district

The instrumental variable details in the Supplementary Materials (`appendix:iv`)
state that rows 1, 4, 7, 8, 9, 10, 11 and 12 of `H_i` are nonnegativity
constraints and, by Proposition 4 (`prop:nontrivial`), the other four (rows 2, 3,
5 and 6) are nontrivial. This chapter proves that classification for the printed
H-representation. A row is trivial (`CoordinateTrivial`, Definition 4 for
inequalities) when it holds for every nonnegative vector satisfying the two
normalizations. Those vectors are the pair of probability simplices for `Z = 0`
and `Z = 1`.

The eight trivial rows: the slack of each is one probability coordinate plus a
combination of the two normalization residuals (`nonneg_slack_certificate`).
Only rows 8 and 10 need a residual; the other six are nonnegativity of a single
coordinate. The identity holds for every vector, not only on the affine hull.

The four nontrivial rows: for each probability coordinate there is a column on
the face of the row with value one in that coordinate
(`nontrivial_incident_cover`), so the columns on the face have no common zero
coordinate. The incidence criterion
`coordinate_trivial_iff_incident_zero_of_ranks` says that a row is trivial
exactly when its face columns have a common zero coordinate. It needs the affine
hull and the facets of the previous chapters. Together they give
`printed_facet_trivial_iff`.

Row numbers in the Lean statements are zero-based.
-/

namespace MeraConstraints.Examples.Instrumental.Appendix

open EqualityConstraints Geometry MeraConstraints.FacetCriterion

/-- Rows 2, 3, 5 and 6 of the manuscript, with zero-based indices. -/
def nontrivialRows : Finset (Fin 12) := {1,2,4,5}

def nonnegativeRows : Finset (Fin 12) := Finset.univ \ nontrivialRows

theorem card_nontrivialRows : nontrivialRows.card = 4 := by decide
theorem card_nonnegativeRows : nonnegativeRows.card = 8 := by decide

/-- The probability coordinate whose nonnegativity each trivial H row states. -/
def nonnegCoordinate : Fin 12 → Option (Fin 8) :=
  ![some 4, none, none, some 0, none, none, some 5, some 7, some 1, some 3, some 6, some 2]

theorem nonnegCoordinate_iff : ∀ f : Fin 12,
    (∃ k, nonnegCoordinate f = some k) ↔ f ∉ nontrivialRows := by decide

def nonnegEqualityWeight : Fin 12 → Fin 2 → ℝ :=
  ![![0,0], ![0,0], ![0,0], ![0,0], ![0,0], ![0,0],
    ![0,0], ![0,1], ![0,0], ![1,0], ![0,0], ![0,0]]

set_option maxHeartbeats 2000000 in
/-- The slack of each trivial row is the coordinate `p k` plus a combination of
the normalization residuals, for every vector `p`. -/
theorem nonneg_slack_certificate (f : Fin 12) (k : Fin 8) (hk : nonnegCoordinate f = some k)
    (p : Fin 8 → ℝ) :
    slack (printedHi f) (printedUpper f) p = p k +
      ∑ e, nonnegEqualityWeight f e * (score (printedHe e) p - printedTarget e) := by
  fin_cases f <;> norm_num [nonnegCoordinate] at hk <;> first | subst k | cases hk
  all_goals
    rw [probability_coordinates p]
    simp only [slack, score, Fin.sum_univ_succ, Fin.sum_univ_zero]
    dsimp [printedHi, printedUpper, printedHe, printedTarget, nonnegEqualityWeight,
      Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    ring

theorem nonneg_slack_eq_coordinate (f : Fin 12) (k : Fin 8) (hk : nonnegCoordinate f = some k)
    {p : Fin 8 → ℝ} (hp : Feasible printedHe printedTarget p) :
    slack (printedHi f) (printedUpper f) p = p k := by
  have h := nonneg_slack_certificate f k hk p
  have he : ∀ e, score (printedHe e) p = printedTarget e := hp
  simpa only [he, sub_self, mul_zero, Finset.sum_const_zero, add_zero] using h

/-- For each nontrivial row and each of the eight probability coordinates, a
column on the face with value one in that coordinate. The entries for the
trivial rows are unused. -/
def nontrivialCoverColumn : Fin 12 → Fin 8 → Fin 16 :=
  ![![0,0,0,0,0,0,0,0],
    ![1,5,9,12,12,1,14,13],
    ![3,4,11,13,4,5,6,3],
    ![0,0,0,0,0,0,0,0],
    ![0,4,8,12,0,9,8,11],
    ![0,6,8,14,0,1,6,3],
    ![0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem nontrivial_cover_integer : ∀ f : Fin 12, f ∈ nontrivialRows → ∀ k : Fin 8,
    facetIntegerSlack f (nontrivialCoverColumn f k) = 0 ∧
      facetIntegerB k (nontrivialCoverColumn f k) = 1 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem printedB_integer_nonnegative : ∀ (i : Fin 8) (j : Fin 16), 0 ≤ facetIntegerB i j := by decide

theorem printedB_nonnegative (i : Fin 8) (j : Fin 16) : 0 ≤ printedB i j := by
  rw [← facetIntegerB_cast]
  exact_mod_cast printedB_integer_nonnegative i j

theorem nontrivial_incident_cover (f : Fin 12) (hf : f ∈ nontrivialRows) (k : Fin 8) :
    ∃ j : Fin 16, slack (printedHi f) (printedUpper f) (fun i => printedB i j) = 0 ∧ printedB k j = 1 := by
  obtain ⟨htight, hone⟩ := nontrivial_cover_integer f hf k
  refine ⟨nontrivialCoverColumn f k, ?_, ?_⟩
  · rw [← facetIntegerSlack_cast]
    exact_mod_cast htight
  · rw [← facetIntegerB_cast, hone]
    norm_num

theorem printedB_coordinate_cover (k : Fin 8) : ∃ j : Fin 16, 0 < printedB k j := by
  obtain ⟨j, _, hj⟩ := nontrivial_incident_cover 1 (by decide) k
  exact ⟨j, by rw [hj]; norm_num⟩

/-- A row is trivial exactly when the columns on its face have a common zero
coordinate. This is the incidence criterion of Proposition 4 (`prop:nontrivial`)
for the printed H-representation. -/
theorem printed_coordinate_trivial_iff_incident_zero (f : Fin 12) :
    CoordinateTrivial printedHe printedTarget (printedHi f) (printedUpper f) ↔
      ∃ k, ∀ j, slack (printedHi f) (printedUpper f) (fun i => printedB i j) = 0 → printedB k j = 0 :=
  coordinate_trivial_iff_incident_zero_of_ranks printedB printedHe printedTarget printedHi printedUpper f
    printed_columnHull_iff printedB_nonnegative printedB_coordinate_cover printed_facet_valid
    (fun g => ⟨facetProperColumn g, printed_facet_proper g⟩)
    printed_facet_incident_nonempty printed_facets_codimension_one
    (fun g hg => printed_facets_distinct f g (Ne.symm hg))

theorem printed_facet_trivial_iff (f : Fin 12) :
    CoordinateTrivial printedHe printedTarget (printedHi f) (printedUpper f) ↔ f ∉ nontrivialRows := by
  rw [printed_coordinate_trivial_iff_incident_zero]
  constructor
  · rintro ⟨k, hzero⟩ hf
    obtain ⟨j, htight, hone⟩ := nontrivial_incident_cover f hf k
    have h := hzero j htight
    rw [hone] at h
    norm_num at h
  · intro hf
    obtain ⟨k, hk⟩ := (nonnegCoordinate_iff f).mpr hf
    refine ⟨k, fun j hj => ?_⟩
    have hp : Feasible printedHe printedTarget (fun i => printedB i j) :=
      (printed_columnHull_iff _).mp (mem_affineSpan ℝ ⟨j, rfl⟩)
    exact (nonneg_slack_eq_coordinate f k hk hp).symm.trans hj

/-- A row is nontrivial exactly when it is one of the four rows of
`nontrivialRows`, the instrumental inequalities. -/
theorem printed_facet_nontrivial_iff (f : Fin 12) :
    ¬ CoordinateTrivial printedHe printedTarget (printedHi f) (printedUpper f) ↔ f ∈ nontrivialRows := by
  simpa only [not_not] using not_congr (printed_facet_trivial_iff f)

theorem printed_facet_trivial_iff_mem_nonnegativeRows (f : Fin 12) :
    CoordinateTrivial printedHe printedTarget (printedHi f) (printedUpper f) ↔ f ∈ nonnegativeRows := by
  rw [printed_facet_trivial_iff]
  simp only [nonnegativeRows, Finset.mem_sdiff, Finset.mem_univ, true_and]

end MeraConstraints.Examples.Instrumental.Appendix
