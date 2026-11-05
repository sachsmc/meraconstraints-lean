import MeraConstraints.CompactDistrict.OrderingConstraints
import MeraConstraints.FacetCriterion.RankCriterion

/-!
# Trivial inequality constraints

`InequalityTrivial` is Definition 4 (trivial constraints) for inequalities: an
inequality `hᵀp ≤ c` holds for every `p` in the cross-product of probability
simplices `P̌` (`InSimplexProduct`) that satisfies the equality constraints. This
chapter proves the first two claims of Proposition 4 (`prop:nontrivial`) (ii): the
inequality is trivial if and only if some entry `p_k` is zero at every column of the
matrix `B` on its facet (`inequalityTrivial_iff_incident_zero`), and in that case
`c - hᵀp = α p_k + λᵀ(H_e p - b_e)` with `α > 0`
(`coordinate_certificate_of_incident_zero`). Both concern only the matrix `B`, so
they have no c-degree hypothesis, but they should be read in the proposition's setting
of c-degree 1.

On the affine hull of the district polytope, (N) holds, so `P̌` there is the set of
nonnegative vectors (`inSimplexProduct_iff_nonneg_on_hull`). This reduces the claims
to the general facet theorems. They also need every entry of `B` to be 0 or 1 and
every row to have entry `1` at some column (`compatibility_row_covered`): take
each member's response function to be constant at its value in that row.
-/

namespace MeraConstraints.CompactDistrict

open EqualityConstraints Geometry

variable {n ℓ : ℕ} (G : HiddenGraph.Graph n ℓ) (val : Fin n → Type*)
  [DecidableEq (HiddenGraph.DistrictId G)] (d : HiddenGraph.DistrictId G)

local notation "Out" => MemberAssign val (HiddenGraph.observedDistrict G) d
local notation "Ext" => ExternalAssign G.observed val (HiddenGraph.observedDistrict G) d
local notation "Rows" => Row G.observed val (HiddenGraph.observedDistrict G) d
local notation "Profiles" => GlobalModel.Profile G.observed val (HiddenGraph.observedDistrict G) d
local notation "C" => matrix G.observed val (HiddenGraph.observedDistrict G) d

/-- The profile in which each member's response function is constant at its value
in `out`. -/
def constantOutputProfile (out : Out) : Profiles := fun i _ => out i

theorem compatibility_constant_output (x : Rows) :
    C x (constantOutputProfile G val d x.1) = 1 := by
  classical
  have hx : Compatible G.observed val (HiddenGraph.observedDistrict G) d x
      (constantOutputProfile G val d x.1) := fun _ => rfl
  simp only [matrix, if_pos hx]

theorem compatibility_binary (x : Rows) (r : Profiles) : C x r = 0 ∨ C x r = 1 := by
  classical
  unfold matrix
  split <;> simp

theorem compatibility_nonneg (x : Rows) (r : Profiles) : 0 ≤ C x r := by
  rcases compatibility_binary G val d x r with h | h <;> simp [h]

theorem compatibility_row_covered (x : Rows) : ∃ r : Profiles, 0 < C x r := by
  refine ⟨constantOutputProfile G val d x.1, ?_⟩
  rw [compatibility_constant_output]
  exact zero_lt_one

variable [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- Equations (N) hold on the affine hull of the district polytope. -/
theorem normalization_on_columnHull (p : Rows → ℝ)
    (hp : p ∈ MeraConstraints.FacetCriterion.columnHull C) (e : Ext) :
    (∑ out, p (out, e)) = 1 := by
  rw [← OrderingConstraints.normalization_score G val d p e]
  apply MeraConstraints.FacetCriterion.equation_on_affineSpan
    (Set.range fun r : Profiles => fun x : Rows => C x r)
    (OrderingConstraints.normalizationMatrix G val d e) 1
  · rintro _ ⟨r, rfl⟩
    exact OrderingConstraints.normalization_column G val d r e
  · exact hp

/-- The cross-product of probability simplices `P̌`: for each value of `v₂`, the
entries `p(· ∣ v₂)` are nonnegative and sum to one. -/
def InSimplexProduct (p : Rows → ℝ) : Prop :=
  ∀ e : Ext, (fun out : Out => p (out, e)) ∈ stdSimplex ℝ Out

/-- On the affine hull, a vector lies in `P̌` if and only if all its entries are
nonnegative. -/
theorem inSimplexProduct_iff_nonneg_on_hull (p : Rows → ℝ)
    (hp : p ∈ MeraConstraints.FacetCriterion.columnHull C) :
    InSimplexProduct G val d p ↔ ∀ x, 0 ≤ p x := by
  constructor
  · intro h x
    exact (h x.2).1 x.1
  · intro hn e
    exact ⟨fun out => hn (out, e), normalization_on_columnHull G val d p hp e⟩

/-- Definition 4 for inequalities: `hᵀp ≤ c` holds for every `p` in `P̌` that
satisfies the equations `A p = b`. -/
def InequalityTrivial {E : Type*} (A : Matrix E Rows ℝ) (b : E → ℝ)
    (h : Rows → ℝ) (c : ℝ) : Prop :=
  ∀ p, InSimplexProduct G val d p → Feasible A b p → 0 ≤ slack h c p

theorem coordinateTrivial_iff_inequalityTrivial {E : Type*}
    (A : Matrix E Rows ℝ) (b : E → ℝ) (h : Rows → ℝ) (c : ℝ)
    (hhull : ∀ p, p ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b p) :
    MeraConstraints.FacetCriterion.CoordinateTrivial A b h c ↔ InequalityTrivial G val d A b h c := by
  constructor
  · intro hc p hk hp
    exact hc p ((inSimplexProduct_iff_nonneg_on_hull G val d p ((hhull p).mpr hp)).mp hk) hp
  · intro hk p hn hp
    exact hk p ((inSimplexProduct_iff_nonneg_on_hull G val d p ((hhull p).mpr hp)).mpr hn) hp

variable [∀ i, Nonempty (val i)]

/-- Proposition 4 (`prop:nontrivial`) (ii), first claim: the inequality `hᵀp ≤ c`
of row `f` is trivial if and only if some entry `p_k` is zero at every column of `B`
with `hᵀβ = c`. The hypotheses say that the rows of `A p = b` define the affine
hull, and that each inequality is valid on the polytope and defines a different
facet. -/
theorem inequalityTrivial_iff_incident_zero {E I : Type*} [Fintype E] [Fintype I]
    (A : Matrix E Rows ℝ) (b : E → ℝ) (h : I → Rows → ℝ) (c : I → ℝ) (f : I)
    (hhull : ∀ p, p ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b p)
    (hvalid : ∀ g r, 0 ≤ slack (h g) (c g) (fun x => C x r))
    (hproper : ∀ g, ∃ r, 0 < slack (h g) (c g) (fun x => C x r))
    (hincident : ∀ g, (MeraConstraints.FacetCriterion.incidentColumns C (h g) (c g)).Nonempty)
    (hdim : ∀ g, Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull C).direction =
      Module.finrank ℝ (MeraConstraints.FacetCriterion.incidentHull C (h g) (c g)).direction + 1)
    (hdistinct : ∀ g, g ≠ f →
      MeraConstraints.FacetCriterion.incidentHull C (h f) (c f) ≠
        MeraConstraints.FacetCriterion.incidentHull C (h g) (c g)) :
    InequalityTrivial G val d A b (h f) (c f) ↔
      ∃ x : Rows, ∀ r : Profiles, slack (h f) (c f) (fun y => C y r) = 0 → C x r = 0 := by
  rw [← coordinateTrivial_iff_inequalityTrivial G val d A b (h f) (c f) hhull]
  exact MeraConstraints.FacetCriterion.coordinate_trivial_iff_incident_zero_of_ranks
    C A b h c f hhull (compatibility_nonneg G val d) (compatibility_row_covered G val d)
    hvalid hproper hincident hdim hdistinct

/-- Proposition 4 (`prop:nontrivial`) (ii), second claim: if `p_x` is zero at every
column of `B` on the facet, then `c - hᵀp = α p_x + λᵀ(A p - b)` with `α > 0`, for
every real vector `p`. The inequality is then `p_x ≥ 0` written differently. -/
theorem coordinate_certificate_of_incident_zero {E : Type*} [Fintype E]
    (A : Matrix E Rows ℝ) (b : E → ℝ) (h : Rows → ℝ) (c : ℝ)
    (hhull : ∀ p, p ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b p)
    (hvalid : ∀ r, 0 ≤ slack h c (fun x => C x r))
    (hproper : ∃ r, 0 < slack h c (fun x => C x r))
    (hincident : (MeraConstraints.FacetCriterion.incidentColumns C h c).Nonempty)
    (hdim : Module.finrank ℝ (MeraConstraints.FacetCriterion.columnHull C).direction =
      Module.finrank ℝ (MeraConstraints.FacetCriterion.incidentHull C h c).direction + 1)
    (x : Rows) (hzero : ∀ r, slack h c (fun y => C y r) = 0 → C x r = 0) :
    ∃ α : ℝ, 0 < α ∧ ∃ weights : E → ℝ, ∀ p,
      slack h c p = α * p x + ∑ e, weights e * (score (A e) p - b e) := by
  have hspan := MeraConstraints.FacetCriterion.facetSpan_of_codimension_one C A b h c
    hhull hincident hproper hdim
  have he : ∀ r, Feasible A b (fun x => C x r) := fun r =>
    (hhull _).mp (mem_affineSpan ℝ ⟨r, rfl⟩)
  have htight : (MeraConstraints.FacetCriterion.incidentIndices C h c).Nonempty := by
    obtain ⟨_, r, hr, rfl⟩ := hincident
    exact ⟨r, (MeraConstraints.FacetCriterion.mem_incidentIndices _ _ _ _).mpr hr⟩
  exact MeraConstraints.FacetCriterion.coordinate_certificate_of_columns C A b h c
    hspan (compatibility_nonneg G val d) (compatibility_row_covered G val d) he
    hvalid hproper htight x hzero

end MeraConstraints.CompactDistrict
