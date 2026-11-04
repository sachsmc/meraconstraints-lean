import MeraConstraints.CompactDistrict.OrderingConstraints
import MeraConstraints.FacetCriterion.RankCriterion

/-!
# The facet incidence criterion for the actual district matrix

The generic facet theorem works in an affine hull intersected with the
nonnegative orthant. The manuscript defines inequality triviality on the
cross-product of probability simplices intersected with that hull. Here we
prove these domains coincide for the actual compact compatibility matrix:
normalization holds on its whole affine hull, since it holds at every column.

The matrix is binary and nonnegative. Every row equals one at some column:
choose each member's mechanism to be the constant specified by that row.
Thus the generic coordinate-coverage hypothesis is proved from the actual
response-function definition rather than supplied as an assumption.

The final theorem gives the manuscript's inequality-triviality incidence
criterion from actual affine-hull equations and distinct proper codimension-one
facet data. It also exposes the positive coordinate-plus-equality certificate.
`CompactDistrict.FacetWitness` constructs an observed distribution that
violates only a selected nontrivial inequality, while satisfying all global
graphical independencies and all other district constraints. It uses the
separate positive-kernel reconstruction and actual polytope reference points.
No unrestricted-profile sufficiency at higher c-degree is asserted here.
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

/-- Constant member mechanisms realize the district-output assignment at
every external input, hence cover every compact row. -/
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

/-- The actual affine hull includes all external-block normalizations. -/
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

/-- The paper's cross-product of probability simplices, one per external input. -/
def KernelSimplex (p : Rows → ℝ) : Prop :=
  ∀ e : Ext, (fun out : Out => p (out, e)) ∈ stdSimplex ℝ Out

/-- Inside the affine hull, normalization is automatic. Therefore simplex
membership adds exactly coordinate nonnegativity. -/
theorem kernelSimplex_iff_nonneg_on_hull (p : Rows → ℝ)
    (hp : p ∈ MeraConstraints.FacetCriterion.columnHull C) :
    KernelSimplex G val d p ↔ ∀ x, 0 ≤ p x := by
  constructor
  · intro h x
    exact (h x.2).1 x.1
  · intro hn e
    exact ⟨fun out => hn (out, e), normalization_on_columnHull G val d p hp e⟩

/-- Inequality triviality as actually defined in `def:nontrivial`: validity
on the cross-product of simplices satisfying the equality constraints. -/
def KernelTrivial {E : Type*} (A : Matrix E Rows ℝ) (b : E → ℝ)
    (h : Rows → ℝ) (c : ℝ) : Prop :=
  ∀ p, KernelSimplex G val d p → Feasible A b p → 0 ≤ slack h c p

theorem coordinateTrivial_iff_kernelTrivial {E : Type*}
    (A : Matrix E Rows ℝ) (b : E → ℝ) (h : Rows → ℝ) (c : ℝ)
    (hhull : ∀ p, p ∈ MeraConstraints.FacetCriterion.columnHull C ↔ Feasible A b p) :
    MeraConstraints.FacetCriterion.CoordinateTrivial A b h c ↔ KernelTrivial G val d A b h c := by
  constructor
  · intro hc p hk hp
    exact hc p ((kernelSimplex_iff_nonneg_on_hull G val d p ((hhull p).mpr hp)).mp hk) hp
  · intro hk p hn hp
    exact hk p ((kernelSimplex_iff_nonneg_on_hull G val d p ((hhull p).mpr hp)).mpr hn) hp

variable [∀ i, Nonempty (val i)]

/-- The incidence criterion of Proposition `prop:nontrivial` (ii), now on
the actual compact district matrix and the paper's probability-kernel domain.
Facet-span and distinct-plane separation follow from the supplied genuine
codimension-one incidence data; neither is a certificate hypothesis. -/
theorem kernel_trivial_iff_incident_zero {E I : Type*} [Fintype E] [Fintype I]
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
    KernelTrivial G val d A b (h f) (c f) ↔
      ∃ x : Rows, ∀ r : Profiles, slack (h f) (c f) (fun y => C y r) = 0 → C x r = 0 := by
  rw [← coordinateTrivial_iff_kernelTrivial G val d A b (h f) (c f) hhull]
  exact MeraConstraints.FacetCriterion.coordinate_trivial_iff_incident_zero_of_ranks
    C A b h c f hhull (compatibility_nonneg G val d) (compatibility_row_covered G val d)
    hvalid hproper hincident hdim hdistinct

/-- The coordinate-plus-equality formula in the trivial case, valid at every
real vector, including vectors outside the simplex or affine hull. -/
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
