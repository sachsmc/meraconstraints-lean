import MeraConstraints.EqualityConstraints
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# Facets whose inequality is a coordinate constraint

General facts for Step 4 of the proof of Proposition 4 (`prop:nontrivial`), the
proof of part (ii). The rows of `H_e` define the affine hull of the district
polytope, and an inequality `hᵀp ≤ c` of `H_i` defines a facet `F`. Write
`FacetSpan` for the property that the affine span of the columns of `B` on `F` is
the set of solutions of `H_e p = b_e` with `hᵀp = c`. `FacetCriterion/Span.lean`
derives it from the dimensions of the affine spans.

If `p_k = 0` at every column of `B` on `F`, then
`c - hᵀp = α p_k + λᵀ(H_e p - b_e)` for some `α > 0` and every `p`. This uses the
fact that an equation holding on the affine span is a linear combination of the
equations (`EqualityConstraints`). Conversely, if no such `k` exists, the average
of the columns on `F` is strictly positive. Moving from the average of all columns
through it, slightly past it (`Geometry`), gives a strictly positive vector in the
affine hull that violates the inequality. So the inequality holds at every
nonnegative solution of `H_e p = b_e` exactly when such a `k` exists
(`coordinate_trivial_iff_incident_zero`). Producing a distribution with the
conditional independencies from this vector is not done here.
-/

namespace MeraConstraints.FacetCriterion

open EqualityConstraints Geometry

variable {Row Col E : Type*} [Fintype Row] [Fintype Col] [Fintype E]

/-- The columns of `B` on the hyperplane `hᵀp = c`. -/
def incidentColumns (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) : Set (Row → ℝ) :=
  {p | ∃ j, slack h c (fun i => B i j) = 0 ∧ (fun i => B i j) = p}

/-- The affine span of the columns of `B` on the hyperplane `hᵀp = c` is the set of
solutions of `A p = b` with `hᵀp = c`. -/
def FacetSpan (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : Row → ℝ) (c : ℝ) : Prop :=
  ∀ p, p ∈ affineSpan ℝ (incidentColumns B h c) ↔ Feasible A b p ∧ slack h c p = 0

private theorem score_affine_step (g : Row → ℝ) (t : ℝ) (x y z : Row → ℝ) :
    score g (t • (x -ᵥ y) +ᵥ z) = t * (score g x - score g y) + score g z := by
  simp only [score, vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  calc
    _ = ∑ i, (t * (g i * x i - g i * y i) + g i * z i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- An equation `gᵀp = d` that holds on a set `s` holds on its affine span. -/
theorem equation_on_affineSpan (s : Set (Row → ℝ)) (g : Row → ℝ) (d : ℝ)
    (hs : ∀ x ∈ s, score g x = d) {p : Row → ℝ} (hp : p ∈ affineSpan ℝ s) :
    score g p = d := by
  refine affineSpan_induction (p := fun p => score g p = d) hp hs ?_
  intro t x y z hx hy hz
  rw [score_affine_step, hx, hy, hz]
  ring

private noncomputable def coordinate (k : Row) : Row → ℝ := by
  classical
  exact fun i => if i = k then 1 else 0

@[simp] private theorem score_coordinate (k : Row) (p : Row → ℝ) :
    score (coordinate k) p = p k := by
  classical
  simp [coordinate, score, ite_mul]

omit [Fintype Col] [Fintype E] in
/-- The average of columns that solve `A p = b` also solves it. -/
theorem average_feasible (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (s : Finset Col) (hs : s.Nonempty) (he : ∀ j ∈ s, Feasible A b (fun i => B i j)) :
    Feasible A b (average s B) := by
  intro e
  have h := slack_average_eq_zero s hs B (A e) (b e) (fun j hj => by
    change b e - score (A e) (fun i => B i j) = 0
    rw [he j hj e]
    exact sub_self _)
  change b e - score (A e) (average s B) = 0 at h
  linarith

omit [Fintype Col] in
/-- If `p_k = 0` at every column on the facet, then `p_k` is proportional to the
slack of the facet inequality at every solution of `A p = b`. -/
theorem coordinate_proportional_on_hull
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : Row → ℝ) (c : ℝ) (hspan : FacetSpan B A b h c)
    (x : Row → ℝ) (hx : Feasible A b x) (hxtight : slack h c x = 0)
    (k : Row) (hzero : ∀ j, slack h c (fun i => B i j) = 0 → B k j = 0) :
    ∃ t : ℝ, ∀ p, Feasible A b p → p k = t * slack h c p := by
  classical
  let A' : Matrix (Option E) Row ℝ := fun e => match e with
    | none => h
    | some e => A e
  let b' : Option E → ℝ := fun e => match e with
    | none => c
    | some e => b e
  have hx' : Feasible A' b' x := by
    intro e
    cases e with
    | none => change score h x = c; change c - score h x = 0 at hxtight; linarith
    | some e => exact hx e
  have hc' : Consequence A' b' (coordinate k) 0 := by
    intro p hp
    apply equation_on_affineSpan (incidentColumns B h c) (coordinate k) 0
    · rintro _ ⟨j, hj, rfl⟩
      simpa only [score_coordinate] using hzero j hj
    · apply (hspan p).mpr
      refine ⟨fun e => hp (some e), ?_⟩
      have hnone := hp none
      change score h p = c at hnone
      change c - score h p = 0
      linarith
  obtain ⟨weights, hw, hb⟩ := (consequence_iff_rowCombination A' b' (coordinate k) 0 x hx').mp hc'
  refine ⟨-weights none, ?_⟩
  intro p hp
  have hs : score (coordinate k) p = ∑ e, weights e * score (A' e) p := by
    rw [show coordinate k = (fun j => ∑ e, weights e * A' e j) from funext hw]
    exact score_rowCombination A' weights p
  simp only [score_coordinate, Fintype.sum_option] at hs
  simp only [Fintype.sum_option] at hb
  change p k = weights none * score h p + ∑ e, weights (some e) * score (A e) p at hs
  change 0 = weights none * c + ∑ e, weights (some e) * b e at hb
  have hpsum : (∑ e, weights (some e) * score (A e) p) = ∑ e, weights (some e) * b e :=
    Finset.sum_congr rfl fun e _ => by rw [hp e]
  rw [hpsum] at hs
  change p k = -weights none * (c - score h p)
  nlinarith

omit [Fintype Col] in
/-- If `p_k = 0` at every column on the facet, then
`c - hᵀp = α p_k + λᵀ(A p - b)` for some `α > 0` and every vector `p`. This is the
second claim of Proposition 4 (`prop:nontrivial`) (ii). -/
theorem coordinate_certificate
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : Row → ℝ) (c : ℝ) (hspan : FacetSpan B A b h c)
    (x β : Row → ℝ) (hx : Feasible A b x) (hxtight : slack h c x = 0)
    (hβ : Feasible A b β) (hβslack : 0 < slack h c β)
    (k : Row) (hβk : 0 < β k)
    (hzero : ∀ j, slack h c (fun i => B i j) = 0 → B k j = 0) :
    ∃ α : ℝ, 0 < α ∧ ∃ weights : E → ℝ, ∀ p,
      slack h c p = α * p k + ∑ e, weights e * (score (A e) p - b e) := by
  classical
  obtain ⟨t, ht⟩ := coordinate_proportional_on_hull B A b h c hspan x hx hxtight k hzero
  have htpos : 0 < t := (mul_pos_iff_of_pos_right hβslack).mp (by rw [← ht β hβ]; exact hβk)
  let α : ℝ := t⁻¹
  have hα : 0 < α := inv_pos.mpr htpos
  have hαt : α * t = 1 := inv_mul_cancel₀ htpos.ne'
  have hslack : ∀ p, Feasible A b p → slack h c p = α * p k := by
    intro p hp
    rw [ht p hp, ← mul_assoc, hαt, one_mul]
  let g : Row → ℝ := fun i => h i + α * coordinate k i
  have hg (p : Row → ℝ) : score g p = score h p + α * p k := by
    simp only [g, score, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show (∑ j, coordinate k j * p j) = p k from score_coordinate k p]
  have hcons : Consequence A b g c := by
    intro p hp
    have hp' := hslack p hp
    rw [hg]
    change c - score h p = α * p k at hp'
    linarith
  obtain ⟨weights, hw, hb⟩ := (consequence_iff_rowCombination A b g c β hβ).mp hcons
  refine ⟨α, hα, fun e => -weights e, ?_⟩
  intro p
  have hwscore : score g p = ∑ e, weights e * score (A e) p := by
    rw [show g = (fun j => ∑ e, weights e * A e j) from funext hw]
    exact score_rowCombination A weights p
  have hres : (∑ e, -weights e * (score (A e) p - b e)) = c - score g p := by
    rw [hb, hwscore, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hres, hg]
  change c - score h p = _
  ring

/-- The indices of the columns of `B` on the hyperplane `hᵀp = c`. -/
noncomputable def incidentIndices (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) : Finset Col := by
  classical
  exact Finset.univ.filter fun j => slack h c (fun i => B i j) = 0

@[simp] theorem mem_incidentIndices (B : Matrix Row Col ℝ) (h : Row → ℝ) (c : ℝ) (j : Col) :
    j ∈ incidentIndices B h c ↔ slack h c (fun i => B i j) = 0 := by
  classical
  simp [incidentIndices]

omit [Fintype E] in
/-- If some solution of `A p = b` on the first plane is off the second plane, then
some column on the first plane is strict for the second inequality, which holds at
every column. -/
theorem incident_strict_of_plane_separation
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h g : Row → ℝ) (c d : ℝ) (hspan : FacetSpan B A b h c)
    (hg : ∀ j, 0 ≤ slack g d (fun i => B i j))
    (hsep : ∃ p, Feasible A b p ∧ slack h c p = 0 ∧ slack g d p ≠ 0) :
    ∃ j, slack h c (fun i => B i j) = 0 ∧ 0 < slack g d (fun i => B i j) := by
  by_contra hn
  push Not at hn
  obtain ⟨p, hp, hptight, hpother⟩ := hsep
  have hs : score g p = d := by
    apply equation_on_affineSpan (incidentColumns B h c) g d
    · rintro _ ⟨j, hj, rfl⟩
      have hz : slack g d (fun i => B i j) = 0 := le_antisymm (hn j hj) (hg j)
      change d - score g (fun i => B i j) = 0 at hz
      linarith
    · exact (hspan p).mpr ⟨hp, hptight⟩
  apply hpother
  change d - score g p = 0
  rw [hs, sub_self]

variable [Nonempty Col]

/-- The certificate `c - hᵀp = α p_k + λᵀ(A p - b)` from the columns of `B`: the
columns are nonnegative, every entry is positive at some column, the columns solve
`A p = b`, and the inequality holds at every column and is strict at some column. -/
theorem coordinate_certificate_of_columns
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : Row → ℝ) (c : ℝ) (hspan : FacetSpan B A b h c)
    (hnonneg : ∀ i j, 0 ≤ B i j) (hcover : ∀ i, ∃ j, 0 < B i j)
    (he : ∀ j, Feasible A b (fun i => B i j))
    (hvalid : ∀ j, 0 ≤ slack h c (fun i => B i j))
    (hproper : ∃ j, 0 < slack h c (fun i => B i j))
    (htight : (incidentIndices B h c).Nonempty)
    (k : Row) (hzero : ∀ j, slack h c (fun i => B i j) = 0 → B k j = 0) :
    ∃ α : ℝ, 0 < α ∧ ∃ weights : E → ℝ, ∀ p,
      slack h c p = α * p k + ∑ e, weights e * (score (A e) p - b e) := by
  classical
  let s := incidentIndices B h c
  let x := average s B
  let β := average Finset.univ B
  have hu : (Finset.univ : Finset Col).Nonempty := Finset.univ_nonempty
  have hx : Feasible A b x := average_feasible B A b s htight (fun j _ => he j)
  have hxtight : slack h c x = 0 := slack_average_eq_zero s htight B h c
    (fun j hj => (mem_incidentIndices B h c j).mp hj)
  have hβ : Feasible A b β := average_feasible B A b Finset.univ hu (fun j _ => he j)
  have hβslack : 0 < slack h c β := (slack_average_pos_iff Finset.univ hu B h c
    (fun j _ => hvalid j)).mpr (by obtain ⟨j, hj⟩ := hproper; exact ⟨j, Finset.mem_univ _, hj⟩)
  have hβk : 0 < β k := (average_pos_iff Finset.univ hu B k (fun j _ => hnonneg k j)).mpr
    (by obtain ⟨j, hj⟩ := hcover k; exact ⟨j, Finset.mem_univ _, hj⟩)
  exact coordinate_certificate B A b h c hspan x β hx hxtight hβ hβslack k hβk hzero

omit [Fintype E] in
/-- If no entry is zero at every column on the facet of `f`, there is a strictly
positive solution of `A p = b` that satisfies every other inequality strictly and
violates the inequality of `f`. This is the vector `q` of Step 4. -/
theorem positive_violator_of_no_incident_zero {I : Type*} [Fintype I]
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : I → Row → ℝ) (c : I → ℝ) (f : I)
    (hspan : FacetSpan B A b (h f) (c f))
    (hnonneg : ∀ i j, 0 ≤ B i j) (he : ∀ j, Feasible A b (fun i => B i j))
    (hvalid : ∀ g j, 0 ≤ slack (h g) (c g) (fun i => B i j))
    (hproper : ∃ j, 0 < slack (h f) (c f) (fun i => B i j))
    (htight : (incidentIndices B (h f) (c f)).Nonempty)
    (hsep : ∀ g, g ≠ f → ∃ p, Feasible A b p ∧
      slack (h f) (c f) p = 0 ∧ slack (h g) (c g) p ≠ 0)
    (hno : ¬ ∃ k, ∀ j, slack (h f) (c f) (fun i => B i j) = 0 → B k j = 0) :
    ∃ p, (∀ k, 0 < p k) ∧ Feasible A b p ∧ slack (h f) (c f) p < 0 ∧
      ∀ g, g ≠ f → 0 < slack (h g) (c g) p := by
  classical
  let s := incidentIndices B (h f) (c f)
  let x := average s B
  let β := average Finset.univ B
  have hu : (Finset.univ : Finset Col).Nonempty := Finset.univ_nonempty
  have hxpos : ∀ k, 0 < x k := average_pos_of_no_zero_coordinate s htight B
    (fun i j _ => hnonneg i j) (by
      rintro ⟨k, hk⟩
      exact hno ⟨k, fun j hj => hk j ((mem_incidentIndices _ _ _ _).mpr hj)⟩)
  have hx : Feasible A b x := average_feasible B A b s htight (fun j _ => he j)
  have hxtight : slack (h f) (c f) x = 0 := slack_average_eq_zero s htight B (h f) (c f)
    (fun j hj => (mem_incidentIndices B (h f) (c f) j).mp hj)
  have hβ : Feasible A b β := average_feasible B A b Finset.univ hu (fun j _ => he j)
  have hβslack : 0 < slack (h f) (c f) β := (slack_average_pos_iff Finset.univ hu B _ _
    (fun j _ => hvalid f j)).mpr (by obtain ⟨j, hj⟩ := hproper; exact ⟨j, Finset.mem_univ _, hj⟩)
  have hother : ∀ g : {g : I // g ≠ f}, 0 < slack (h g) (c g) x := by
    intro g
    obtain ⟨j, hjf, hjg⟩ := incident_strict_of_plane_separation B A b (h f) (h g)
      (c f) (c g) hspan (hvalid g) (hsep g g.2)
    exact (slack_average_pos_iff s htight B (h g) (c g) (fun j _ => hvalid g j)).mpr
      ⟨j, (mem_incidentIndices _ _ _ _).mpr hjf, hjg⟩
  obtain ⟨ε, _, hp, ho, ha, hv⟩ := exists_positive_violator x β (h f) (c f)
    (fun g : {g : I // g ≠ f} => h g) (fun g => c g) A b
    hxpos hxtight hβslack hother hx hβ
  exact ⟨perturb x β ε, hp, ha, hv, fun g hg => ho ⟨g, hg⟩⟩

/-- The inequality `hᵀp ≤ c` holds at every nonnegative solution of `A p = b`. For
a district matrix, the normalization equations among the equations of the affine
hull make the nonnegative solutions the points of the cross-product of probability
simplices. -/
def CoordinateTrivial (A : Matrix E Row ℝ) (b : E → ℝ) (h : Row → ℝ) (c : ℝ) : Prop :=
  ∀ p, (∀ k, 0 ≤ p k) → Feasible A b p → 0 ≤ slack h c p

/-- The inequality of `f` holds at every nonnegative solution of `A p = b` exactly
when some entry `p_k` is zero at every column on its facet. The hypotheses include
`FacetSpan` for `f` and, for each other inequality, a solution on the facet plane
of `f` that is off the plane of the other inequality. -/
theorem coordinate_trivial_iff_incident_zero {I : Type*} [Fintype I]
    (B : Matrix Row Col ℝ) (A : Matrix E Row ℝ) (b : E → ℝ)
    (h : I → Row → ℝ) (c : I → ℝ) (f : I)
    (hspan : FacetSpan B A b (h f) (c f))
    (hnonneg : ∀ i j, 0 ≤ B i j) (hcover : ∀ i, ∃ j, 0 < B i j)
    (he : ∀ j, Feasible A b (fun i => B i j))
    (hvalid : ∀ g j, 0 ≤ slack (h g) (c g) (fun i => B i j))
    (hproper : ∃ j, 0 < slack (h f) (c f) (fun i => B i j))
    (htight : (incidentIndices B (h f) (c f)).Nonempty)
    (hsep : ∀ g, g ≠ f → ∃ p, Feasible A b p ∧
      slack (h f) (c f) p = 0 ∧ slack (h g) (c g) p ≠ 0) :
    CoordinateTrivial A b (h f) (c f) ↔
      ∃ k, ∀ j, slack (h f) (c f) (fun i => B i j) = 0 → B k j = 0 := by
  constructor
  · intro htriv
    by_contra hno
    obtain ⟨p, hp, ha, hv, _⟩ := positive_violator_of_no_incident_zero B A b h c f
      hspan hnonneg he hvalid hproper htight hsep hno
    have hnon := htriv p (fun k => (hp k).le) ha
    linarith
  · rintro ⟨k, hk⟩
    obtain ⟨α, hα, weights, hcert⟩ := coordinate_certificate_of_columns B A b (h f) (c f)
      hspan hnonneg hcover he (hvalid f) hproper htight k hk
    intro p hp ha
    rw [hcert]
    have hz : (∑ e, weights e * (score (A e) p - b e)) = 0 :=
      Finset.sum_eq_zero fun e _ => by rw [ha e, sub_self, mul_zero]
    rw [hz, add_zero]
    exact mul_nonneg hα.le (hp k)

end MeraConstraints.FacetCriterion
