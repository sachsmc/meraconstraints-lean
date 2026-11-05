import MeraConstraints.Completeness.Global
import MeraConstraints.Completeness.HLP
import MeraConstraints.Completeness.Merging
import MeraConstraints.Completeness.StrongFaceSplitting
import MeraConstraints.Identification.OriginalMeasure
import MeraConstraints.CompactDistrict.EqualityRank
import MeraConstraints.CompactDistrict.FacetWitness
import MeraConstraints.CompactDistrict.Incidence
import MeraConstraints.HiddenGraph.InstrumentalInequalities
import MeraConstraints.HiddenGraph.BellInequalities

/-!
# The manuscript's main results, in manuscript order

This page restates each main result of *Deriving Complete Constraints in Hidden
Variable Models* as one Lean theorem. Each theorem is named after the LaTeX
label of the result it formalizes, so `prop_complete` is `\label{prop:complete}`.
The theorem's proof only points to the longer development elsewhere in this
library, so what is stated here is what Lean has verified. If a statement
differs from the manuscript, the theorem's description says how.

## How to read a Lean statement

No knowledge of Lean is needed to read the statements below.

* `theorem name (h : A) : B` says "if `A` holds, then `B` holds". Everything
  before the final colon is a hypothesis of the result. There are no hidden
  hypotheses, so this list is exactly what the result assumes.
* `(p : FullAssign val → ℝ)` means `p` assigns a real number to every joint value
  of the observed variables. `p ∈ stdSimplex ℝ _` says it is a probability vector.
* `∀ x, A` is "for all `x`, `A`", `∃ x, A` is "there is an `x` with `A`", `A ∧ B` is
  "`A` and `B`", `A ↔ B` is "`A` if and only if `B`", and `¬ A` is "not `A`".
* `∑ x, f x` is a sum and `∏ x, f x` is a product over all values of `x`.
* Square-bracket hypotheses such as `[∀ i, Fintype (val i)]` are standing
  assumptions; this one says every observed variable has finitely many values.
* The proof comes after `:=`. It can be skipped: Lean has verified it.

## Dictionary from the manuscript to Lean

The observed variables `V_1, …, V_n` are numbered in a topological order of the
graph. This loses no generality, since any DAG can be relabeled that way, and
the manuscript's "ordering consistent with a topological ordering" is then the
numeric order. Other orderings are covered in `GlobalModel.OrderingInvariance`.

* Hidden variables DAG `𝒢(V, U)` satisfying Conditions 1 and 2 (`A1`, `A2`):
  `HiddenGraph.Graph n ℓ`, with `n` observed and `ℓ` unobserved variables.
* Values of `V_i`: the type `val i`. Joint value `v` of `V`: `FullAssign val`.
* District: `DistrictId G`. Its members `V₁`: `CompactDistrict.Member`. Its
  external parents `V₂`: `CompactDistrict.ExternalParent`.
* c-degree of a district, and of a DAG: `cDegree`, `graphCDegree`.
* Structural model with independent inputs, generating one distribution in the
  marginal model: `HiddenGraph.ProbabilityModel`.
  Marginal model `𝓜(𝒢)`: `MarginalModel` below.
* Conditional independencies implied by `𝒢`: `GlobalMarkov`.
* Profile, one joint value of the response functions of a district's members:
  `DistrictProfile`. Vector `r` of response function variable probabilities:
  a probability vector over profiles.
* Matrix `B`: `districtMatrix`, with rows `(v₁, v₂)` given by `CompactDistrict.Row`
  and one column per profile. District polytope `{B r}`: `Polytope.mixture B`.
* District factor `Pdo(V₁ = v₁ ∣ V₂ = v₂)`, the entries of `p`: `districtFactor`.
* H-representation `H_i p ≤ b_i`, `H_e p = b_e`: `Polytope.HRep`, with fields
  `inequalities` (`H_i`), `upper` (`b_i`), `equalities` (`H_e`), `target` (`b_e`).
  It contains a proof that it describes the same set as the district polytope.
* Cross-product of probability simplices `P̌`: `CompactDistrict.InSimplexProduct`.
* Equations (N) and (O), stacked: `CompactDistrict.OrderingConstraints.constraintsMatrix`.
  Closed set: `HiddenGraph.FullClosed`. Closed in the district:
  `HiddenGraph.ClosedInDistrict`.
* Trivial constraints: `CompactDistrict.EqualityTrivial` and
  `CompactDistrict.InequalityTrivial`.
* Affine hull of the polytope: `FacetCriterion.columnHull`. Affine hull of the
  columns on a facet: `FacetCriterion.incidentHull`.
* `gᵀp`: `EqualityConstraints.score g p`. `c - hᵀp`: `Geometry.slack h c p`.
* `M p = a` for a matrix `M`: `EqualityConstraints.Feasible M a p`.

## Modeling choices to keep in mind

* **Private noise.** Each observed variable also has its own independent
  unobserved input, which the graph does not draw. This matches the manuscript's
  response function variable for every observed variable, including singleton
  districts, and these inputs do not count towards the c-degree.
* **Independence.** All unobserved inputs are mutually independent, not just
  pairwise independent. The unobserved variables may take values in any
  measurable space; only the observed variables must be finite.
* **The H-representation is an input.** The results apply to any H-representation
  that comes with a proof that it matches the polytope. Lean does not run or
  verify the double description method. That such a representation exists is the
  Minkowski–Weyl theorem, which is not proved here.
* **Conditional independencies.** "Implied by `𝒢`" is defined by separation in the
  ancestral moral graph, a standard equivalent of d-separation. The equivalence
  itself is not formalized. See `HiddenGraph.MoralSeparated`.
-/

namespace MeraConstraints.MainResults

open HiddenGraph MeasureTheory EqualityConstraints Geometry
open GlobalModel.KernelReconstruction CompactDistrict.OrderingConstraints

universe u

/-! ## Vocabulary used in the statements -/

section Vocabulary

variable {Row Col I E : Type*} [Fintype Row] [Fintype Col]

/-- The vector `p` satisfies the H-representation: `H_i p ≤ b_i` and `H_e p = b_e`. -/
def Satisfies {B : Matrix Row Col ℝ} (H : Polytope.HRep B I E) (p : Row → ℝ) : Prop :=
  (∀ i, ∑ x, H.inequalities i x * p x ≤ H.upper i) ∧
    ∀ e, ∑ x, H.equalities e x * p x = H.target e

/-- The hypothesis of `prop:nontrivial`: "each row of `H_i` defines a different
facet of the district polytope and the rows of `H_e` define its affine hull". -/
structure DefinesFacetsAndHull {B : Matrix Row Col ℝ} (H : Polytope.HRep B I E) : Prop where
  /-- The rows of `H_e` define the affine hull of the polytope. -/
  hull : ∀ q, q ∈ FacetCriterion.columnHull B ↔ Feasible H.equalities H.target q
  /-- No row of `H_i` holds with equality on the whole polytope. -/
  proper : ∀ f, ∃ j, 0 < slack (H.inequalities f) (H.upper f) (fun x => B x j)
  /-- Some column of `B` lies on each row's face. -/
  incident : ∀ f, (FacetCriterion.incidentColumns B (H.inequalities f) (H.upper f)).Nonempty
  /-- Each face has dimension one less than the polytope, so it is a facet. -/
  codimension_one : ∀ f, Module.finrank ℝ (FacetCriterion.columnHull B).direction =
    Module.finrank ℝ (FacetCriterion.incidentHull B (H.inequalities f) (H.upper f)).direction + 1
  /-- Different rows define different facets. -/
  distinct : ∀ f g, g ≠ f →
    FacetCriterion.incidentHull B (H.inequalities f) (H.upper f) ≠
      FacetCriterion.incidentHull B (H.inequalities g) (H.upper g)

end Vocabulary

variable {n ℓ : ℕ} (G : Graph n ℓ) (val : Fin n → Type u)
variable [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]

/-- The compatibility matrix `B` of a district. Entry `(v₁, v₂), r` is `1` when
the profile `r` gives the members the values `v₁` once their external parents
are fixed to `v₂`, and `0` otherwise. -/
noncomputable abbrev districtMatrix (d : DistrictId G) :=
  CompactDistrict.matrix G.observed val (observedDistrict G) d

/-- The vector `p` of a district: the entries `Pdo(V₁ = v₁ ∣ V₂ = v₂)`, computed
from an observed distribution with the conditioning sets `C_i` of `prop:ident`. -/
noncomputable abbrev districtFactor [∀ i, Nonempty (val i)]
    (p : FullAssign val → ℝ) (d : DistrictId G) :=
  CompactDistrict.districtFactor G.observed val (observedDistrict G) d p

variable [∀ i, MeasurableSpace (val i)]

/-- The marginal model `𝓜(𝒢)`: the observed distributions generated by some
structural model on `𝒢` with mutually independent unobserved inputs. The
definition mentions no constraints and no response function variables. Unlike
the manuscript's `𝓜(𝒢)` in `prop:complete`, it includes distributions with zero
probabilities; `prop_complete` restricts to strictly positive ones. -/
def MarginalModel : Set (FullAssign val → ℝ) :=
  {p | ∃ P : ProbabilityModel G val, P.observed = p}

variable {G val}
variable [∀ i, MeasurableSingletonClass (val i)]

/-- The probability vector `r` that a structural model induces on the profiles of
a district: the distribution of the response function variables `R_{V₁}`. -/
noncomputable def responseLaw (P : ProbabilityModel G val) (d : DistrictId G) :
    DistrictProfile G val d → ℝ :=
  letI := P.sampleSpace
  letI := P.inputSpaces
  MeasureCanonicalization.canonicalLaw P.model P.measure P.inputs d

/-- `Pr(V₁ = · ∣ do(V₂ = v₂))` in a structural model: the distribution of the
district's members after setting its external parents to their values in `v`. -/
noncomputable def doLaw (P : ProbabilityModel G val) (d : DistrictId G) (v : FullAssign val) :
    CompactDistrict.MemberAssign val (observedDistrict G) d → ℝ :=
  letI := P.sampleSpace
  letI := P.inputSpaces
  Identification.externalInterventionLaw P.model P.measure P.inputs d v

/-! ## Section 2: the response function variable transformation -/

omit [DecidableEq (DistrictId G)] [∀ i, Fintype (val i)] [∀ i, DecidableEq (val i)]
  [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Remark 1 (`rmk1`).** Replacing the unobserved inputs by the response
functions they induce gives the same values of all observed variables, under any
intervention on any observed variables and under no intervention.

The manuscript states this for c-degree 1. It holds without that restriction,
because it is a statement about each fixed value of the unobserved inputs. -/
theorem rmk1 (M : HiddenGraph.SCM G val) (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u ε =
      evalR (interveneProfile (M.responseProfile u ε) targets setTo) :=
  M.eval_intervene_eq_evalR u ε targets setTo

variable [∀ i, Nonempty (val i)]

/-- **Proposition 1 (`prop:ident`).** The district factor is linear in the response
function variable probabilities: `p = B r`, where `r` is the probability vector the
model induces on the district's profiles.

Read this in the manuscript's setting of c-degree at most 1, where `r` can be any
probability vector, so the district factors form the district polytope. The Lean
statement has no c-degree hypothesis because the proof of the identity does not use
one. It does not describe the marginal model at higher c-degree. -/
theorem prop_ident (P : ProbabilityModel G val) (hpos : ∀ w, 0 < P.observed w)
    (d : DistrictId G) (x : CompactDistrict.Row G.observed val (observedDistrict G) d) :
    responseLaw P d ∈ stdSimplex ℝ (DistrictProfile G val d) ∧
      districtFactor G val P.observed d x = (districtMatrix G val d).mulVec (responseLaw P d) x := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  letI := P.probability
  have hLocal := Measurability.localProfile_measurable P.model P.measurableMechanisms
  refine ⟨MeasureCanonicalization.canonicalLaw_mem_stdSimplex P.model P.measure P.inputs
    P.measurableInputs hLocal d, ?_⟩
  have h := Identification.original_measure_district_linear P.model P.measure P.inputs
    P.measurableInputs P.independent P.measurableMechanisms hpos d
    (CompactDistrict.extend G.observed val (observedDistrict G) d x)
  rwa [CompactDistrict.project_extend] at h

/-- **Proposition 2 (`causalprop`).** The intervention distribution
`Pr(V₁ = v₁ ∣ do(V₂ = v₂))` is identified, and equals the district factor. There is
no restriction on the c-degree. The intervention is carried out on the structural
model itself, replacing the mechanisms of the external parents by constants. -/
theorem causalprop (P : ProbabilityModel G val) (hpos : ∀ w, 0 < P.observed w)
    (d : DistrictId G) (w : FullAssign val) :
    districtFactor G val P.observed d (CompactDistrict.project G.observed val (observedDistrict G) d w) =
      doLaw P d w (fun i => w i) := by
  letI := P.sampleSpace
  letI := P.inputSpaces
  letI := P.probability
  exact (CompactDistrict.districtFactor_project G.observed val (observedDistrict G) d
    P.observed w).trans (Identification.districtFactor_eq_externalInterventionLaw P.model
      P.measure P.inputs P.measurableInputs P.independent P.measurableMechanisms hpos d w)

/-! ## Section 3: completeness -/

variable (G val)

/-- **Proposition 3 (`prop:complete`).** Let `𝒢` satisfy Conditions 1 and 2 and have
c-degree at most 1. A strictly positive distribution `p` is in the marginal model
exactly when it satisfies the conditional independencies implied by `𝒢` and, in every
district, the H-representation constraints on its district factor. -/
theorem prop_complete (hdegree : graphCDegree G ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep (districtMatrix G val d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) (hpos : ∀ w, 0 < p w) :
    p ∈ MarginalModel G val ↔
      GlobalMarkov G val p ∧ ∀ d, Satisfies (H d) (districtFactor G val p d) :=
  Completeness.original_model_iff_global_compact_HRep G val
    ((graphCDegree_le_iff G 1).mp hdegree) H p hp hpos

/-- **Remark 2 (`rmk:positivity`).** The extension of `prop_complete` to distributions
with zero probabilities. An entry of a district factor is free when the first factor
in its product that is not positive is undefined. Then `p` is in the marginal model
exactly when it satisfies the conditional independencies and, in every district, the
free entries can be chosen so that the H-representation constraints hold.
See `Completeness.Boundary.CompactHCompletion`. -/
theorem rmk_positivity (hdegree : graphCDegree G ≤ 1) {I E : DistrictId G → Type*}
    (H : ∀ d, Polytope.HRep (districtMatrix G val d) (I d) (E d))
    (p : FullAssign val → ℝ) (hp : p ∈ stdSimplex ℝ (FullAssign val)) :
    p ∈ MarginalModel G val ↔
      GlobalMarkov G val p ∧ Completeness.Boundary.CompactHCompletion G val H p :=
  Completeness.original_model_iff_global_boundary_compact_HCompletion G val
    ((graphCDegree_le_iff G 1).mp hdegree) H p hp

/-! ## Section 3: which constraints are trivial -/

variable {G val}

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Proposition 4 (`prop:nontrivial`), part (i), first claim.** An equation
`gᵀp = c` is trivial, meaning it holds for every strictly positive distribution with
the conditional independencies of `𝒢`, if and only if it is a linear combination of
the equations (N) and (O), with the same weights for coefficients and right-hand sides. -/
theorem prop_nontrivial_i_trivial_iff (hdegree : graphCDegree G ≤ 1) (d : DistrictId G)
    (g : CompactDistrict.Row G.observed val (observedDistrict G) d → ℝ) (c : ℝ) :
    CompactDistrict.EqualityTrivial G val d g c ↔
      RowCombination (constraintsMatrix G val d) (constraintsRhs G val d) g c :=
  CompactDistrict.equalityTrivial_iff_rowCombination G val d
    ((graphCDegree_le_iff G 1).mp hdegree) g c

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Proposition 4, part (i), second claim.** The number of linearly independent
nontrivial equality constraints is `rank(N; O; H_e) - rank(N; O)`. The left side is the
dimension of the space of all equality constraints of the district modulo the trivial
ones. Both spaces are defined without reference to any of these matrices. -/
theorem prop_nontrivial_i_rank (hdegree : graphCDegree G ≤ 1) (d : DistrictId G)
    {E : Type*} [Fintype E]
    (He : Matrix E (CompactDistrict.Row G.observed val (observedDistrict G) d) ℝ)
    (be : E → ℝ)
    (hhull : ∀ q, q ∈ FacetCriterion.columnHull (districtMatrix G val d) ↔ Feasible He be q) :
    Module.finrank ℝ (Modulo (CompactDistrict.graphTrivialSpace G val d)
        (CompactDistrict.districtEqualitySpace G val d)) =
      (Matrix.fromRows (constraintsMatrix G val d) He).rank - (constraintsMatrix G val d).rank :=
  CompactDistrict.nontrivialEquality_rank_count G val d
    ((graphCDegree_le_iff G 1).mp hdegree) He be hhull

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Proposition 4, part (i), third claim.** Rows of `H_e` that extend (N) and (O) to
span all of `(N; O; H_e)` imply, together with the conditional independencies, all the
equality constraints of the district. The manuscript chooses rows that extend a basis;
here any spanning choice is allowed. -/
theorem prop_nontrivial_i_selected (d : DistrictId G) {E F : Type*} [Fintype F]
    (He : Matrix E (CompactDistrict.Row G.observed val (observedDistrict G) d) ℝ)
    (be : E → ℝ) (pick : F → E)
    (hhull : ∀ q, q ∈ FacetCriterion.columnHull (districtMatrix G val d) ↔ Feasible He be q)
    (hspan : rowSpace (Matrix.fromRows (constraintsMatrix G val d) (fun f => He (pick f))) =
      rowSpace (Matrix.fromRows (constraintsMatrix G val d) He))
    (p : FullAssign val → ℝ) (hpos : ∀ w, 0 < p w) (hCI : GlobalMarkov G val p)
    (hselected : ∀ f, score (He (pick f)) (districtFactor G val p d) = be (pick f)) :
    Feasible He be (districtFactor G val p d) :=
  CompactDistrict.selected_equalities_imply_all G val d He be pick hhull hspan p hpos hCI hselected

section Inequalities

variable {d : DistrictId G} {I E : Type*} [Fintype I] [Fintype E]
  {H : Polytope.HRep (districtMatrix G val d) I E}

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)]
  [∀ i, Nonempty (val i)] [Fintype I] [Fintype E] in
private theorem row_valid (r : DistrictProfile G val d) (f : I) :
    0 ≤ slack (H.inequalities f) (H.upper f) (fun x => districtMatrix G val d x r) := by
  have hr := (H.exact_representation _).mp (CompactDistrict.column_mem_mixture G val d r)
  exact sub_nonneg.mpr (hr.1 f)

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Proposition 4, part (ii), first claim.** An inequality of `H_i` is trivial if
and only if some entry `p_k` is zero at every column of `B` on its facet. Trivial
means it holds at every point of the cross-product of simplices that satisfies `H_e`.

Read this in the proposition's setting of c-degree 1. The Lean statement has no c-degree
hypothesis because it concerns only the matrix `B`. -/
theorem prop_nontrivial_ii_trivial_iff (hF : DefinesFacetsAndHull H) (f : I) :
    CompactDistrict.InequalityTrivial G val d H.equalities H.target
        (H.inequalities f) (H.upper f) ↔
      ∃ k, ∀ r : DistrictProfile G val d,
        slack (H.inequalities f) (H.upper f) (fun x => districtMatrix G val d x r) = 0 →
          districtMatrix G val d k r = 0 :=
  CompactDistrict.inequalityTrivial_iff_incident_zero G val d H.equalities H.target
    H.inequalities H.upper f hF.hull (fun g r => row_valid r g) hF.proper hF.incident
    hF.codimension_one (fun g hg => hF.distinct f g hg)

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] [Fintype I] in
/-- **Proposition 4, part (ii), second claim.** In the trivial case,
`c - hᵀp = α p_k + λᵀ(H_e p - b_e)` with `α > 0`, for every vector `p`. So the
constraint is the nonnegativity constraint `p_k ≥ 0` written in a different form. -/
theorem prop_nontrivial_ii_nonnegativity_form (hF : DefinesFacetsAndHull H) (f : I)
    (k : CompactDistrict.Row G.observed val (observedDistrict G) d)
    (hzero : ∀ r : DistrictProfile G val d,
      slack (H.inequalities f) (H.upper f) (fun x => districtMatrix G val d x r) = 0 →
        districtMatrix G val d k r = 0) :
    ∃ α : ℝ, 0 < α ∧ ∃ lam : E → ℝ, ∀ p,
      slack (H.inequalities f) (H.upper f) p =
        α * p k + ∑ e, lam e * (score (H.equalities e) p - H.target e) :=
  CompactDistrict.coordinate_certificate_of_incident_zero G val d H.equalities H.target
    (H.inequalities f) (H.upper f) hF.hull (fun r => row_valid r f) (hF.proper f)
    (hF.incident f) (hF.codimension_one f) k hzero

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **The incidence test following Proposition 4.** Let `I` be the 0/1 matrix recording
which columns of `B` lie on which facets. A row of `H_i` is nontrivial if and only if
every entry of its row of `I Bᵀ` is positive. -/
theorem incidence_test (hF : DefinesFacetsAndHull H) (f : I) :
    (¬ CompactDistrict.InequalityTrivial G val d H.equalities H.target
        (H.inequalities f) (H.upper f)) ↔
      ∀ x, 0 < (FacetCriterion.incidence (districtMatrix G val d) H.inequalities H.upper *
        Matrix.transpose (districtMatrix G val d)) f x :=
  CompactDistrict.inequality_nontrivial_iff_incidence_product_pos G val d H.equalities H.target
    H.inequalities H.upper f hF.hull (fun g r => row_valid r g) hF.proper hF.incident
    hF.codimension_one (fun g hg => hF.distinct f g hg)

end Inequalities

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Proposition 4, part (ii), third claim.** A nontrivial inequality can be violated
on its own. There is a strictly positive distribution that satisfies the conditional
independencies, all equality constraints of all districts, and every other inequality
of every district, and that violates this one. The other inequalities of the same
district even hold strictly. -/
theorem prop_nontrivial_ii_witness (hdegree : graphCDegree G ≤ 1) {I E : DistrictId G → Type*}
    [∀ e, Fintype (I e)] [∀ e, Fintype (E e)] (d : DistrictId G)
    (H : ∀ e, Polytope.HRep (districtMatrix G val e) (I e) (E e))
    (hF : DefinesFacetsAndHull (H d)) (f : I d)
    (hnontrivial : ¬ CompactDistrict.InequalityTrivial G val d (H d).equalities (H d).target
      ((H d).inequalities f) ((H d).upper f)) :
    ∃ p : FullAssign val → ℝ, p ∈ stdSimplex ℝ (FullAssign val) ∧ (∀ w, 0 < p w) ∧
      GlobalMarkov G val p ∧
      (∀ e, Feasible (H e).equalities (H e).target (districtFactor G val p e)) ∧
      (H d).upper f < score ((H d).inequalities f) (districtFactor G val p d) ∧
      (∀ g, g ≠ f → score ((H d).inequalities g) (districtFactor G val p d) < (H d).upper g) ∧
      ∀ e, e ≠ d → ∀ g, score ((H e).inequalities g) (districtFactor G val p e) ≤ (H e).upper g :=
  CompactDistrict.observed_law_violating_only_facet G val d
    ((graphCDegree_le_iff G 1).mp hdegree) H f hF.hull hF.proper hF.incident
    hF.codimension_one (fun g hg => hF.distinct f g hg) hnontrivial

/-! ## Section 4: graphical structures that imply inequality constraints -/

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Remark 3 (`prop:ineqstructure`), type (i), instrumental type.** Suppose a district
has members `A` and `B` with `A` a parent of `B`, and a directed path from an external
parent `W` to `A` through members, such that no vertex on the path other than `A` is a
parent of `B`. If its members and external parents have at least two levels, every
H-representation of the district contains a nontrivial inequality.

Read this in the manuscript's setting of c-degree 1, where the district polytope is the
set of possible district factors. The Lean statement has no c-degree hypothesis because
it concerns only the matrix `B` and its polytope. It makes no claim about the marginal
model at higher c-degree, whose district factors need not form a polytope. -/
theorem prop_ineqstructure_i (d : DistrictId G) {I E : Type*}
    (H : Polytope.HRep (districtMatrix G val d) I E)
    (hstructure : InstrumentalStructure G d)
    (hlevels : CompactDistrict.HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ f : I, ¬ CompactDistrict.InequalityTrivial G val d H.equalities H.target
      (H.inequalities f) (H.upper f) :=
  instrumental_nontrivial_H_row G d val H hstructure hlevels

omit [∀ i, MeasurableSpace (val i)] [∀ i, MeasurableSingletonClass (val i)] in
/-- **Remark 3, type (ii), Bell type.** Suppose a district has members `A` and `B` and
external parents `W_A` and `W_B` such that `W_A` reaches `A` but not `B`, and `W_B`
reaches `B` but not `A`, where reaching means by a directed path through members. If
its members and external parents have at least two levels, every H-representation of
the district contains a nontrivial inequality.

Read this in the manuscript's setting of c-degree 1, as for type (i). The Lean statement
has no c-degree hypothesis because it concerns only the matrix `B` and its polytope. It
makes no claim about the marginal model at higher c-degree. -/
theorem prop_ineqstructure_ii (d : DistrictId G) {I E : Type*}
    (H : Polytope.HRep (districtMatrix G val d) I E)
    (hstructure : BellStructure G d)
    (hlevels : CompactDistrict.HasTwoLevels G.observed val (observedDistrict G) d) :
    ∃ f : I, ¬ CompactDistrict.InequalityTrivial G val d H.equalities H.target
      (H.inequalities f) (H.upper f) :=
  bell_nontrivial_H_row G d val H hstructure hlevels

/-! ## Section 5: graphs with c-degree greater than 1 -/

omit [DecidableEq (DistrictId G)] [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)] in
/-- **Proposition 5 (`prop:hlp`).** Let `𝒢` be a graph without the edge `a → b`, and
`𝒢⁺ = addEdge 𝒢 a b` the graph with it. If `Pa(a) ⊆ Pa(b)`, for both observed and
unobserved parents, and `a` and `b` share an unobserved parent, then the two graphs
have the same marginal model, and so the same constraints.

The variables are numbered in a topological order of `𝒢⁺`, which gives `a < b`. There
are no positivity or c-degree assumptions. -/
theorem prop_hlp (a b : Fin n) (hab : a < b)
    (hobserved : G.observed.parents a ⊆ G.observed.parents b)
    (hunobserved : ∀ j, a ∈ G.children j → b ∈ G.children j)
    (s : Fin ℓ) (hsa : a ∈ G.children s) (hsb : b ∈ G.children s) :
    MarginalModel G val = MarginalModel (HLP.addEdge G a b hab) val :=
  Set.ext fun p =>
    Completeness.original_model_iff_HLP G val a b hab hunobserved s hsa hsb hobserved p

omit [∀ i, DecidableEq (val i)] [∀ i, Nonempty (val i)] in
/-- **Proposition 6 (`prop:strong`), Strong Face Splitting.** Take a graph satisfying
Condition 1, with selected unobserved variables having children `C_i ∪ D` and other
unobserved variables having children `other j`. The graph `splitGraph`, in which the
selected variables are replaced by one with children `C_i` for each `i` and one with
children `D`, has the same marginal model.

The hypotheses here are those printed in the manuscript. The proof needs slightly
less: numbered condition 2 of the proposition can be weakened by replacing "contained
in any `C_i`" with "contained in `⋃ C_i`". See `StrongFaceSplitting.Conditions`.

These graphs need only satisfy Condition 1 (`A1`), since splitting can break `A2`. They
are therefore of the more general type `RootGraph`, and the structural models are of
type `RootProbabilityModel`, whose observed distribution is written as a measure. -/
theorem prop_strong {K J : Type u} [Fintype K] [Fintype J]
    (A : CausalDAG n) (C : K → Finset (Fin n)) (D : Finset (Fin n)) (other : J → Finset (Fin n))
    (h : StrongFaceSplitting.ManuscriptConditions A C D other) (p : Measure (FullAssign val)) :
    (∃ P : StrongFaceSplitting.RootProbabilityModel
        (StrongFaceSplitting.originalGraph A C D other) val, P.observed = p) ↔
      ∃ Q : StrongFaceSplitting.RootProbabilityModel
        (StrongFaceSplitting.splitGraph A C D other) val, Q.observed = p :=
  Completeness.original_model_iff_strongFaceSplitting A C D other val h.toConditions p

variable (G val)

omit [DecidableEq (DistrictId G)] in
/-- **Remark 4 (`prop:merge`).** Merging all unobserved variables of each district into
a single parent of all its members gives a graph of c-degree at most 1 whose marginal
model contains the original one. So every constraint of the merged graph holds on the
original graph. The reverse inclusion is not claimed, and need not hold. -/
theorem prop_merge :
    graphCDegree (Merging.mergedGraph G) ≤ 1 ∧
      MarginalModel G val ⊆ MarginalModel (Merging.mergedGraph G) val :=
  ⟨(graphCDegree_le_iff _ 1).mpr (Merging.mergedGraph_cDegree_le_one G),
    fun p hp => Completeness.original_model_subset_merged G val p hp⟩

end MeraConstraints.MainResults
