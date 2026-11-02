# Semantic audit during formalization

Specification checked: `sources/manuscript/main-revised.tex` and
`sources/manuscript/appendix.tex`, 2026-11-02. Line numbers below refer to
these source files. This log distinguishes a mathematical counterexample
to an insufficient formulation from a missing Lean proof. The original
manuscript has not been edited.

## 1. District independence needs a joint statement

**Status: resolved by author clarification: full mutual independence is intended.**

The author confirmed in this chat that the assumption is full mutual
independence of district response vectors. The Lean product-law assumption
therefore matches the intended manuscript semantics. The discussion and
counterexample below document why the displayed pairwise equations alone
would not express that intention; they are not an outstanding mathematical
objection to the manuscript. A textual clarification remains an editorial
suggestion, not a missing assumption in the intended model.

Lean status: the construction now uses the literal product law
`Independent.joint` on whole district profiles; the implementation does not
substitute pairwise independence for this condition.

`main-revised.tex:305` describes the response-variable graph by stating
pairwise independence of selectors with no undirected edge between them.
`appendix.tex:241`, `:256` and `:270` use the stronger fact that the entire
response-function vectors of distinct districts are *mutually independent*.
The latter is appropriate for the intended graphical model, but it does not
follow from the displayed pairwise equations alone.

For example, take independent fair binary variables `R₁` and `R₂` and set
`R₃ = R₁ xor R₂`. Each pair is independent. The joint distribution is not a
product: `(0,0,1)` has probability zero, whereas the product of the three
marginals assigns it probability `1/8`. Thus a three-district construction
using only pairwise independence would invalidate the product-of-districts
step of the completeness proof.

The finite example is now kernel-checked in
`MeraConstraints/Examples/PairwiseIndependence.lean`: `marginal_X`,
`marginal_Y`, `marginal_Z`, `independent_XY`, `independent_XZ`,
`independent_YZ` and `not_mutually_independent` prove these claims directly.

Suggested clarification after the response transformation: the joint law
factorizes as the product of unrestricted within-district joint laws,
`P(R) = ∏_D P(R_D)`. This is already the assumption explicitly used in the
appendix, not a new restriction on the intended model.

## 2. Private noise is implicit when singleton latent vertices are removed

**Status: semantic convention to state explicitly; not a disproof of the
intended marginal-model result.**

Lean status: private disturbances are now explicit in `HiddenGraph.SCM`.
`HiddenGraph.Source` and `sourceDistrictEquiv` account for unconfounded
singleton inputs in the c-degree-at-most-one realization construction.

`main-revised.tex:113` calls the model an NPSEM. Condition A2 at `:123--124`
removes hidden vertices with fewer than two children. The response
transformation at `:298--305` nevertheless introduces a response selector
for *every* observed variable, including singleton districts, with arbitrary
selector laws. These statements are consistent if observed vertices retain
stochastic kernels, or equivalently independent private disturbances omitted
from the graph used to count common causes.

A literal deterministic structural-equation model with only the explicitly
drawn hidden variables would be different: one observed root and no hidden
vertices could generate only a point mass. The manuscript's singleton
district instead allows every categorical distribution, including positive
ones. A Lean model must therefore retain private disturbances or stochastic
kernels and count only shared hidden causes in c-degree.

Suggested clarification: private independent disturbances are implicit at
observed vertices and do not contribute to the displayed hidden child sets
or c-degree. Independence across districts then includes these private
disturbances.

There is a related small omitted case in `appendix.tex:241`: it invokes
Proposition `prop:ident` for every district, although that proposition's
statement (`main-revised.tex:399`) assumes c-degree one. C-degree-zero
districts are singletons and admit the same finite-selector representation
by the usual independent response construction. State this elementary case
when assembling the district factors.

## 3. Two closure notions must remain distinct in Lean

**Status: initial Lean correspondence issue resolved; the manuscript
explicitly makes the distinction.**

`main-revised.tex:599` defines a *closed* set using observed ancestors in the
full graph. Its equations (O) are the trivial equality equations in
Proposition `prop:nontrivial` (i). At `:623`, *closed in the district* means
closure under internal observed parents. This weaker condition can yield
nontrivial Verma equalities because directed ancestral paths may leave the
district and reenter it.

For example, in `A → B → C → D` with a shared latent parent of `B,D`, the
district subset `{D}` is internally closed but not closed in the full
ancestor order, since `B` is an ancestor of `D` through `C`. The resulting
kernel-margin independence from `A` is the Verma equality discussed at
`main-revised.tex:623--627`.

The initial `District.Closed` definition checks internal parents only.
Its theorem about marginal dependence is mathematically valid, but calling
every instance an equation (O) obscures this distinction: it includes the
Verma-type instances as well. Document it as internal closure and add a
separate full-graph closure bridge before deriving triviality. Do not use
internal closure alone to prove the manuscript's characterization of trivial
equalities.

Resolution checked: the implementation now calls the predicate
`District.ClosedInDistrict` and its theorem
`marginal_eq_of_closedInDistrict`. Its documentation explicitly distinguishes
the full-ancestor-closed equations (O) from possible Verma constraints.
`HiddenGraph/Ancestry.lean` now proves full closure implies internal closure,
and `Examples/VermaClosure.lean` checks that the converse fails in the paper's
Verma graph. The compact matrix now uses the actual global member subtypes
directly, with proved local evaluation and full-row projection identities;
the identification proof does not rely on an unproved reindexing to the
older, separately indexed local `District.Graph` foundation.

## 4. Inherited literate prose must refer to the current paper

**Status: inherited Lean documentation issue resolved; not a defect in the
manuscript.**

The adapted foundational modules retained explanatory prose for the
different `causaloptim-lean` paper:

- `Probability/Finite.lean` describes the old left/right split and labels
  its independence restriction "Condition 2". Current A2 concerns latent
  child sets; district independence is the relevant factorization here.
- `SCM/Basic.lean` says the manuscript orders left-side variables before
  right-side variables. The current manuscript instead fixes a topological
  observed-variable order, with districts possibly interleaved.
- `SCM/ResponseFunction.lean` repeatedly identifies its canonical partition
  theorem with "Proposition 1" of the current paper. Current `prop:hlp` is
  the first proposition; canonical partitioning is background in
  `sec:respvar`. The historical declaration name `SCM.proposition1` may be
  retained, but its prose must identify the source paper and explain that
  it is reused background here.

Also qualify the opening finite-probability discussion: the original latent
inputs may be infinite. Finite probability vectors enter after the
response-function reduction; the pointwise structural maps are not all on
finite types.

Resolution checked: the probability module now describes finite response
laws and arbitrary original latent spaces separately; the SCM module allows
interleaved districts and identifies itself as general reused background;
the response-function module explicitly identifies the source manuscript
and the historical meaning of `SCM.proposition1`.

## 5. Review of the constructive completeness step

**Status: formalization scope, not newly discovered manuscript defects.**

The new `Reconstruction`, `GlobalModel`, `Completeness` and `HiddenGraph`
chapters were reviewed against the proof at `appendix.tex:239--276`.

- `Reconstruction.conditioningVariables` agrees with the revised `C_i`:
  preceding members of the same district, plus external parents of every
  member up to and including the current one. In particular it does not
  use only the current member's external parents.
- `Reconstruction.OrderedMarkov` supplies atomic event independence equations
  for the actual observed law. These equations suffice for the proved chain
  rule and reconstruction. `GlobalModel.observed_orderedMarkov` now derives
  precisely these equations for strictly positive laws generated by the
  independent finite-profile construction. It uses parent restrictions,
  prefix-event factorization and averaging over predecessor fibers, rather
  than assuming them of the generated law. The original-measure
  canonicalization described below now transports these ordered equations
  to actual original SCM laws with arbitrary measurable input spaces.
  This still does not enumerate or prove all graphical d-separation
  statements; it proves the precise ordered equations used in reconstruction.
- `GlobalModel.observed_eq_prod_factor` derives the product-event formula
  from recursive structural uniqueness and a mutually independent profile
  law. It does not assume that contracting districts yields an acyclic
  graph; observed paths may leave and reenter a district.
- The source/district bijection in `HiddenGraph.Components` uses the
  c-degree bound. In particular it does not simulate a higher-c-degree
  district by copying one correlated profile to several latent roots.
- `sourceMechanisms` reads one permitted latent parent, or the observed
  vertex's own private input, and `source_joint_reindex` preserves the
  product law under the proved bijection. The prior representation gap has
  been resolved by `HiddenGraph/SCMRealization.lean`: `profileSCM` is an
  explicit parent-restricted `HiddenGraph.SCM`, `profileSCM_eval` identifies
  its evaluation with the source mechanisms, and
  `sourceObserved_eq_profileSCM` identifies its pushforward under the
  independent source law. `Completeness.realize_with_explicit_SCM` supplies
  this concrete SCM realization for the constructive inclusion.
- `GlobalModel.matrix` uses full observed assignments as rows, with repeated
  rows as irrelevant coordinates vary. The manuscript's matrix instead
  uses district assignments and external-parent assignments. This
  correspondence gap is now resolved by `CompactDistrict.lean` and
  `CompactDistrict/Observable.lean`: the row projection is surjective,
  its matrix pullback is exactly the full-row matrix, and the actual
  observable product is constant on its fibers. Checked compact H-systems
  therefore transfer directly to full-row feasibility. Exactness of a
  numerical R/cdd H-system remains a proof obligation for that supplied
  system; the row transport does not certify the conversion algorithm.
- Pointwise faithfulness of the structural response map allows arbitrary
  latent types. The probability-law bridge is now proved as well:
  `HiddenGraph/Canonicalization.lean` handles arbitrary given finite original
  input laws, and `HiddenGraph/MeasureCanonicalization.lean` handles original
  inputs on arbitrary probability spaces without finite/countable state-space
  assumptions. `Probability/IndependentGroupingMeasure.lean` derives
  independence after disjoint grouping of the original inputs, and
  `HiddenGraph/Measurability.lean` derives the needed local-profile
  measurability from the ordinary structural mechanism measurability.
  Independence of induced response profiles is a conclusion, not a premise.

## 6. Original-measure identification and constraints

**Status: original-model probability-law correspondence resolved in both
directions; semantic review found no defect.**

The indexing in the canonicalization is faithful: an `inl i` input is the
private disturbance of observed vertex `i`, and an `inr u` input is the
listed latent root `u`. A local profile reads only its member's private input
and latent parents, all of which lie in that member's district. The universe
lifts change neither native input values nor the structural mechanisms.

`Identification.original_measure_district_linear` identifies the actual
original SCM's observable cumulative-conditioning product with the compact
matrix applied to the profile law *induced by that original SCM*. Its only
independence premise concerns the original roots/private inputs. The law
transport derives mutual independence of the district profiles.

`Identification.observableFactor_eq_externalInterventionLaw` additionally
identifies that observable quantity with an actual surgical intervention on
the same original SCM, preserving the original probability law. Only the
external observed parents are fixed; `HiddenGraph/Intervention.lean` proves
that this gives the same district output as fixing the whole complement.
Neither the observational identification nor this reduction is assumed as
an input to the theorem.

Strict positivity is required only for the observational conditioning steps
and is stated for every *observed* complete assignment. The induced profile
law and original latent law may have zeros. The canonicalization and
interventional matrix identities themselves also apply when the observed
law has zeros; this does not yet prove the manuscript's full boundary
completion rule.

The new `Completeness.original_measure_satisfies_compact_HRep` supplies
necessity for actual original SCMs with arbitrary measurable independent
inputs. This direction and the identification identities hold at every
c-degree. At higher c-degree the induced profile laws remain constrained
by the mechanisms; the code does not infer freedom to choose arbitrary
district profile laws. Sufficiency of all simplex-valued profile laws still
requires c-degree at most one.

The prior reverse probability-measure packaging gap is now resolved by
`HiddenGraph/MeasureRealization.lean`. Its `probabilityModelOfProfiles`
constructs a literal `HiddenGraph.ProbabilityModel`: an original
parent-restricted SCM, a probability space, measurable original input maps,
full mutual independence of those original inputs, and measurable
mechanisms. The finite simplex source law becomes an actual sum-of-Dirac
probability measure by `MeasureFinite.measureOfLaw`.

The original-input independence proof groups source coordinates by their
original graph vertices. Each original latent or private input reads only
its own group; unused private inputs at confounded vertices are constants.
Empty groups are allowed. Thus the construction does not assume independence
of the desired original inputs merely because source profiles are independent.
It proves that independence by disjoint grouping and measurable coordinate
maps, and proves the observed law is the evaluation law of the actual SCM.

`Completeness.original_model_iff_compact_HRep` consequently has a genuine
original-model existence statement on its left: there exists an arbitrary
`ProbabilityModel` whose observed law is `p`. That bundle contains no
response-law, Markov, H-constraint or target-distribution field. The forward
proof canonicalizes the given original model; the reverse proof obtains
finite source laws from the compact constraints and uses the actual
probability-model construction. There is no circular definition of the
model class by the constraints it should satisfy.

For strictly positive observed laws and c-degree at most one, this proves
that the ordered equations together with exact compact H-constraints form
a complete set of constraints for the original probability models. The
formal predicate uses the proved sufficient ordered equations; it is not
yet a separate predicate enumerating every ordinary graphical conditional
independence. This is an explicit formulation difference, not a missing
original-model direction of the proved equivalence.

## 7. Remaining semantic and algorithmic coverage

These are unfinished formalization obligations, not newly discovered flaws
in the manuscript:

- Formalize an explicit all-d-separation conditional-independence predicate
  and relate it to the proved ordered equations and original model laws
  when expressing the manuscript's exact `C(G)` wording. No equivalence
  between the independence predicates alone is asserted. The existing
  equivalence already establishes completeness of the explicitly stated
  ordered equations plus H-system.
- Boundary completion is now checked, including classification by the first
  zero or undefined conditional, converse reconstruction and actual original
  model realization. The compact H-system remains a checked exact input.
- Complete the graph-specific nontriviality theorem. The finite-dimensional
  affine consequence, rank-count and perturbation lemmas are established,
  and the actual full-ancestry (N)/(O) matrices are now established, but
  identifying them with all graph-trivial equality constraints requires
  the positive-kernel realization argument. The geometric facet incidence
  criterion and coordinate certificate are checked from codimension-one
  ranks; its graph-compatible positive observed-law witness remains separate.
- Certify concrete H-representations or the conversion algorithm. The
  generic completeness theorems take an exact `HRep` with its equivalence
  proof as an input; an external R/cdd output is not accepted without such
  a proof. Latent merging is checked as an original-to-merged inclusion;
  further graph-transform and general inequality-structure arguments need
  their own formal coverage.

## Checked qualifications and directions

No new counterexample to the intended identification, completeness or facet
criterion was found in this audit. In particular:

- Strict positivity is explicitly assumed globally at
  `main-revised.tex:113`, and `rmk:positivity` addresses the boundary. The
  positive-distribution propositions should not be reported as missing
  positivity merely because their individual statements do not repeat it.
- `main-revised.tex:805--806` calls the original graph `G'` and the merged
  graph `G`. The inclusion in `appendix.tex:352`, `M(G') ⊆ M(G)`, has the
  correct direction: merging relaxes the model and gives constraints valid
  for the original model. Do not invert that direction when renaming graphs
  in Lean.
- The small-positive-perturbation argument at `appendix.tex:310` needs a
  finite family of other facet inequalities. This follows from the finite
  H-representation in the manuscript. `Geometry.exists_positive_violator`
  makes this finiteness hypothesis explicit and preserves equality rows
  without a finiteness requirement on their index type.
- A proper facet's average of incident columns is strict on every other
  distinct facet. This relies on the hypothesis that the listed rows define
  distinct facets, explicitly included at `main-revised.tex:607`. The new
  facet span chapter now derives the strict incident-column property from
  distinct incident spans and actual codimension-one direction ranks.

## 8. Transformation wording and graph domain

The merging proof's wording at `appendix.tex:352` that an observed variable
can depend on the merged root only through old-parent components describes
the constructed embedding of an original model. It is not a restriction on
arbitrary merged models. Clarifying this would help explain why the result
is inclusion rather than equality; the stated inclusion is correct.

Strong Face Splitting assumes A1 only. Its raw split graph can have empty,
single-child or nested latent child sets before the manuscript's subsequent
reductions restore A2. A formalization must therefore allow that intermediate
graph, rather than require it to inhabit the existing A1/A2 graph type.
This is a formal interface requirement, not a manuscript defect.

The chosen root family in Strong Face Splitting must also be nonempty
(`k ≥ 1`). The instruction to choose roots with a common child suggests this
intention. If an empty family were admitted, the two numbered conditions
would be vacuous while the transformation could add a common cause to
previously independent observed nodes. The formal construction therefore
requires a selected root as an anchor. Making `k ≥ 1` explicit would remove
this boundary ambiguity.
