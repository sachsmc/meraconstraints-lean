# Semantic audit during formalization

Specification checked: `sources/manuscript/main-revised.tex` and
`sources/manuscript/appendix.tex`, updated 2026-11-03. Line numbers below refer to
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

For strictly positive observed laws and c-degree at most one, the original
ordered formulation already gave both original-model directions. The new
`Completeness.original_model_iff_global_compact_HRep` now replaces that
right-hand hypothesis with global graphical independencies. A graph cut
proves global-to-local, and the literal prefix-blanket/cumulative-`C_i`
identity derives the required ordered equations. The corresponding global
boundary theorem includes zero observations and the known/free completion
rule. The prior formulation difference in the completeness iff is resolved
under the explicitly documented ancestral-moral separation specification.

## 7. Remaining semantic and algorithmic coverage

These notes distinguish resolved semantic bridges from remaining formalization
obligations; they do not report newly discovered flaws in the manuscript:

- A global graphical independence predicate is now defined independently
  using ancestral moral separation in the original hidden DAG. The
  reconstructed kernel laws and actual original models at c-degree at most
  one satisfy it. Global-to-local is now proved for arbitrary laws, and the
  positive and boundary completeness iff statements use that global predicate
  directly. A general arbitrary-law local-to-global converse is not assumed.
- Boundary completion is now checked, including classification by the first
  zero or undefined conditional, converse reconstruction and actual original
  model realization. The compact H-system remains a checked exact input.
- The graph-specific nontriviality theorem is now assembled under its stated
  affine-hull and genuine distinct-facet assumptions. The finite-dimensional
  affine consequence, rank-count and perturbation lemmas are established,
  and the actual full-ancestry (N)/(O) matrices are now established. Their
  necessity for every positive globally Markov law is now proved by
  `GlobalModel.OrderingInvariance.observable_constraints`, including all fully
  closed subsets, rather than only numeric prefixes. The literal ancestral
  district margin equals the retained conditional product, so the ancestors
  of a fully closed subset give precisely its (O) margin and its own external
  parent dependence. This uses full observed ancestry, including paths leaving
  and reentering the district. Ordering invariance is proved for the actual
  observable district factors, including the compact-row bridge. No new
  manuscript defect was found in this step. The equality characterization is
  now assembled in `CompactDistrict/EqualityTriviality.lean`: triviality
  quantifies over actual normalized positive globally Markov observed laws;
  it is equivalent to an affine row combination of the exact (N)/(O) matrix,
  including its constants. `GlobalModel/SingleKernel.lean` proves that every
  positive (N)/(O) kernel occurs as such an observable district factor.
  `CompactDistrict/EqualityRank.lean` defines all district equality coefficients
  by constancy on actual response columns and proves the quotient by intrinsic
  graph-trivial coefficients has the paper's rank difference, given checked
  affine-hull equations. It also proves selected spanning equality rows imply
  all equality rows, with a common compatibility column fixing constants.
  No further manuscript defect was found in the equality/rank step. Positive-kernel
  reconstruction is now checked beyond the fixed order: every ancestral
  margin has the Appendix product formula, and the reconstructed law
  satisfies the local equations for every ancestral set and sink. At c-degree
  at most one, the actual induced districts and blankets are proved to match
  the district intersections used in that argument. A direct ancestral
  moral-graph cut proof now establishes all graphical independencies of the
  reconstructed law. The general equivalence of local/global predicates for
  arbitrary laws remains separate and is not used by that proof.
  The geometric facet incidence criterion and coordinate certificate are
  checked from codimension-one ranks. The formerly separate observed-law
  witness is now checked in `CompactDistrict/FacetWitness.lean`: the actual
  positive globally Markov observed law violates the selected nontrivial
  facet, satisfies every H-equality, strictly satisfies the other selected-
  district facets, and satisfies all inequalities of every other district.
  `GlobalModel/SingleKernelPolytope.lean` places those other factors inside
  their actual response polytopes using positive uniform column averages.
  All (N)/(O) equations for the violating factor are derived from its actual
  affine-hull membership; neither the observed law nor its feasibility is
  assumed. No new manuscript defect was found in this assembly. Exact
  numerical H-conversion and geometric certificates for specific examples
  remain separate obligations.
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

HLP now has checked pointwise structural simulations in both directions.
`HiddenGraph.HLP.eval_absorb` reproduces the edge-added model after moving
the source vertex's private input into a chosen shared latent root. The
target reconstructs the source value from its permitted observed and latent
parents; the source's now-unused private input is fixed. The observed and
latent parent inclusions are exactly the two parts of the manuscript's full
parent inclusion. The numeric presentation uses a common topological order
of the edge-added DAG, with `a < b`; no arbitrary reindexing theorem is
claimed. No manuscript defect was found in this pointwise step. The subsequent
`HLPMeasure` and `HLPInputs` chapters derive mechanism/input measurability and
full mutual independence of the regrouped original inputs. The target's
reconstructed source value changes a parent assignment; finiteness of observed
state spaces justifies this measurable selection from the original fixed-parent
mechanisms. No discreteness or finiteness is assumed of original exogenous
spaces. The wrapper input types retain the original measurable spaces and
erase their bookkeeping lifts before mechanism evaluation.
`Completeness.original_model_iff_HLP` now gives the actual original-model
equivalence on the same sample space and probability measure, including
boundary observed distributions. `constraint_valid_iff_HLP` gives the paper's
'same constraints' conclusion for an arbitrary observed-law predicate.
No new manuscript defect was found in this probability transport step.

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

The reverse structural construction is now checked in `StrongFaceReplay` and
`StrongFaceReverse`. Condition 1 supplies the observed C values and all their
parents to every D vertex; Condition 2 supplies every crossing root needed
to check the original C equations. The local consistency checks are proved
identical, so D vertices select the same first accepted candidate from their
common root. The general consistent-replay theorem identifies the resulting
evaluation with an original evaluation using resampled C-local inputs.

There is a probability-proof obligation here that pointwise simulation does
not discharge: the constant trial encoding reproducing an old realization
duplicates old random inputs across C-side roots and the common D root. It
must not be used as an independence-preserving probability transport. The
probability construction needs independent candidate trials, almost-sure success
on supported fibers, and the conditional-replay law, now established below.
Simple disjoint grouping alone does not supply that reverse direction. This is a formalization scope
qualification, not a counterexample to the manuscript's cited splitting rule.

The generic probability foundation is now checked in `Probability/ReplayLaw`
and `ReplayTrials`: the actual first-replay selector is measurable, independent
common-law trials hit a fixed positive measurable acceptance set almost surely,
and their selected candidate has exactly the original law conditioned on that
set. An explicit infinite-product probability measure supplies such trials on
arbitrary measurable candidate spaces, without a standard-Borel restriction.
This resolves the fixed-set conditional-replay obligation. `ReplayContext` and
`ReplayContextLaw` now prove joint selector measurability and the full joint
law with an independent random context, allowing null unsupported fibers.
Attaching the context to every trial is used only for the measurability proof;
those context-tagged pairs are not asserted to be independent. The probability
proof fixes the context and then integrates the conditional law using the
product measure. It retains the dependence of the selected candidate on its
context and proves the context marginal unchanged. The extension to any
independent context/stream coupling explicitly checks both input laws.

For the graph itself, `StrongFaceFibers` now identifies both the global and
each D-local acceptance predicate with preservation of the observed boundary
C union Pa(C) under resampling. The C sets may overlap and need not be
ancestral. Condition 1 puts the boundary strictly before every D vertex;
the proof preserves evaluations below the least D vertex. It does not claim
preservation of a prefix containing earlier D vertices, whose outputs can
change after resampling. This is a proof-construction detail, not a defect
in the manuscript's stated conditions.

`StrongFaceInputs` now derives independence of the external and C-local
blocks from full original mutual independence. Selected roots, roots confined
to C and private inputs at C belong to the local block; all other inputs are
external. Fixed constants fill unused coordinates, without duplicating random
inputs. `Probability/ReplaySupport` proves positive observation-fiber mass
almost surely for independent resampling with a countable-valued observation.
`StrongFaceSupport` instantiates this with the actual boundary and also proves
joint acceptance measurability from ordinary joint measurability of the
original local mechanisms. This permits countable observed state spaces and
arbitrary measurable exogenous spaces, including the paper's finite observed
case; no strictly positive observed-law hypothesis is added.

The actual independent-stream sampler therefore succeeds and accepts almost
surely, and its complete context/selected-candidate joint conditional law is
checked without a separate supported-fiber positivity premise.

`StrongFaceMeasurability` now also proves joint measurability of the actual
local acceptance checker on every permitted parent/root argument, rather than
only on arguments coming from original evaluations. Inconsistent parent
assignments and no-hit streams are included. The actual split selector,
mechanisms and evaluation are therefore measurable. `StrongFaceCoupling`
defines and proves measurable the concrete input encoding that puts the trial
stream at the common D root and retains the other original root/private
coordinates, and its actual split evaluation. These statements require no
probability or positive-fiber premise.

The three probability obligations are now checked. `StrongFaceAlignment`
proves that the split and original boundary evaluations agree for every
stream, identifying the actual acceptance contexts without a probability
premise. `StrongFaceIndependence` proves full mutual independence of the
complete encoded root/private family, including the entire shared stream.
Checked coordinate identities connect this family to the structural encoding;
independence of the selected candidate from its context is never asserted.

`Probability/ReplayInvariance` proves that averaging finite boundary-fiber
conditional laws recovers the original local law at every fixed external
input. The finite law of total probability handles zero-mass boundary fibers.
`StrongFaceLaw` integrates over the independently grouped external/local law
to preserve the entire original input law, then uses almost-sure success and
boundary alignment to prove equality of the actual split and original full
observed distributions. Observed states are finite, as in the manuscript;
root/private state spaces remain arbitrary measurable spaces, with no
standard-Borel or strictly positive observed-law assumption.

The bundled A1 probability-model equivalence is now checked in
`Completeness/StrongFaceSplitting`. `RootProbabilityModel` records arbitrary
measurable sample, root and private spaces, full original mutual independence
and jointly measurable permitted-parent mechanisms. Its observed measure is
proved to be a probability measure. Passing to the native joint input law
derives both its independence and observed-law identity from those fields.
The common universe parameter is bookkeeping, following the existing
`HiddenGraph.ProbabilityModel`; ordinary finite, real and product spaces
are allowed.

For the easy split-to-original direction, `StrongFaceBundling` proves joint
measurability and full input independence by grouping the common D input
with exactly one selected anchor root; nonanchor common components are fixed
constants. The source sample space is retained. The reverse transport builds
a literal split model on the derived input law times the independent stream
law, with measurable native input maps and all independence fields proved.
`original_model_iff_strongFaceSplitting` proves equality of the observational
marginal-model classes, and `constraint_valid_iff_strongFaceSplitting` proves
the paper's same-constraints conclusion for every observed-law predicate.
This completes the observational proposition for finite observed states,
including zero probabilities and arbitrary measurable exogenous/sample
spaces, without A2, a c-degree restriction, strict positivity or standard-Borel
assumptions. No new manuscript defect was found during the assembly.

The chosen root family in Strong Face Splitting must also be nonempty
(`k ≥ 1`). The instruction to choose roots with a common child suggests this
intention. If an empty family were admitted, the two numbered conditions
would be vacuous while the transformation could add a common cause to
previously independent observed nodes. The formal construction therefore
requires a selected root as an anchor. Making `k ≥ 1` explicit would remove
this boundary ambiguity.

## 9. Graphical-separation specification

The global predicate now uses ancestral moral separation in the original
hidden DAG, including explicit latent roots. This is the graphical
construction described as an alternative d-separation test in Section 2.1,
equation (3), of [Pearl and Dechter, *Identifying Independencies in Causal
Graphs with Feedback*](https://ics.uci.edu/~dechter/publications/indep-causal-graph-feedback.pdf).
The citation records the semantic convention; no external theorem from that
paper is imported as a Lean proof premise.

The checked `moralVertex_ancestral_iff` theorem identifies retained vertices
with ancestors in the actual original directed graph. The cut/path bridge
and probability factorization are proved in Lean. The collider example
separately checks that its child is omitted before conditioning and retained
when conditioned on, activating the moral co-parent connection.

A distinct active-trail definition and its equivalence with this chosen
specification have not been formalized. Nor does the construction theorem
claim a local/global equivalence for every arbitrary observed law. The
global-to-local direction has now been proved, including the exact cumulative
conditioning-set identity, and strengthens both completeness statements.
The arbitrary-law reverse direction remains unproved. Global graphical
sufficiency was proved directly for the reconstructed kernels, and
canonicalization proves graphical necessity for actual original models at
c-degree at most one, including boundary observations. These are scope
qualifications, not newly identified manuscript defects.

## 10. Inequality-structure proof: intermediate vertices and treatment A

In the appendix proof of `prop:ineqstructure`, type (i), the path is written
as W→Z₁→…→Zᵣ→A. The description of the target t then says that members on the
path equal ζ. Read literally this includes A. The next sentence specifies
the target triple as (ζ,0,ζ), and the parent-of-B argument also requires A=0.

The intended construction is clear from that triple: only the intermediate
vertices Z₁,…,Zᵣ copy ζ, A is fixed to zero, and B equals ζ. Suggested wording
is “the intermediate vertices Z₁,…,Zᵣ equal ζ, A=0, every other member except
B is zero, and B=ζ.” The profile descriptions likewise override A separately
after copying the intermediate path.

This is a wording ambiguity in the target definition, rather than a
counterexample to the intended argument. The Lean path includes its endpoint,
and `InstrumentalWitness.intermediates` erases A explicitly. The exclusion
obstruction and profile-dependence step are checked. The three lifted profiles
and their actual evaluations are now constructed in `InstrumentalProfiles`;
`InstrumentalAffine` proves the full-row identity t=a+b−c, zero/one target
entries, normalized input blocks and affine-hull membership. A is explicitly
zero in that target, and only intermediate path members copy ζ. This follows
the intended triple and parent-of-B argument. `InstrumentalNonmembership` now
also checks the two distinct W input assignments and proves that their target
blocks cannot be produced by one profile. `Polytope/ZeroOne` supplies the
checked zero/one mixture-to-column implication, so the full target lies outside
the convex district polytope. The normalized affine/nonmembership witness is
assembled as `instrumental_affine_witness`. `LevelChoices` now derives the
reference levels from the manuscript's cardinality assumptions, and
`HiddenGraph/InstrumentalInequalities` assembles the actual graph-level
nontrivial H-row using the existing simplex/equality-set definition of
triviality. `Completeness/InstrumentalStructure` also gives the strictly
positive globally Markov observed-law witness under the general facet theorem's
checked affine-hull and proper/distinct facet data. These are explicit
certificate inputs, as elsewhere in the development; the numerical H-conversion
has not been silently assumed. No additional manuscript issue arose. The
manuscript sources are unchanged.

Bell-branch continuation: the full lifted PR-box construction, CHSH
nonmembership and cardinality-derived actual graph nontrivial H-row are
now assembled in `CompactDistrict/BellNonmembership` and
`HiddenGraph/BellInequalities`. `Completeness/BellStructure` also supplies
the positive globally Markov observed-law witness with the same explicit
checked H, affine-hull and proper/distinct facet inputs as the instrumental
branch. No additional manuscript defect arose from this assembly. Concrete
numerical H-conversion certificates remain a separate task; sources are
unchanged.

Appendix B certificate audit: the literal B, H_i, H_e and right-hand-side
entries agree between the LaTeX, the Lean transcription and the stored
`01-iv.R` output. The printed (X,Y,Z) coordinate table is mapped explicitly
to the semantic (Z,X,Y) row type, and rcdd's coefficient sign convention is
accounted for. Lean checks all B entries against actual response profiles
and proves every printed H row necessary for all their simplex mixtures.
No discrepancy was found. Reverse H sufficiency and concrete facet
certificates remain open; the manuscript and R sources are unchanged.

Appendix B reverse-inclusion continuation: `Examples/InstrumentalHRep`
now reconstructs simplex response weights from every feasible printed H
vector, including boundary points, and bundles exact `printedHRep` data.
`Examples/InstrumentalExact` transports this result to the original semantic
IV coordinates and bundles `semanticHRep`. The generated symbolic certificate
is fully checked by Lean and assumes no R/cdd correctness. No discrepancy
or new manuscript defect arose. Concrete affine-hull/facet certificates and
subsequent numerical examples remain separate; sources are unchanged.

Appendix B affine-hull continuation: `Examples/InstrumentalHull` now proves
that the two printed normalizations describe the complete affine hull,
including signed vectors. Seven selected actual response columns give an
explicit affine basis, and the checked direction dimension is six. No
additional equality constraint or manuscript discrepancy appeared. The
individual facet certificates and their classification remain separate;
sources are unchanged.

Appendix B facet continuation: exact integer left inverses certify six
independent incident response columns for each of the twelve H inequalities.
Together with the six-dimensional full hull and strict off-plane columns,
Lean derives incident-hull dimension five and properness for every row.
Checked pairwise column witnesses distinguish all twelve facet planes.
No numerical rank assumption or new manuscript discrepancy arose. The
eight/four nonnegativity/nontrivial classification remains separate;
manuscript and R sources are unchanged.

Appendix B classification continuation: `Examples/InstrumentalClassification`
now proves the stated eight/four split. Rows 1,4,7,8,9,10,11,12 are exactly
probability-coordinate nonnegativity on the normalized affine hull, with
explicit equality-residual identities; only rows 8 and 10 use a residual.
For rows 2,3,5,6 every coordinate is positive at a checked incident column,
and the general geometric criterion proves nontriviality. Numbering here is
one-based as in the manuscript. No discrepancy with the printed statement
or stored R classification was found; sources remain unchanged.
