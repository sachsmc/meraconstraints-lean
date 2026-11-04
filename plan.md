# Formalization status and remaining work

Specification: `sources/manuscript/main-revised.tex` and `appendix.tex`.
Use manuscript labels as identifiers: proposition numbers can change.

## Foundations implemented and kernel-verified

- Adapt the finite probability, topologically ordered DAG, SCM evaluation and
  canonical response-function machinery from `causaloptim-lean`.
- Model a district with separate internal/external parent sets; evaluate its
  profiles uniquely; reduce a shared latent input to a finite profile.
- Construct its binary compatibility matrix and prove the kernel is `Br`,
  with every input block normalized and nonnegative.
- Prove external-parent dependence for closed-in-district margins; these include
  equations (O) for fully closed sets and possible Verma constraints otherwise.
- Establish finite-mixture inequality certificates and partial-row completion.
- Identify simplex images with convex hulls, allowing duplicate columns.
- Supply the nonnegativity-modulo-equalities certificate implication.
- Work a binary instrumental-variable inequality directly from response profiles.
- Prove binary CHSH and separate the normalized PR box from the Bell polytope.

Validation on 2026-11-02: `lake build` passed, the source scan found no proof
placeholders, and `lake env lean MeraConstraints/Test/Smoke.lean` passed with
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Next milestones implemented in the parallel continuation

Integrated validation on 2026-11-02: `lake build` passed (1,692 jobs);
all 60 declarations in the expanded smoke check used only the standard
axioms listed above. The source placeholder scan also passed.

- Full finite hidden graph with A1/A2, bipartite districts, c-degree and its
  graph maximum; prove degree-zero districts are singletons and degree-one
  components are stars around one actual latent root.
- Parent-restricted SCMs with arbitrary latent input types and explicit private
  disturbances; pointwise finite response reduction and intervention preservation.
- Finite event/marginal/conditional probabilities, strict positivity, supported
  conditioning replacement, ordered assignment chain rule, event pullback and
  fiber averaging. No graph property is smuggled into these probability identities.
- Mutually independent families of district profiles; structural global and
  prefix-event factorization, off-block cancellation, and identification of
  global-predecessor district products by telescoping.
- The exact revised cumulative conditioning sets, their precedence and nesting
  properties, reconstruction under explicit ordered Markov equations, and
  realization using checked H-representations.
- Derive the ordered Markov equations for generated canonical finite-profile
  laws using prefix-factor dependence and finite fiber averaging. Combine this
  with reconstruction into an exact canonical finite-source/H-constraint equivalence.
- A bijection between actual latent/private singleton sources and districts at
  c-degree ≤ 1; an independence-preserving original-source realization. This
  prevents accidentally allowing correlated distinct roots at higher c-degree.
- The finite geometric perturbation used in the facet nontriviality proof,
  including positivity of facet averages and exact preservation of affine rows.
- Full observed ancestry, distinct full/internal district closure definitions,
  closure of district prefixes, and the checked Verma-graph counterexample to
  identifying those two closure notions.
- Exact PR-box affine weights and the binary affine-but-incompatible witness;
  a checked parity counterexample documenting why pairwise independence is insufficient.

The initial `District.Closed` correspondence was corrected to
`District.ClosedInDistrict`: the former name conflated two notions the manuscript
explicitly distinguishes. The inherited prose now distinguishes canonical
partitioning from the source causaloptim paper's proposition numbering.
See `manuscript-issues.md`; the LaTeX sources have not been changed.

## Original-model and compact-row continuation

The author confirmed full mutual independence as the intended assumption;
issue 1 in the audit is resolved by that clarification.

Integrated validation on 2026-11-03: `lake build` passed, the
source placeholder scan passed, and all 279 expanded smoke checks used only
`propext`, `Classical.choice` and `Quot.sound` (or a subset).

- `IndependentMap` and `IndependentGroupingMeasure` prove disjoint grouping
  and local mapping preserve mutual independence, for finite vectors and
  arbitrary measurable original state spaces respectively.
- `Canonicalization` derives district laws from given original finite inputs,
  including a public law on native latent/private types. `Measurability` and
  `MeasureCanonicalization` extend this to arbitrary probability spaces using
  ordinary per-node structural-mechanism measurability.
- `CompactDistrict` proves explicit compact evaluation, the row projection
  identity and its surjectivity, and exact V/H transport. `Observable` proves
  that the cumulative conditioning product depends only on those compact rows.
- `Identification/OriginalMeasure` proves the original model's observable
  product is `Br` (`prop:ident`) and equals an actual external-parent surgical
  intervention (`causalprop`). These identities allow higher c-degree; they
  do not assert unrestricted-profile sufficiency there.
- `MeasureOfLaw` and `MeasureRealization` construct actual independent-input
  probability spaces for profile witnesses. `ProbabilityModel` bundles the
  original SCM and probability data without assuming any observed constraint.
  `Completeness.original_model_iff_compact_HRep` proves the positive-law
  original marginal-model equivalence for c-degree at most one, with derived
  ordered conditional independencies and checked compact H-systems.
- `EqualityConstraints` proves the complete positive-affine-consequence /
  row-combination bridge, including right-hand sides. Its rank chapter proves
  the actual stacked-matrix rank difference as a quotient dimension and the
  consistent selected-row span implication. Graph-triviality is not assumed
  proved by these linear-algebra results.
- `BoundaryMarkov` removes observed positivity from the ordered cross-product
  equations. `BoundaryObservation` proves supported cumulative ratios,
  zero-row soundness despite later undefined factors, and all-defined-row
  soundness. `BoundaryCompletion` now proves the exact ordered known/free
  classification and converse reconstruction. `Completeness.Boundary` lifts
  the full boundary equivalence to actual original measurable models.

- `HiddenGraph.Merging` constructs the merged graph, proves c-degree at most
  one and preservation of the observed district partition. `Completeness.Merging`
  embeds every actual original model into an actual merged model; no positivity
  or finite original latent spaces are required.
- `CompactDistrict.OrderingConstraints` constructs actual (N)/(O) matrices,
  using full observed ancestry, and proves column/mixture validity, positive
  uniform feasibility and the positive affine-consequence characterization.
- `FacetCriterion` and its span/rank chapters derive the positive coordinate
  certificate and exact geometric incidence criterion from proper distinct
  codimension-one facet data, plus a positive kernel violating only one row.
- `CompactDistrict.FacetCriterion` proves coverage/nonnegativity and affine-hull
  normalization of the actual matrix. It establishes the inequality-triviality
  incidence iff on the manuscript's cross-product simplex domain. Its incidence
  chapter proves the exact `I Bᵀ` positivity test.

## Sequential continuation: positive-kernel reconstruction

**Completed mathematical checkpoint:** fixed-order reconstruction from arbitrary
strictly positive compact district kernels satisfying the actual (N)/(O)
matrices. No response-profile feasibility or candidate joint normalization is
assumed. No subagents were used in this continuation.

- `Probability.PrefixPartition.mass_prefix_eq_sum_next` partitions a prefix by
  the next value for arbitrary real masses, with no positivity hypothesis.
- `KernelReconstruction.sum_prefixJoint_next` proves reverse elimination.
  `joint_prefix_mass` identifies every global-prefix probability with the
  product of district prefix margins; `joint_sum_eq_one` proves normalization
  even for signed kernels. Positive kernels give `joint_mem_stdSimplex`.
- `KernelIdentification.joint_orderedMarkov` derives the fixed-order equations
  from (O), cancellation and finite averaging. `joint_observableFactor`
  telescopes the ratios to recover exactly each supplied compact kernel.
  `reconstruct_positive_kernels` packages the positive law, normalization,
  ordered equations and recovery in one theorem.
- The previous independent-profile conditioning proof now uses the general
  `prefixConditional_eq_conditioning_of_congr` averaging theorem; its public
  statement is retained and remains checked.

This completes the fixed-order construction, not the entire graph-specific
nontriviality proposition. The following checkpoint extends the margin identity
and local equations to **all observed ancestral sets**. One fixed-order
predicate must not be substituted for that stronger statement.

Verification of this checkpoint: the final integrated `lake build` passed
(2,337 jobs), all 134 smoke declarations used only `propext`,
`Classical.choice` and `Quot.sound` (or a subset), and the source placeholder
scan passed. The final changed modules built without warnings. No new
manuscript flaw was identified; the all-ancestral/global-Markov boundary above
was remaining formalization work at this checkpoint.

## Sequential continuation: ancestral margins and induced local equations

**Completed on 2026-11-03, without subagents.**

- `HiddenGraph.AncestralSets` defines observed ancestral sets using full
  directed ancestry, proves that district intersections are fully closed,
  and checks sink removal and the ancestral extensions `A ∪ prefix(k)`.
- `AncestralKernels.joint_ancestral_mass` proves Appendix equation
  `eqn:ancmargin` for every observed ancestral set. The proof uses the literal
  margins of the supplied compact kernels, the actual (N)/(O) equations and
  reverse sink elimination. It is valid for signed kernels; positivity and
  profile/polytope feasibility are not inputs.
- `Probability.AssignmentConditioning` proves finite averaging over assignment
  fibers, with explicit conditional-independence equations. `AncestralMarkov`
  derives each ancestral-sink conditional as its own district-margin ratio,
  reduces it to the retained district blanket and proves the local equation.
- `HiddenGraph.retainedDistrictConnected_iff` proves, under c-degree at most
  one, that actual latent-incidence connectivity after retaining observed
  vertices equals original district membership on those vertices.
  `inducedAncestralBlanket_eq` identifies the actual induced blanket; this
  correspondence is proved rather than assumed for a general graph.
- `KernelReconstruction.joint_ancestralLocalMarkov` packages the local
  equations for **every ancestral set and every sink**, using that actual
  induced blanket. Positivity is used for conditional ratios and averaging.

Validation: the integrated `lake build` passed (2,343 jobs); all 148 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset); the source placeholder scan passed. The new modules built without
warnings. No new manuscript defect was identified.

The following checkpoint addresses graphical sufficiency by a direct proof
from ancestral factorization. It does not assume a general local/global
equivalence for arbitrary laws, nor build it into either predicate.

## Sequential continuation: global graphical independencies

**Completed on 2026-11-03, without subagents.**

- `HiddenGraph.MoralSeparation` defines separation by absence of an undirected
  walk in the original hidden DAG's ancestral moral graph after deleting `Z`.
  The graph explicitly includes latent roots. `moralVertex_ancestral_iff`
  proves its retained vertices are exactly ancestors in the full original
  directed graph, not an assumed observed district clique.
- `moralSeparated_cut` constructs a two-sided cut from absence of a walk;
  `moralSeparated_of_cut` proves the converse certificate direction. Under
  c-degree at most one, `kernelFamily_same_side` proves no district-kernel
  family straddles such a cut outside `Z`, using its actual root or singleton.
- `Probability.FactorizedFibers` and `CutFactorization` prove conditional
  independence from factorized joint assignment fibers. `CoordinateCI`
  quantifies over all observed assignments and uses literal event masses.
  Neither normalization, positivity nor an independence conclusion is assumed
  by these algebraic lemmas.
- `MoralMarkov.joint_moralGlobalMarkov` proves all independencies specified
  by that graph criterion for the reconstructed law. Its graph-cut proof
  groups the already checked ancestral district factors into `F(L,Z) H(R,Z)`.
  `reconstruct_positive_kernels_global` packages a positive normalized law,
  all these graphical independencies and exact recovery of every supplied
  observable district factor. The separation/independence predicates contain
  no assumed kernel feasibility or local Markov conclusion.
- `Completeness.probabilityModel_moralGlobalMarkov` transports global
  graphical necessity to actual original measurable SCMs via canonicalization.
  It allows arbitrary original latent inputs and zero observed probabilities.
- `Examples.MoralCollider` independently verifies `0 → 2 ← 1`: the roots
  are separated without conditioning, and conditioning on the child opens
  the connection. This checks ancestor retention and the co-parent edge rule.

Validation: the integrated `lake build` passed (2,349 jobs); all 166 smoke
declarations, including multiline dependency reports, used only `propext`,
`Classical.choice` and `Quot.sound` (or a subset); the source placeholder scan
passed. The final modules built without warnings. No new manuscript defect
was identified.

Specification boundary: this formalization takes the ancestral-moral criterion
as its definition of graphical separation. It does not separately define
active trails or prove the equivalence of two trail/separation presentations.
The direct global sufficiency result also does not claim a general equivalence
between arbitrary laws satisfying ancestral local equations and global Markov.

**Next milestone:** prove (N)/(O) necessity for an arbitrary strictly positive
law satisfying the graph independencies, including the ordering-invariance
argument. Then assemble graph-trivial equality completeness and the positive
observed-law facet witness, using the now-checked global reconstruction.

## Sequential continuation: graphical completeness

**Completed on 2026-11-03, without subagents.** This closes the arbitrary-law
global-to-local prerequisite for the ordering argument and strengthens the
main completeness statements themselves.

- `HiddenGraph.LocalSeparation.ancestral_sink_blanket_separated` proves the
  actual moral-graph separation of an ancestral sink from the vertices outside
  its original district blanket. The proof cuts original districts, including
  latent roots, and checks parent-child and co-parent edges. It does not take
  a local independence equation as a premise.
- `Probability.CoordinateJoin` joins the conditioning coordinates to an
  assigned event without changing its conditional-independence cross-product
  equation. No support or positivity premise is used.
- `HiddenGraph.observedUpto_blanket` proves the literal identity between the
  global-prefix blanket and the manuscript's cumulative `C_i`, including
  external parents of every member up to and including the current vertex.
- `GlobalToLocal.moralGlobalMarkov_ancestral_equation` proves the ancestral
  local equations for an arbitrary globally Markov law. At degree at most
  one the induced-blanket local predicate follows as well.
  `moralGlobalMarkov_orderedMarkov` derives the exact fixed-order equations
  used in reconstruction, without positivity or a degree bound.
- `Completeness.original_model_iff_global_compact_HRep` proves the positive
  original marginal-model equivalence using **global graphical independencies
  plus compact H-constraints**, with no extra ordered-Markov assumption.
- `Completeness.original_model_iff_global_boundary_compact_HCompletion`
  proves the analogous equivalence with zero probabilities and the exact
  first-zero/first-undefined compact completion rule. Both theorems quantify
  over actual original measurable probability models and require c-degree
  at most one. H-representation exactness remains a checked input.

Validation: the final integrated `lake build` passed (2,353 jobs); all 176
smoke declarations used only `propext`, `Classical.choice` and `Quot.sound`
(or a subset); the source placeholder scan passed. The final new modules
built without warnings. No new manuscript defect was identified.

This completes the graphical formulation of `prop:complete` and the boundary
remark under the ancestral-moral specification. It does **not** prove the
general arbitrary-law local-to-global converse or an active-trail equivalence.
Neither is assumed by the completeness proofs.

The following checkpoint uses that global-to-local theorem to handle all
valid topological orders. Necessity for all closed district subsets remains
separate; fixed-prefix equations alone must not be reported as all of (O).

## Sequential continuation: ordering invariance

**Completed on 2026-11-03, without subagents.**

- `HiddenGraph.EliminationOrder.Valid` checks a literal list of observed
  sink removals, ending with the empty set. `valid_erase` proves deletion of
  a vertex leaves a valid order on the remaining vertices.
- `EliminationOrder.products_eq` proves that explicit two-sink multiplicative
  diamonds imply equality for every two valid orders on an ancestral set.
  Its proof moves a chosen sink through another order one removal at a time;
  order invariance itself is not a hypothesis.
- `OrderingInvariance.chainWeight_diamonds` proves those diamonds for the
  actual district conditional weights of an arbitrary positive globally
  Markov law. Two selected-district vertices commute by the ordinary chain
  rule. If exactly one is in the district, the other sink can be dropped
  from its conditioning event, by global-to-local and finite averaging.
- `blanketProduct_order_invariant` replaces the chain conditionals by the
  proved ancestral blanket conditionals and establishes invariance for every
  valid reverse topological order. In forward order these are the paper's
  earlier district members plus cumulative external observed parents.
- `HiddenGraph.CanonicalOrder` constructs the actual numeric order, proves
  it is valid, and equates its schedule product to a finite prefix product.
  `canonicalProduct_eq_observableFactor` identifies it literally with the
  existing `Reconstruction.observableFactor` used in the manuscript bridges.
- `orderProduct_eq_observableFactor` and
  `orderProduct_eq_compact_observableFactor` therefore identify **every valid
  order's product with the existing full and compact observable factors**.
  No original-SCM representation or district polytope feasibility is assumed
  of the observed law. The result uses positivity and the graphical global
  predicate; it does not need a c-degree bound.

Validation: the final integrated `lake build` passed (2,358 jobs); all 188
smoke declarations used only `propext`, `Classical.choice` and `Quot.sound`
(or a subset); the source placeholder scan passed. The final changed modules
built without warnings. No new manuscript defect was identified.

The summation/closed-subset step was a separate obligation after ordering
invariance. It is completed in the following sequential continuation.

## Sequential continuation: necessity of all (N)/(O) equations

Working solo, completed normalization and every fully closed district subset
equation for arbitrary strictly positive globally Markov observed laws.

- `HiddenGraph.SelectedOrder` constructs a valid elimination order for every
  retained vertex set by removing its largest remaining topological label.
- `GlobalModel.AncestralProducts` defines the retained district conditional
  product, proves its exact member/external-parent dependence, and derives
  sink-removal recursion from ordering invariance. A removed sink cannot
  affect the remaining product; summing its conditional gives one.
- `GlobalModel.ObservableMargins.observable_setMargin_eq_ancestralProduct`
  identifies the **literal compact district margin** on every ancestral set
  with that retained product. Reverse elimination through `A ∪ prefix(k)`
  reaches arbitrary ancestral sets, not just the original numeric prefixes.
- `fullClosed_ancestor_intersection` proves that the full observed ancestors
  of a fully closed district subset intersect the district in exactly that
  subset. Directed paths may leave the district and return. Consequently
  `observable_ordering` equates its actual margins for all external inputs
  agreeing on its own parent set `E(S)`. The empty ancestral set gives
  `observable_normalization`.
- `GlobalModel.OrderingInvariance.observable_constraints` packages these
  results as feasibility of the existing exact stacked compact `(N;O)` matrix.
  Neither a hidden-variable realization, response-profile feasibility nor
  any (N)/(O) equations are assumed of the observed law. No c-degree bound
  is needed. This completes the necessity/triviality direction of Appendix
  `prop:nontrivial`, Step 1; the row-span iff remains a separate milestone.

Validation: the integrated `lake build` passed (2,362 jobs). All 200 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset); the source placeholder scan passed. The new modules built without
warnings, and `git diff --check` reported no whitespace errors.
No new manuscript defect was identified. The existing distinction between
full closure and internal-parent closure is preserved explicitly.

The equality characterization and rank count were the next separate
milestone, completed in the following sequential continuation.

## Sequential continuation: graph-trivial equality characterization and rank

Working solo, assembled Proposition `prop:nontrivial` (i) from the checked
graphical reconstruction, (N)/(O) necessity and affine-consequence results.

- `GlobalModel.SingleKernel.realize_single_positive_kernel` inserts an arbitrary
  positive (N)/(O) kernel at one district and uniform output kernels at the
  others, then constructs a normalized positive globally Markov observed law
  whose actual compact observable factor is the supplied kernel.
  `positive_kernel_iff_graphical_image` proves the exact domain equivalence.
  This selected-kernel result does not yet package all constraints of the
  other districts; that stronger packaging belongs to the facet-witness step.
- `CompactDistrict.EqualityTriviality.EqualityTrivial` follows the manuscript's
  definition: quantify over normalized strictly positive observed laws and
  the actual global graphical predicate. It contains no kernel-feasibility
  or row-span field. `equalityTrivial_iff_rowCombination` proves that such an
  equation holds exactly when its coefficients **and constant** are a common
  linear combination of the concrete (N)/(O) equations, at c-degree ≤ 1.
- `graphTrivialSpace` is defined intrinsically using those observed laws and
  proved equal to the actual (N)/(O) row space. `districtEqualitySpace` is
  independently defined by equations constant on every compatibility column;
  `equation_of_columns` extends them to every response-profile mixture.
- Given checked equations for the actual district affine hull,
  `CompactDistrict.nontrivialEquality_rank_count` proves that the dimension of
  the intrinsic district equality space modulo the intrinsic graph-trivial
  space is exactly `rank (N;O;H_e) - rank (N;O)`. The theorem proves the semantic
  identification of both spaces before applying the generic dimension result.
- `selected_equalities_imply_all` proves that selected H equality rows which,
  together with (N)/(O), span the full stacked row space imply every district
  equality on globally Markov observed laws. An actual compatibility column
  fixes the affine constants. Any basis extension has the required spanning
  property; numerical row independence is not assumed or computed here.

Validation: the integrated `lake build` passed (2,365 jobs). All 212 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The final
new modules compiled without warnings.
No new manuscript defect was identified. Affine-hull exactness remains a
proof-carrying input, matching the proposition's stated H-representation
assumption; external numerical conversions are not certified by this step.

The observed-law facet witness was the next separate milestone and is
completed in the following sequential continuation.

## Sequential continuation: a positive observed-law witness for each nontrivial facet

Working solo, completed Proposition `prop:nontrivial` (ii)'s final assertion.

- `CompactDistrict.PositiveReference` constructs the uniform average of the
  actual response columns, explicitly as a matrix image of the uniform
  profile simplex law. Constant-output profiles cover every row, proving
  strict positivity. The reference point lies in the actual district polytope
  and satisfies its (N)/(O) equations.
- `GlobalModel.SingleKernelPolytope.realize_single_kernel_other_polytopes`
  strengthens the earlier selected-kernel realization: the selected positive
  (N)/(O) kernel is recovered exactly, while **every other** district factor
  belongs to its actual response polytope. This derives all their checked
  H-system constraints, rather than supplying other-district feasibility as
  an observed-law premise.
- `CompactDistrict.positive_facet_kernel` derives facet spans and separation
  from genuine codimension-one incidence data, then uses the checked positive
  perturbation. Its positive kernel lies in the actual affine hull, violates
  the selected nontrivial facet and strictly satisfies all other inequalities.
  All (N)/(O) equations are derived on that hull from the actual columns.
- `CompactDistrict.observed_law_violating_only_facet` constructs a normalized
  strictly positive observed law satisfying the full global graphical Markov
  predicate. It violates the selected inequality, satisfies every H-equality
  in every district, strictly satisfies the other selected-district facets,
  and satisfies every inequality of every other district. Column validity is
  derived from the supplied exact H-representation, not assumed separately.

The existing incidence iff and coordinate-plus-equality certificate, together
with this witness, now cover part (ii). Genuine distinct proper facets and
affine-hull exactness remain checked geometric inputs, exactly as stipulated
in the proposition; actual external R/cdd output is not certified by this step.

Validation: the integrated `lake build` passed (2,368 jobs). All 219 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The new
modules compiled without warnings.
No new manuscript defect was identified. Full closure and all graphical
independencies retain their previously documented semantic specifications.

The HLP reverse pointwise simulation was the next separate milestone and
is completed in the following sequential continuation.

## Sequential continuation: HLP reverse pointwise evaluation preservation

Working solo, completed the reverse structural direction of `prop:hlp` for
the existing explicit absorption model.

- `HiddenGraph.HLPEvaluation.reconstructed_a_eq` proves that the value
  reconstructed at the target vertex is the edge-added source model's actual
  value at the source vertex. Its permitted observed parent arguments agree
  by the manuscript's observed-parent inclusion; the selected root carries
  exactly the original source private disturbance.
- `HiddenGraph.HLP.eval_absorb` checks the original recursive structural
  equations at the source, target and every other observed vertex, then uses
  uniqueness to prove equality of the **complete observed assignments** for
  every original latent/private input realization. The target has access to
  every source latent parent by the manuscript's latent-parent inclusion.
  Unused extension values in `parentWitness` do not affect evaluation.
- Together with `eval_ignoreEdge`, this gives pointwise structural simulation
  in both directions, with arbitrary possibly infinite input types and no
  c-degree, positivity or probability hypothesis. The common numeric labels
  are a topological order of the edge-added DAG, so the added edge obeys
  `a < b`. An arbitrary graph-reindexing theorem is not part of this step.

Validation: the integrated `lake build` passed (2,369 jobs). All 221 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The final
HLP modules compiled without warnings.
No new manuscript defect was identified. Full probabilistic observational
equivalence is not claimed from the pointwise result alone.

The HLP probability transport was the next separate milestone, completed in
the following sequential continuation.

## Sequential continuation: HLP equivalence of original probability models

Working solo, completed the probability transport for `prop:hlp` without
changing the original sample space or probability measure.

- `HiddenGraph.HLPMeasure.liftedAbsorb` uses the original indexed measurable
  input spaces as native input types. The wrapper erases bookkeeping lifts
  before calling the checked absorption mechanisms, and its evaluation is
  identified with that earlier model. `liftedAbsorb_mechanisms` derives
  transformed mechanism measurability. At the target, a finite-valued
  measurable source value selects among the original fixed-parent mechanisms;
  no joint-measurability premise is added to the original model bundle.
- `HiddenGraph.HLPInputs.absorptionBlock` groups the source private input
  with the chosen common root, leaving every other original input in its own
  group. Local measurable maps supply the transformed inputs; the now-unused
  private input and all unused extra root coordinates are constants.
  `absorptionEncode_independent` derives **full mutual independence** by the
  checked disjoint-grouping theorem. No nonconstant original input is copied
  between independent groups.
- `eval_absorptionEncode` identifies the native inputs with the already
  checked `absorbLatents` / `absorbPrivate` encoding and proves exact observed
  evaluation equality for every original input realization.
- `Completeness.probabilityModel_ignoreEdge` and `probabilityModel_absorb`
  construct literal original `ProbabilityModel` witnesses in both directions,
  including all measurable-space, mechanism, independent-input and probability
  fields. Their observed-law identities retain the original probability measure.
  `original_model_iff_HLP` equates the two marginal-model classes, and
  `constraint_valid_iff_HLP` equates validity of every observed-law constraint.

Scope: finite observed state spaces with measurable singletons, arbitrary
possibly infinite original latent/private/sample spaces, zero probabilities
allowed, and no c-degree bound or positivity premise. The common numeric
topological presentation of the edge-added graph is retained.

Validation: the integrated `lake build` passed (2,372 jobs). All 231 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The final
new HLP modules compiled without warnings. No subagents were used.
No new manuscript defect was identified in the probability-law correspondence.

The reverse structural Strong Face Splitting construction was the next
separate milestone and is completed in the following sequential continuation.

## Sequential continuation: Strong Face Splitting reverse structural replay

Working solo, constructed an actual reverse `RootSCM` on the A1-only raw
split graph and verified its parent restrictions and evaluation identities.

- `StrongFaceReplay` proves the union of C-sets is disjoint from D, that
  every D vertex observes all C values and their observed parents, and that
  every unselected root crossing out of C is available at every D vertex.
  These are direct uses of the manuscript's disjointness and two coverage
  conditions; overlaps among the C-sets are retained.
- A candidate contains original root/private inputs. A D vertex checks all
  original C equations against its permitted observed/root arguments.
  `localReplayAccept_iff_global` proves every local test is exactly one common
  global predicate. `firstReplay_shared` therefore gives the same first
  accepted candidate to all D vertices. A specified fallback makes the SCM
  total even if no trial succeeds. Root/private input universes may differ;
  lifts on unchanged root values are erased at mechanism calls.
- `StrongFaceReverse.replayModel` retains C-side mechanisms and uses the
  shared candidate at D. `encoded_replay_accepts` proves the original input
  tuple passes the local check. `original_eval_reproduced` proves exact
  complete observed evaluation equality under an explicit constant-trial
  encoding, completing the reverse pointwise direction.
- `replayModel_eval_of_consistent` is stronger than that special encoding:
  for any trial sequence with a consistent candidate, the split evaluation
  equals an original evaluation using the shared replay at selected and
  internal-C roots and at C's private inputs. Other root/private inputs
  remain unchanged. This is checked structural infrastructure for the
  conditional probability construction, not an assumed equivalence of models.

Validation: the integrated `lake build` passed (2,374 jobs). All 244 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The new
structural chapters compiled without warnings. No subagents were used.

**Probability qualification:** the constant pointwise encoding copies random
old inputs into the common replay root and is not independence preserving.
No probability-model equivalence is claimed from it. The remaining reverse
probability argument needs independent trials and a conditional-replay law;
the simpler disjoint-grouping argument used for HLP is insufficient here.
No new counterexample to the manuscript's splitting rule was found. This
remaining proof obligation is flagged in `manuscript-issues.md`.

The independent-trial replay law was the next separate milestone, completed
in the following sequential continuation.

## Sequential continuation: measurable independent conditional replay

Working solo, proved the probability foundation for the exact `firstReplay`
selector already used by the reverse Strong Face Splitting SCM.

- `Probability.ReplaySelection` proves the disjoint first-hit partition and
  the exact preimage formula, including the no-hit fallback. It derives
  selector measurability from measurable trials and a measurable acceptance
  set, with no independence or candidate-space finiteness assumption.
- `Probability.ReplayLaw.firstHit_measure` uses full mutual independence and
  the common trial law to derive the geometric first-hit mass. Summing the
  disjoint cylinders gives the conditional mass of every measurable event.
  `ae_exists_accepted` derives almost-sure success from positive acceptance
  probability; success is not assumed as a premise of the law theorem.
- `firstReplay_map_eq_cond` proves exact equality of probability measures:
  the original probability measure pushed forward through the actual
  selector is `ProbabilityTheory.cond` of the candidate law. The candidate
  state space may be arbitrary, including infinite non-standard-Borel spaces.
- `Probability.ReplayTrials.trialMeasure` explicitly constructs a probability
  space of candidate sequences using Mathlib's infinite product. Its
  coordinates are measurable, mutually independent and have the supplied
  original candidate law. `trials_replay_map_eq_cond` and `trials_ae_success`
  instantiate the generic theorems for this actual sampler, rather than
  assuming an iid stream exists.

Scope: any fixed measurable acceptance set with nonzero original probability;
the no-hit fallback is measurable and lies on a null event. No finite,
countable or standard-Borel condition is imposed on candidate states. The
graph-specific random acceptance context is not replaced by a fixed set in
any claimed model-equivalence theorem.

Validation: the integrated `lake build` passed (3,047 jobs). All 263 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The final
new replay chapters compiled without warnings. No subagents were used.
No new manuscript defect was identified. The additional pinned Mathlib cache
for infinite product measures is a build dependency, not a new proof premise.

The random-context extension was the next separate milestone and is completed
in the following sequential continuation.

## Sequential continuation: jointly measurable random-context replay

Working solo, proved the measurable selector and joint conditional-law identity
for replay with an external random context independent of the candidate stream.

- `Probability.ReplayContext.firstReplay_pair` identifies the actual selector
  after attaching a fixed context to every trial. Applying only the earlier
  **measurability** theorem to these pairs proves `contextReplay_measurable`;
  no independence of context-tagged trials is asserted. The theorem is joint
  in context and stream, includes the no-hit fallback, and composes with
  arbitrary measurable original context/stream maps.
- A jointly measurable acceptance event supplies measurable sections and a
  measurable normalized conditional mass for every joint context/candidate
  event. The context and the explicit infinite-product stream are independent
  under their actual product measure (`context_trial_independent`).
- `context_replay_ae_success` and `context_replay_ae_accept` derive almost-sure
  success and acceptance when the candidate acceptance probability is nonzero
  for almost every context. Positivity is not assumed at null unsupported
  contexts, and success is not a separate premise.
- `context_replay_joint_law` computes the pushforward of the complete pair
  (context, selected candidate) on **every measurable joint event** as the
  integral of its fiberwise conditional mass. This preserves the dependence
  created by conditioning. `context_replay_context_law` separately proves
  that the original context marginal is unchanged, even on the fallback branch.
- `independent_context_replay_map` and `independent_context_replay_joint_law`
  transport the full result to any original probability space with measurable
  independent context and whole-stream maps having the specified input laws.
  Independence and laws of the inputs are explicit; the desired output law
  is derived from them.

Scope: arbitrary context and candidate measurable spaces, with no finiteness,
countability or standard-Borel restrictions. Joint measurability of the
acceptance event and almost-sure positive acceptance fibers remain explicit
generic hypotheses. They have not yet been derived for the graph's own replay
predicate, and no Strong Face Splitting probability equivalence is claimed.

Validation: the integrated `lake build` passed (3,049 jobs). All 279 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The new
contextual replay chapters compiled without warnings. No subagents were used.
No new manuscript defect was identified. The remaining graph-supported-fiber
obligation is recorded explicitly in `manuscript-issues.md`.

The structural boundary-fiber identification is completed in the following
sequential continuation. Positive fiber probability remains separate.

## Sequential continuation: graph-specific boundary-fiber identity

Working solo, completed the structural part of the supported-fiber milestone
for manuscript `prop:strong` in `HiddenGraph.StrongFaceFibers`.

- Defined the actual observed boundary as C union Pa(C), where C is the union
  of all selected C sets, and proved it precedes every D vertex by Condition 1.
- Defined original evaluation, boundary observation and the exact resampled
  inputs used by the existing reverse replay construction.
- Proved by well-founded evaluation that an accepted candidate preserves the
  entire prefix before the least D vertex, hence the boundary. This permits
  overlapping C sets and paths that leave C and re-enter it; no ancestry
  closure is added as a hypothesis.
- Proved the converse from equality of boundary observations using the
  original C mechanism equations. `replayAccept_iff_boundaryFiber` is the
  exact global iff; `localReplayAccept_iff_boundaryFiber` ties every D-local
  permitted-parent checker to that same fiber.

Scope: arbitrary observed and original input types, with no finite-state,
measurability or positivity premise needed for these structural statements.
Almost-sure positive fiber probability under mutually independent original
inputs and graph-specific joint measurability are still unproved. This is
not yet the Strong Face Splitting probability-model equivalence.

Validation: the integrated `lake build` passed (3,050 jobs). All 285 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The new
chapter compiled without warnings. No subagents were used and no new
manuscript defect was identified; the probability obligations remain explicit
in `manuscript-issues.md`.

The supported-fiber probability step and original-context joint acceptance
measurability are completed in the following sequential continuation.

## Sequential continuation: supported measurable graph replay

Working solo, completed the next probability-support milestone for
manuscript `prop:strong`.

- `Probability.ReplaySupport` proves that a countable-valued observation has
  positive-mass fibers almost surely, and derives the independent-resampling
  version by measurable product integration. Input state spaces may be
  arbitrary measurable spaces; no regular conditional distribution is used.
- `HiddenGraph.StrongFaceInputs` identifies the actual C-local and external
  blocks. The local block contains selected roots, other roots confined to C
  and private inputs at C. Disjoint grouping of the original full mutually
  independent family proves `replayBlocks_independent`. Fixed constants fill
  unused coordinates, so no random input is duplicated. Reassembly of these
  blocks is exactly the existing `resampleInputs` construction.
- `HiddenGraph.StrongFaceSupport` proves original evaluation and boundary
  observation measurable directly by DAG induction from ordinary joint
  measurability of the original local mechanisms. The boundary-fiber iff
  gives `replayAcceptanceEvent_measurable` for the actual joint event.
- `replayAcceptance_ae_positive` derives almost-sure positive candidate
  acceptance probability from the original full input independence. Neither
  observed-law positivity nor the desired replay-output independence or law
  is assumed. Countable observed states suffice and include the finite case.
- `replayTrials_ae_success`, `replayTrials_ae_accept` and
  `replayTrials_joint_law` instantiate the explicit independent infinite-product
  stream and its exact context/selected-candidate joint conditional law, now
  with both graph-specific measurability and support premises discharged.

Scope: a law on the actual original root/private candidate tuples, arbitrary
measurable exogenous spaces and countable observed state spaces with measurable
singletons. This does not yet assert the split model's full observed-law
equivalence or measurability of its new local mechanisms.

Validation: the integrated `lake build` passed (3,053 jobs). All 305 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. No
subagents were used, and no new manuscript defect was identified. The remaining
probability-model assembly obligations are recorded in `manuscript-issues.md`.

The split replay mechanism measurability step is addressed in the following
sequential continuation. Observed-law preservation remains separate.

## Sequential continuation: measurable split replay mechanisms

Working solo, completed measurability of the actual reverse model in
manuscript `prop:strong`, on all its graph-permitted mechanism arguments.

- `HiddenGraph.RootMeasurability` supplies a reusable A1-only local mechanism
  measurability predicate and proves joint evaluation measurability by DAG
  induction. It permits the raw split graph's empty and single-child roots.
- `HiddenGraph.StrongFaceMeasurability` equips the actual replay root types
  with their product/ULift measurable spaces, retaining arbitrary measurable
  original root and private input types.
- Proves the parent-completion witness and the three root-input maps
  measurable. Crossing roots in the local checker are precisely the
  permitted arguments supplied by Condition 2.
- Proves `localAcceptanceEvent_measurable` directly on the complete space of
  permitted parent/root arguments and candidates. This strengthens the
  earlier original-evaluation-context event: parent assignments need not be
  consistent with any original evaluation.
- `localFirstReplay_measurable` includes arbitrary trial streams and the
  no-hit fallback. Composition with the original local mechanisms gives
  `replayModel_mechanismsMeasurable` and `replayModel_eval_measurable` for the
  existing split `RootSCM`, without assuming supported fibers or any
  probability law.
- `HiddenGraph.StrongFaceCoupling` defines the concrete original-context/
  trial-stream encoding and proves both it and the actual coupled split
  evaluation measurable. The common D root receives the stream, each other
  root retains its own original coordinate, and private inputs are retained.
  Full independence of this encoded family remains a separate probability
  statement; it is not inferred from measurability.

Scope: countable observed state spaces with measurable singletons, arbitrary
measurable original input types, and ordinary joint measurability of the
original local mechanisms. The statement is joint, rather than only for
fixed observed-parent assignments. It does not yet identify the split
evaluation's observed distribution with the original model's distribution.

Validation: the integrated `lake build` passed (3,056 jobs). All 317 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed; the new
chapters compiled without warnings. No subagents were used and no new
manuscript defect was identified. The boundary-context and law-preservation
obligations are recorded as remaining formalization gaps in
`manuscript-issues.md`.

The next three probability steps are completed in the following sequential pass.

## Sequential continuation: boundary alignment, input independence and law preservation

### Current three-step pass: step 1 completed — boundary alignment

`HiddenGraph.StrongFaceAlignment` compiles with the pinned toolchain. Before
the least D vertex every split mechanism uses exactly its original inputs,
for every stream. Condition 1 puts the entire replay boundary in this prefix.
`coupledReplayAccept_iff` identifies the actual split and original acceptance
contexts, and `coupledReplayEval_of_success` identifies the successful split
output with original evaluation of the existing conditional resampling.
No probability, measurability or positivity hypothesis is added for this step.
Targeted module validation passed before starting step 2. No subagents are used.

### Current three-step pass: step 2 completed — encoded-input independence

`Probability.IndependentAppend` proves the complete dependent-product law
after adjoining a separate product-space input to a mutually independent
family. `HiddenGraph.StrongFaceIndependence` applies this to the whole trial
stream and uses an injective reindexing to prove full mutual independence of
every actual split root and private input. Checked root/private coordinate
identities tie the indexed family to `encodeReplayStream`; private ULifts
only provide uniform universes. No selected-candidate independence is claimed.
Both modules compiled without warnings before starting step 3.

### Current three-step pass: step 3 completed — observed-law preservation

`Probability.ReplayInvariance.finite_fiber_average` proves the finite law of
total probability for the normalized boundary-fiber masses, including null
fibers. `independent_resampling_mass` applies this at fixed external inputs
and integrates against the external/local product law. No regular conditional
distribution or strictly positive observed-law assumption is used.

`HiddenGraph.StrongFaceLaw.conditionalResampledInputs_map` instantiates this
with the actual replay selector and proves preservation of the **entire native
original input law**. `coupledReplayEval_ae` uses boundary alignment and the
derived almost-sure success theorem. Finally `coupledReplayEval_map` identifies
the full observed distributions of the actual split evaluation and original
model. This uses the same concrete product coupling whose complete encoded
root/private family was proved mutually independent in step 2.

Scope: finite observed state spaces (the manuscript's setting), measurable
original local mechanisms, full original input independence and arbitrary
measurable original root/private input types. No standard-Borel restriction,
c-degree assumption or observed-law positivity is added. Both law chapters
compile without warnings. This completes the requested three steps; the
bundled A1 probability-model equivalence remains a separate assembly task.

Integrated validation of all three steps: `lake build` passed (3,061 jobs).
All 335 smoke declarations used only `propext`, `Classical.choice` and
`Quot.sound` (or a subset). The source placeholder scan, whitespace checks
of the new chapters and `git diff --check` passed. All five new chapters
compiled without warnings. No subagents were used. No new manuscript defect
was identified; `manuscript-issues.md` distinguishes the completed reverse
transport from the remaining bundled-equivalence assembly.

The bundled A1 probability-model equivalence is completed in the following
sequential continuation.

## Sequential continuation: complete A1 Strong Face Splitting equivalence

Working solo, completed manuscript `prop:strong` as an equivalence of actual
bundled observational probability models.

- `HiddenGraph.RootProbabilityModel` records arbitrary measurable original
  sample, root and private spaces; full mutual input independence; and joint
  measurability of every permitted-parent mechanism. Its observed measure is
  proved to be a probability measure. The derived native joint input law is
  probabilistic and independent, and evaluating it has the same observed law
  as the arbitrary original sample-space model.
- `HiddenGraph.StrongFaceBundling` proves the easy split-to-original transport
  measurable, with full independence from disjoint grouping. The common D
  input belongs only to the anchor root's group; other common components are
  fixed constants. All private inputs retain their own groups. The old sample
  space is retained and the checked pointwise identity preserves its law.
- `HiddenGraph.StrongFaceNativeTransport` connects the earlier uniform ULift
  coordinate families with the literal native root/private inputs of the
  replay model through measurable maps. Its complete native input independence
  is a conclusion, and the constant pointwise replay encoding is not used.
- `Completeness.StrongFaceSplitting.probabilityModel_bundleSplit` and
  `probabilityModel_replayStrong` construct literal model bundles. Every
  measurability, probability and independence field is discharged. Their
  observed-law identities give `original_model_iff_strongFaceSplitting` and
  `constraint_valid_iff_strongFaceSplitting`: equality of the actual A1
  observational model classes and of every observed-law constraint predicate.

Scope: finite observed states, arbitrary measurable exogenous/sample spaces,
the manuscript's literal coverage hypotheses and a nonempty selected root
family. No A2, c-degree, strictly positive observed-law or standard-Borel
hypothesis is added. Types share a common universe, following the existing
probability-model bundle; this is bookkeeping for the included finite, real
and product spaces. The theorem is observational, as is `prop:strong`.
All four new chapters passed targeted compilation without warnings. No
subagents were used and no new manuscript defect was identified.

Integrated validation: `lake build` passed (3,065 jobs). All 357 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan and `git diff --check` passed. The new
chapter whitespace checks passed as well. The milestone is complete.

The first path/dependence submilestone of milestone 4 is completed in the
following sequential continuation.

## Sequential continuation: district reachability and instrumental-path exclusion

Working solo, completed the graph and deterministic-dependence foundation of
manuscript `prop:ineqstructure`, including Appendix Step 1 and the exclusion
obstruction in type (i).

- `CompactDistrict.Reachability.MemberPath` records a nonempty directed path
  whose vertices after its source all stay in the selected district. It
  includes its terminal member, permits a direct edge, and never allows an
  observed path to leave the district and return. Checked vertex membership,
  topological bounds and cardinality/length identities prevent repeated
  vertices in subsequent copying constructions.
- `eval_eq_of_eq_on_reaching` proves Appendix Step 1 for the existing compact
  profile evaluation. `eval_eq_of_change_unreached` derives invariance to a
  change in one unreaching external input. These statements allow arbitrary
  state spaces and need no probability or c-degree premise.
- `CompactDistrict.InstrumentalStructure` records the literal path W to A,
  edge A to B, and exclusion of every path vertex except A from B's parents.
  W itself is included in the exclusion. Intermediate vertices explicitly
  exclude A. The direct W→A case has an empty intermediate set, and the DAG
  order proves B is off the entire path.
- `InstrumentalWitness.parentAssign_eq` and `outcome_eq_of_compatible` prove
  that varying W, copied intermediate values and B leaves every permitted
  argument of B unchanged when other members agree. `not_both_compatible`
  gives the resulting two-row obstruction to a single response profile.
- `HiddenGraph.InequalityStructures` specializes the definitions and Step 1
  theorem to `observedDistrict G`, and checks that the restricted reachability
  implies ordinary observed ancestry. The converse is not assumed.

Scope: this completes the reachability/path submilestone, not the full remark.
The affine 0/1 witness, nonmembership in the convex mixture polytope and
nontrivial-H-row conclusion still need to be assembled. A wording ambiguity
in the appendix's description of the type-(i) target is recorded in
`manuscript-issues.md`: only intermediate vertices copy ζ while A is zero.
The manuscript files have not been edited.

Validation: the integrated `lake build` passed (3,068 jobs). All 389 smoke
declarations used only `propext`, `Classical.choice` and `Quot.sound` (or a
subset). The source placeholder scan, new-chapter whitespace scan and
`git diff --check` passed. All three new chapters compiled without warnings.
No subagents were used. The appendix wording clarification is recorded as
issue 10; it does not invalidate the intended construction. This submilestone
is complete.

The lifted profile construction and affine identity are completed in the
following sequential continuation. Convex-polytope nonmembership remains next.

## Sequential continuation: lifted instrumental profiles and affine target

Working solo, completed the path-copying construction and exact affine
identity in Appendix `prop:ineqstructure` (i).

- `CompactDistrict.PathCopying` selects a listed observed parent for each
  path member, from the external source or another path member. The selected
  parent precedes the terminal treatment A. No member obtains access to an
  unlisted input. Additional permitted edges cause no problem: the evaluation
  proof checks the copied bit for the selected parent on every external input.
- `CompactDistrict.InstrumentalProfiles` constructs actual profiles for any
  binary treatment/outcome rules f,g. Intermediate vertices copy ζ, A applies
  f, B applies g to A, and all other members are at their chosen zero level.
  `read_copyParent` and `eval_copyingProfile` verify the complete structural
  equations using the existing compact evaluation and parent restrictions.
- Two full assignments supply chosen zero and one values. They need be
  distinct only at district members for these results; irrelevant coordinates
  may coincide. Deterministic evaluation needs no finite or binary-only state
  spaces. The source indicator is one at W's chosen one value and zero at all
  other W values, so arbitrary extra external levels are included.
- `CompactDistrict.InstrumentalAffine` defines the actual three profiles with
  rules (id,id), (not,constant one), and (constant one,constant one). The target
  fixes A to zero and B to ζ, with only intermediate path vertices copying ζ.
  `instrumentalTarget_eq_columns` proves t=a+b−c at **every full compact row**,
  including all surrounding district members and external input assignments.
- The target has zero/one entries. With finite observed state spaces, each
  external-input block is a probability vector. The target lies in the affine
  span of the actual compatibility columns and of their mixture polytope.
  The coefficients are the manuscript's 1,1,−1, summing to one.

Scope: the affine construction is complete. The full instrumental conclusion
still needs convex-polytope nonmembership and the nontrivial-H-row assembly.
Distinct zero/one values at W will be required to exhibit the two incompatible
external input blocks in that next step. The implementation follows the
explicit A=0 target triple in the appendix, resolving the implementation
convention for the wording ambiguity already recorded as issue 10; no further
manuscript issue was found.

Validation on 2026-11-04: the integrated `lake build` passed (3,071 jobs).
All 406 smoke declarations used only `propext`, `Classical.choice` and
`Quot.sound` (or a subset). The source placeholder scan and `git diff --check`
passed, as did the new-chapter whitespace check. All three new chapters
compiled without warnings. No subagents were used. This affine submilestone
is complete.

The convex-polytope nonmembership step is completed in the following
sequential continuation.

## Sequential continuation: instrumental target outside the district polytope

Working solo, completed the instrumental target's nonmembership argument in
Appendix `prop:ineqstructure` (i).

- `Polytope.ZeroOne.zero_one_mixture_is_column` proves the extreme-point step
  directly from nonnegative weights summing to one and entries bounded in
  [0,1]. A positive-weight column is selected once, and agrees with the
  zero/one target at **every** row. Duplicate columns are allowed; no separate
  external vertex enumeration is assumed.
- `CompactDistrict.InstrumentalNonmembership` chooses explicit external
  assignments e0 and e1. They agree at every coordinate except W, where they
  use the chosen distinct zero/one levels. Their source bits are checked to
  be false and true.
- `target_assignments_agree_off_path` verifies that A and all other members
  outside B/intermediate vertices agree. Applying the existing excluded-parent
  obstruction proves `instrumentalTarget_not_profile`: no one profile can
  produce all target blocks. This deterministic argument needs distinct
  levels only at W and B.
- `instrumentalTarget_not_column` connects equality of the actual complete
  compatibility column to the specified target evaluations. The generic
  zero/one mixture lemma then proves `instrumentalTarget_not_mem_mixture`.
- `instrumental_affine_witness` combines the three properties required by the
  appendix: every target block is a probability vector, the target belongs to
  the affine hull of the actual district polytope, and it lies outside that
  polytope. All surrounding members and arbitrary extra external levels are
  retained. The affine part uses the chosen distinct member levels from the
  previous milestone; this step adds distinct levels at W.

Scope: the full instrumental affine witness is checked for arbitrary finite
observed state spaces with the stated chosen levels. The final nontrivial-H-row
conclusion and graph-level extraction of level choices remain to be assembled.
No new manuscript issue was found; the implementation continues to use the
explicit A=0 target convention recorded in issue 10.

Validation on 2026-11-04: the integrated `lake build` passed (3,073 jobs).
All 412 smoke declarations used only `propext`, `Classical.choice` and
`Quot.sound` (or a subset). The source placeholder scan, new-chapter whitespace
check and `git diff --check` passed. Both new chapters compiled without
warnings. No subagents were used. This nonmembership submilestone is complete.

The nontrivial-H-row and actual graph-level instrumental assembly are completed
in the following sequential continuation.

## Sequential continuation: graph-level instrumental nontrivial inequality

Working solo, assembled the instrumental branch of `prop:ineqstructure` for
the actual hidden-graph district, including its positive observed-law consequence.

- `Polytope.HRepAffine` checks Appendix Step 2. Every equality of a checked
  exact H-system holds on the full affine hull of its mixture polytope. An
  affine point outside the polytope violates an inequality row. If it is in
  the basic probability domain, that same point witnesses nontriviality on
  the basic domain intersected with the equality set. No separate affine-hull
  exactness or facet geometry is needed for this row-existence implication.
- `CompactDistrict.LevelChoices.HasTwoLevels` records the literal cardinality
  assumption on members and external parents. `exists_reference_levels` and
  `exists_instrumental_levels` derive the two reference assignments from
  those cardinalities. Other observed variables require only nonempty state
  spaces to extend the assignments; they need not have two levels.
- `HiddenGraph.InstrumentalInequalities` specializes to `observedDistrict G`.
  The actual graph structure and state cardinalities produce the full lifted
  affine witness, without supplied binary encodings. The target satisfies
  `KernelSimplex` and every H-equality, while strictly violating an H-row.
  `instrumental_nontrivial_H_row` proves failure of the existing `KernelTrivial`
  predicate for that row, hence the manuscript's nontrivial-inequality claim.
- `Completeness.InstrumentalStructure.instrumental_structure_positive_witness`
  invokes the checked general facet-witness theorem with this derived row.
  At c-degree at most one it constructs a strictly positive normalized observed
  law satisfying global ancestral-moral graphical independencies, every
  equality, all other selected-district facets strictly, and every other
  district inequality, while violating the selected row strictly.

Scope: the instrumental branch is assembled. Its H-row statement uses a
checked exact H-representation. The positive global witness additionally
uses the same checked affine-hull exactness and proper, distinct codimension-one
facet data as the earlier general `prop:nontrivial` (ii) theorem; no nontrivial
row or positive observed law is assumed. Numerical V-to-H certificate
construction remains a later milestone. No new manuscript issue was found;
the wording clarification in issue 10 and the unchanged source files remain
documented. All four new chapters passed targeted compilation without warnings.

Integrated validation on 2026-11-04: `lake build` passed (3,077 jobs). All
421 smoke declarations used only `propext`, `Classical.choice` and `Quot.sound`
(or a subset). The source placeholder scan, new-chapter whitespace check and
`git diff --check` passed. No subagents were used. This instrumental assembly
milestone is complete.

**Next:** the Bell branch, `prop:ineqstructure` (ii). First prove that its two
external sources are distinct and the two district-internal paths are disjoint,
using the no-cross-reach assumptions. Then construct the lifted Bell profiles
and PR-box target, reuse the checked 3/16 and −1/16 affine weights, and prove
polytope nonmembership from profile dependence and CHSH. Exact numerical
certificates and publication remain later milestones.

## Sequential continuation: Bell-path geometry

Working solo on `prop:ineqstructure` (ii), added the literal `BellWitness`
with two chosen district-member paths and the full no-cross-reach assumptions.
`MemberPath.reaches_vertex` checks prefixes, and `reaches_endpoint` splices
any reaching path into a chosen suffix. Consequently the two sources and
endpoints are distinct, the two member paths are disjoint, neither path
contains the opposite endpoint, and their intermediate sets are disjoint.
The stronger statements exclude each source from reaching any member of
the opposite path. Direct paths have empty intermediate sets; their
constructor retains full no-cross reachability rather than merely excluding
cross edges.

`HiddenGraph.BellStructure` specializes the witness to the actual district
partition. Its `bell_eval_A_eq` and `bell_eval_B_eq` apply Appendix Step 1:
every profile's endpoint value is invariant when only the opposite source's
external coordinate changes. No cardinality, probability or c-degree premise
is needed for these geometry and dependence statements.

Scope: these are the path-separation and deterministic-dependence foundations,
not the full Bell inequality or its affine witness. No new manuscript issue
was found, and the manuscript sources remain unchanged.

Validation on 2026-11-04: both new chapters compiled without warnings, and
the integrated `lake build` passed (3,079 jobs). All 434 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source placeholder scan, new-chapter whitespace check and
`git diff --check` passed. No subagents were used. This geometry milestone
is complete.

**Next:** construct the lifted Bell copying profiles and verify their actual
evaluations. Then lift the PR-box target and signed affine weights, prove
nonmembership by CHSH, and assemble the graph-level nontrivial inequality
and positive observed-law witness. Numerical certificates and publication
remain later milestones.

## Sequential continuation: lifted Bell copying profiles

Working solo on Appendix `prop:ineqstructure` (ii), added
`CompactDistrict.BellProfiles`. `MemberPath.copyValue` reads one selected
actual observed parent and applies a Boolean function only at the endpoint.
`read_copyParent_of_values` proves that any assignment copying the source
bit on intermediate members gives every such parent reader that same bit.
The endpoint's assigned value is irrelevant because every selected parent
is strictly before that endpoint.

`BellWitness.copyingProfile` combines these mechanisms on the two disjoint
member paths. `binaryAssignment` specifies the complete district output:
intermediates on the A path copy alpha, intermediates on the B path copy
beta, A=f(alpha), B=g(beta), and all remaining members are their chosen zero.
`eval_copyingProfile` proves this complete assignment is the actual compact
evaluation at every external input. Endpoint corollaries make the f/g
semantics explicit; `matrix_copyingProfile` gives the corresponding actual
compatibility-column indicator on full compact rows.

Scope: arbitrary state spaces with two chosen distinct levels at each member;
no finite-state, c-degree or probability premise. Extra external levels are
decoded as zero unless they equal the chosen one, exactly as in the appendix.
Both direct paths and paths with intermediates use the same construction.
Extra observed parents are ignored by these particular mechanisms; no member
is given access to an unlisted parent. The existing binary encoding and
path-parent selection are reused without changing the instrumental proofs.
No new manuscript issue was found; manuscript sources are unchanged.

Validation on 2026-11-04: the new chapter compiled without warnings, and
the integrated `lake build` passed (3,080 jobs). All 443 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source placeholder scan, new-chapter whitespace check and
`git diff --check` passed. No subagents were used. This lifted-profile
milestone is complete.

**Next:** define the lifted PR-box target, check normalized external-input
blocks and the signed 3/16, -1/16 affine identity on full compact rows.
Then prove nonmembership using profile dependence and CHSH, assemble the
graph-level nontrivial inequality and positive observed-law witness, and
continue to numerical certificates and publication.

## Sequential continuation: lifted PR-box target and signed affine identity

Working solo on Appendix `prop:ineqstructure` (ii), added
`CompactDistrict.BellAffine`. `bellTarget` pushes the checked binary PR law
onto the full district assignment used by the copying profiles. At each
external input, intermediate members copy their own decoded source bit,
surrounding members are zero, and only the two endpoint bits are random.
`binaryAssignment_injective` derives distinctness of the four assignments
from the chosen distinct member levels. `bellTarget_at_assignment` proves
that their probabilities are exactly the binary PR probabilities (one half
for winning parity, zero otherwise); `bellTarget_eq_zero_of_outside` gives
zero mass at every other full member assignment.

`bellTarget_block_probability` proves nonnegativity and normalization of
every external-input block, including inputs at additional state levels.
`matrix_copyingProfile_eq_pushforward` transports a deterministic binary
column through the same assignment map. Finite-sum interchange then lifts
the already checked binary `signed_mixture_eq_prBox` with the unchanged
3/16 and -1/16 weights. `bellTarget_eq_signed_columns` is the resulting
identity on every complete compact row. The weights sum to one, proving
membership in the affine span of actual district columns and in the affine
hull of their mixture polytope.

Scope: no convex membership or nonmembership is claimed in this milestone.
Chosen distinct member levels suffice for the affine identity and support
description. Finiteness is used for block normalization and the finite-state
mixture polytope; no c-degree or probability-model premise is needed. The
chosen levels at the two external sources need not yet be distinct; that
assumption enters the four-reference-input nonmembership argument next. The
numerical signed-weight calculation is reused from `Examples.BellAffine`,
with its existing kernel-checked enumeration. No new manuscript issue was
found, and manuscript sources remain unchanged.

Validation on 2026-11-04: the new chapter compiled without warnings, and
the integrated `lake build` passed (3,081 jobs). All 451 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source placeholder scan, new-chapter whitespace check and
`git diff --check` passed. No subagents were used. This lifted PR-box affine
milestone is complete.

**Next:** prove the lifted target is outside the convex district polytope
using the four reference external inputs, the no-cross profile-dependence
theorems and CHSH. Then assemble the graph-level Bell nontrivial inequality
and positive observed-law witness. Numerical certificates and publication
remain later milestones.

## Sequential continuation: CHSH nonmembership of the lifted Bell target

Working solo on Appendix `prop:ineqstructure` (ii), added
`CompactDistrict.BellNonmembership`. `referenceInput` varies the two sources
over their chosen binary levels and fixes every other external coordinate.
`reference_source_bits` checks that the four reference inputs decode to
the intended input bits when the source levels are distinct. The existing
no-cross reachability hypotheses and Step 1 give `eval_reference_A` and
`eval_reference_B`: A depends only on the first bit and B only on the second,
for every actual district profile, regardless of extra member state levels.
`responseProfile` decodes their chosen-one indicators as two Boolean
response functions.

`gameScore` is the appendix's S(p), summing over full member assignments at
the four reference inputs. `gameScore_column` identifies the score of every
actual compatibility column with the checked binary CHSH score.
`gameScore_mulVec` proves finite-sum linearity; `gameScore_le_three` derives
the CHSH bound for the entire district mixture polytope. The lifted PR
target's copied assignments decode to their endpoint bits, and each block
wins with total probability one. `bellTarget_gameScore` therefore gives
score four, and `bellTarget_not_mem_mixture` proves convex nonmembership.
`bell_affine_witness` assembles block probabilities, affine-hull membership
and convex nonmembership of the same full-row target.

Scope: finite observed state spaces with chosen distinct member levels and
distinct levels at both external sources. The CHSH bound itself needs no
level-distinctness assumption and decodes arbitrary outputs by equality to
the chosen one. No c-degree, graphical probability-model or positivity
premise is used in this deterministic/convex argument. No new manuscript
issue was found; manuscript sources are unchanged.

Validation on 2026-11-04: the new chapter compiled without warnings, and
the integrated `lake build` passed (3,082 jobs). All 463 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source placeholder scan, new-chapter whitespace check and
`git diff --check` passed. No subagents were used. This CHSH nonmembership
milestone is complete.

**Next:** derive the binary level choices from cardinality assumptions and
assemble the actual hidden-graph Bell nontrivial H-row, then its positive
globally Markov observed-law witness under the existing checked facet data.
Numerical certificates and publication remain later milestones.

## Sequential continuation: graph-level Bell nontrivial inequality

Working solo, assembled the Bell branch of `prop:ineqstructure` for the
actual hidden-graph district and its positive observed-law consequence.
`HiddenGraph.BellInequalities.bell_affine_witness_of_two_levels` uses
`exists_reference_levels` to derive all member levels and both external
source levels from the literal `HasTwoLevels` cardinality assumption.
Coordinates outside the members and external parents need only be nonempty.
The result is the normalized lifted PR-box affine witness outside the actual
district mixture polytope, with no supplied binary encoding.

`bell_nontrivial_H_witness` applies Appendix Step 2 to a checked exact
H-system: the target satisfies every equality, violates an inequality row,
and witnesses failure of the existing `KernelTrivial` predicate for that
row. `bell_nontrivial_H_row` exposes the nontrivial-inequality conclusion
for the actual graph partition. Separate affine-hull exactness and facet
geometry are unnecessary for this row-existence implication.

`Completeness.BellStructure.bell_structure_positive_witness` invokes the
general checked facet-witness theorem using the derived nontrivial row.
At c-degree at most one it gives a strictly positive normalized globally
ancestral-moral Markov observed law satisfying every H-equality, violating
the selected row strictly, satisfying all other selected-district facets
strictly, and satisfying every other district inequality.

Scope: both branches of the inequality-structure roadmap are now assembled.
They use checked exact H-representations; positive observed-law realization
additionally uses the same selected-district affine-hull exactness and
proper, distinct codimension-one facet data as the general `prop:nontrivial`
(ii) theorem. Neither nontriviality nor a positive observed law is assumed
as an input. Numerical H-conversion and geometric certificates are still
separate obligations. No new manuscript issue was found, and manuscript
sources remain unchanged.

Validation on 2026-11-04: both new chapters compiled without warnings, and
the integrated `lake build` passed (3,084 jobs). All 467 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source placeholder scan, new-chapter whitespace check and
`git diff --check` passed. No subagents were used. This graph-level Bell
assembly milestone is complete.

**Next:** milestone 5, exact example certificates. Begin with the actual
Appendix B instrumental compatibility matrix and its stated H-system;
check the correspondence to the manuscript/R data and certify V-to-H
exactness in Lean. Publication remains milestone 6.

## Sequential continuation: Appendix B literal data and H necessity

Working solo, began milestone 5 with `Examples.InstrumentalAppendix`.
The literal 8-by-16 B, 12-by-8 H_i, 2-by-8 H_e and both right-hand-side
vectors are transcribed from Appendix B. `rowEquiv` checks the printed
(X,Y,Z) order against the semantic (Z,X,Y) row type. `profileEquiv` enumerates
all sixteen actual response profiles in the printed column order, including
different profiles producing repeated columns. `printedB_eq_matrix` checks
each of the 128 entries against the existing semantic IV matrix.

`printedB_inequalities` checks all 192 column/inequality pairs by exact
arithmetic, and `printedB_equalities` checks both normalizations at every
column. `printed_mixture_feasible` transports these checks through simplex
mixtures. `reindex_simplex` and `reindex_mulVec` retain all profiles under
the column permutation; `instrumental_mixture_printed_feasible` therefore
gives every printed H inequality and equality for actual semantic IV mixtures.

`scripts/check-iv-appendix.ps1` compares the numeric Lean transcription with
the LaTeX and stored R output, including all entries, right-hand sides,
the row-coordinate change and rcdd's [equality flag,b,-A] sign convention.
The source audit passes without rerunning R or trusting cdd as a proof step.
No discrepancy or new manuscript defect was found; sources remain unchanged.

Scope: this submilestone certifies data correspondence and H necessity.
It does not construct an exact `HRep`, prove reverse H sufficiency, or
certify facet dimensions/nontriviality for this numerical H-system.

Validation on 2026-11-04: the chapter compiled without warnings, and the
integrated `lake build` passed (3,085 jobs). All 476 smoke declarations used
only `propext`, `Classical.choice` and `Quot.sound` (or a subset). The
source-transcription audit, source placeholder scan, new-file whitespace
check and `git diff --check` passed. The sources directory has no changes.
No subagents were used. This data-and-necessity submilestone is complete.

**Next:** prove reverse inclusion for this exact Appendix B H-system by
constructing nonnegative response-profile weights from every feasible H
vector (or an equivalent exact finite certificate), then bundle the checked
`HRep`. Concrete affine-hull/facet certificates and subsequent examples
follow before publication.

## Sequential continuation: Appendix B exact H-representation

Working solo, completed reverse H inclusion for the literal Appendix B
instrumental system. `Examples.InstrumentalHRep.printed_feasible_mixture`
constructs all sixteen response-profile weights from an arbitrary feasible
H vector. Seven independent margin equations leave five free weights on
twelve distinct columns; the four duplicate-column profiles receive zero.
A finite symbolic Fourier–Motzkin certificate eliminates the five weights,
derives 28 terminal bounds from the printed H rows and normalizations, and
reconstructs the free weights in reverse order as maxima of lower bounds.
Every lower/upper comparison and reconstructed nonnegativity condition is
checked by Lean linear arithmetic. The final simplex normalization and all
eight margin equations are checked explicitly.

`printed_mixture_iff_feasible` combines the two directions, and `printedHRep`
bundles precisely the manuscript's twelve inequalities and two equalities
with their exact-representation proof. `Examples.InstrumentalExact` transports
the reverse inclusion through the row/profile equivalences, proves
`instrumental_mixture_iff_printed_feasible`, and bundles `semanticHRep` for
the original (Z,X,Y) semantic IV matrix.

`scripts/generate-iv-hrep.mjs` reproducibly generates the explicit certificate;
its output is checked by the kernel, rather than assuming correctness of the
generator or an external solver. Only division by fixed numeric coefficients
is used, never division by a probability. Zero probabilities and boundary
points are included. Source correspondence remains checked independently by
`scripts/check-iv-appendix.ps1`; manuscript and R sources are unchanged.
No new manuscript defect was found.

Scope: Appendix B V-to-H exactness is now proved for the literal and semantic
matrices. This does not yet certify its affine-hull equations separately,
the proper/distinct facet dimensions and classification, or the numerical
H-systems of subsequent examples. General H-conversion algorithm correctness
is not claimed.

Validation on 2026-11-04: both new chapters compiled without warnings, and
the integrated `lake build` passed (3,087 jobs). All 481 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
Certificate regeneration was byte-identical. The source-transcription audit,
placeholder scan, new-file whitespace check and `git diff --check` passed.
The sources directory has no changes. No subagents were used. This exact
H-representation milestone is complete.

**Next:** derive concrete affine-hull and facet certificates for this exact
Appendix B system, including the eight nonnegativity facets and four
nontrivial instrumental facets. Subsequent example certificates and publication
remain later milestones.

## Sequential continuation: Appendix B affine hull and dimension

Working solo, added `Examples.InstrumentalHull`. `printed_equalities_iff`
identifies the two literal H_e equations with normalization of the separate
Z=0 and Z=1 blocks. `affineColumn` selects printed columns 4, 7, 10, 12,
13, 14 and 15 (one-based indices). `affineWeight` gives explicit signed
weights for these seven columns. They sum to one at every normalized vector,
and `sevenColumnMap_affineWeight` reconstructs all eight coordinates using
only the two normalizations. Thus `normalized_mem_sevenColumnHull` proves
affine-hull membership for arbitrary signed normalized vectors.

The converse follows from the checked exact H-system's equality necessity
on the affine hull. `printed_columnHull_iff` supplies the literal concrete
affine-hull exactness input required by the general facet theorems.
`printed_columnHull_eq_seven` proves that these seven selected columns span
the whole hull. The explicit inverse `affineWeight_sevenColumnMap` also
proves `sevenColumn_linearIndependent`, hence affine independence. The
existing finite-dimensional affine-space theorem gives
`printed_columnHull_finrank`: the hull's direction has dimension six.

Scope: this milestone certifies the printed matrix's full affine hull and
its dimension; signed points are included without inequalities, positivity
or probability denominators. The twelve individual facet dimensions,
properness/distinctness and nonnegativity/nontrivial classification remain
separate. No new manuscript issue was found; manuscript and R sources remain
unchanged.

Validation on 2026-11-04: the new chapter compiled without warnings, and
the integrated `lake build` passed (3,091 jobs). All 492 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source-transcription audit, placeholder scan, new-file whitespace check
and `git diff --check` passed. The sources directory has no changes.
No subagents were used. This affine-hull and dimension milestone is complete.

**Next:** certify that the twelve printed H inequalities are distinct proper
facets of dimension five, then check the appendix's classification into eight
nonnegativity facets and four nontrivial instrumental facets. Subsequent
example certificates and publication remain later milestones.

## Sequential continuation: Appendix B twelve distinct proper facets

Working solo, added exact integer witness data in
`Examples.InstrumentalFacetData` and geometric assembly in
`Examples.InstrumentalFacets`. For each of the twelve printed inequalities,
`facetColumn` selects six actual response columns and `facetReader` gives
an integer left inverse of their eight-by-six matrix. Lean checks the
integer identities, selected-column tightness, strict off-plane columns,
and a separating column for every pair of distinct H rows. Entrywise cast
proofs identify the integer B/H data with the literal real matrices.

`facetColumn_linearIndependent` derives independence from the left inverse;
the six selected incident points therefore have affine dimension five.
The full incident hull is a proper subspace of the checked six-dimensional
column hull, so it has dimension at most five. These bounds give
`printed_facetHull_finrank` and `printed_facets_codimension_one` for every
printed row. `printed_facets_distinct` uses the pairwise separating columns
to distinguish the incident affine hulls. Finally `printed_facetSpan`
derives each complete supporting-plane identity from the general rank
theorem and the concrete normalized affine hull.

`scripts/generate-iv-facets.mjs` reads the printed B/H definitions and
generates the integer certificates. The generator is outside the trusted
proof kernel: its entire output, including casts and all finite arithmetic,
is checked by Lean. No numerical rank estimate or external solver result
is assumed.

Scope: all twelve H rows are certified valid, proper, distinct codimension-one
facets, with nonempty incident sets and five-dimensional incident hulls.
The appendix's classification into eight nonnegativity facets and four
nontrivial instrumental facets is the next submilestone. No new manuscript
issue was found; manuscript and R sources remain unchanged.

Validation on 2026-11-04: both new chapters compiled without warnings, and
the integrated `lake build` passed (3,093 jobs). All 513 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
Facet certificate regeneration was byte-identical. The source-transcription
audit, placeholder scan, new-file whitespace check and `git diff --check`
passed. No subagents were used. This twelve-facet geometry milestone is
complete.

**Next:** use these checked facet data with the general coordinate-incidence
criterion to prove the exact eight/four classification and its nonnegativity
certificates. Subsequent example certificates and publication remain later
milestones.

## Sequential continuation: Appendix B eight/four facet classification

Working solo, added `Examples.InstrumentalClassification`.
`nonnegCoordinate` records the exact probability coordinate for each of
the manuscript's eight nonnegativity rows. `nonneg_slack_certificate`
proves an identity on arbitrary signed vectors: the row's slack is that
coordinate plus a fixed combination of the two equality residuals. The
combination is zero for rows 1,4,7,9,11,12, the second normalization residual
for row 8, and the first for row 10 (one-based numbering). On the normalized
affine hull, `nonneg_slack_eq_coordinate` reduces every one of these rows
to precisely its coordinate's nonnegativity.

For each of rows 2,3,5,6 and each probability coordinate, a checked integer
witness gives an actual incident column with value one at that coordinate.
`nontrivial_incident_cover` transports this to the real matrix. In particular,
these four facets have no common zero coordinate. The geometric criterion
`coordinate_trivial_iff_incident_zero_of_ranks` is instantiated using the
already checked affine hull, validity, properness, incidence, dimension and
distinctness data, together with nonnegative entries and coordinate coverage.
`printed_facet_trivial_iff` and `printed_facet_nontrivial_iff` therefore prove
the exact classification in the existing `CoordinateTrivial` sense. The
two explicitly enumerated row sets have checked cardinalities eight and four.

Scope: the normalized nonnegative affine domain here is exactly the two
probability simplices, so the classification includes the equalities as
required by the manuscript. The explicit certificates hold even off that
domain. This completes the Appendix B matrix-level exact-H, affine-hull,
facet-geometry and classification certificate package. No R classification
flag is assumed. No new manuscript discrepancy was found; manuscript and
R sources remain unchanged.

Validation on 2026-11-04: the new chapter compiled without warnings, and
the integrated `lake build` passed (3,094 jobs). All 527 smoke declarations
used only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The source-transcription audit, placeholder scan, new-file whitespace check
and `git diff --check` passed. The sources directory has no changes.
No subagents were used. This eight/four classification milestone is complete.

**Next:** begin the binary front-door district certificate from Section 3.3
and `03-front-door.R`: identify its response matrix and normalization/(O)
equalities, then certify that nonnegativity together with those equalities
is exact and every inequality is trivial. Subsequent numerical examples
and publication remain later milestones.

## Publication continuation: literate book and declaration API

The author requested skipping further concrete example certificates and
proceeding with the Verso book and API documentation. This supersedes the
front-door continuation above. The completed Appendix B certificate package
is retained; no additional R example is a publication prerequisite.

The book uses Verso's literate rendering of the actual Lean source, following
the sibling `causaloptim-lean` layout. New `Guide` and `Scope` chapters give
the manuscript reading routes, the explicit H/facet assumptions, the mutual
independence clarification, and the omitted claims. `literate.toml` orders
the mathematical chapters, renders declaration documentation as prose and
excludes smoke-test plumbing. Shared navigation joins book, guide, scope,
declaration API and resources.

Pinned doc-gen4 provides the project declaration API through its prefix
analysis command. It analyzes all imported project modules in one environment
without regenerating dependency-library API pages. The original full
`MeraConstraints:docs` facet remains available. Cross-platform Node scripts
build, assemble, preview and check the site, and archive the roadmap,
manuscript audit, README correspondence and pinned revisions as resources.
The documentation workflow builds reviewable artifacts and provides an
explicit manual GitHub Pages publication option. No publication is performed
by this local task.

Publication milestone completed on 2026-11-04. The integrated library and
doc-gen4 build passed (3,288 jobs); all 527 audited declarations use only the
standard logical dependencies. All 151 planned chapter exports are valid
JSON. The generated API contains 151 project modules and 1,445 declarations.
The assembled website passes checks for all 318 HTML pages, with no missing
local pages or assets. Browser checks covered the reading guide, scope,
book search, API search, theorem signatures and API-to-literate source links.

Windows setup is reproducible in the builder: pinned C SDK/intrinsic headers,
the local `cc` alias, and a workaround for Verso's search-asset path separators.
One extractor access violation was resolved by an isolated retry; the builder
now retries a failed Windows extraction once with one Lean worker. Namespace
landing pages and custom-route aliases repair Verso's breadcrumb links.
Dependency API imports link externally; project declarations stay local.
No additional manuscript or proof issue arose in this publication pass.
No site was pushed or published. Preview with `node scripts/serve-web.mjs`.

## Remaining milestones

1. **Boundary completion (`rmk:positivity`) — completed.** Exact ordered
   known/free classification, converse reconstruction and original-model
   compact H-completion equivalence are checked, including zero probabilities.
2. **Graph-specific nontriviality (`prop:nontrivial`) — completed under checked
   affine-hull and genuine distinct-facet data.** The actual (N)/(O)
   matrices and fixed-order positive-kernel reconstruction are checked.
   All-ancestral-set margins and actual induced-blanket local equations are
   now checked, as are global ancestral-moral independencies for reconstructed
   laws and graphical necessity for actual original SCMs. The positive and
   boundary completeness iff statements now use the global graphical predicate,
   with the required ordered equations derived. Ordering invariance for
   arbitrary positive graph-compatible laws is now checked, including its
   exact compact observable-factor bridge. All (N)/(O) necessity is now
   checked for those laws, including every fully closed subset and its own
   external-parent dependence. Part (i) is now assembled: graph-trivial
   equalities are precisely affine (N)/(O) row combinations; the intrinsic
   quotient has the manuscript's rank difference; selected spanning H rows
   imply all equality constraints together with global graphical Markov.
   Affine-hull exactness remains an explicit checked input. Part (ii) now
   includes the geometric incidence iff, coordinate certificate, rank-derived
   facet spans/separation and an actual strictly positive globally Markov
   observed-law witness violating only the selected nontrivial facet among
   all district H constraints. Appendix B supplies a concrete numerical
   H/geometric certificate; further examples are skipped under milestone 5.
3. **Graph transformations — completed for the roadmap's three rules.**
   HLP (`prop:hlp`), Strong Face Splitting (`prop:strong`) and latent merging
   (`prop:merge`) are checked. Merging relaxes
   the model, so merged-model constraints hold for the original model.
   Strong splitting's A1-only graphs and both pointwise structural directions
   are checked. The reverse construction has a parent-restricted shared
   candidate checker and a general consistent-replay evaluation theorem.
   The generic independent-trial conditional law, actual infinite-product
   sampler, joint selector measurability and independent-random-context joint
   law are checked for arbitrary measurable spaces. Both global and local
   acceptance are now identified with exact observed-boundary fibers under
   resampling. Disjoint grouping of the original mutually independent inputs
   proves independence of the external/local replay blocks. Original mechanism
   measurability and countable observed states give joint acceptance
   measurability and almost-sure positive fiber probability, hence actual
   independent-stream success, acceptance and the graph-specific conditional
   joint law. The actual split local checker, selector, mechanisms and
   evaluation are jointly measurable on all arguments, including inconsistent
   parents and fallback streams. The concrete context/stream encoding and
   its split evaluation are also measurable. Boundary-context alignment holds
   for every stream, and the complete encoded root/private family is mutually
   independent. For finite observed states, conditional resampling preserves
   the entire original input law and the actual split evaluation has the
   original observed joint law, including zero probabilities. Bundled A1
   probability-model equivalence and validity of every observed-law constraint
   are now assembled in `Completeness.StrongFaceSplitting`, with arbitrary
   measurable original sample/root/private spaces and finite observed states.
   The easy direction's input independence and mechanism measurability follow
   from disjoint anchor-root grouping. The reverse direction derives the native
   joint input law and uses independent replay; the pointwise constant encoding
   is not used as a probability transport. Neither direction assumes A2,
   c-degree, strict positivity or standard-Borel inputs.
   HLP has an explicit edge-added graph and checked pointwise simulations
   in both directions, including reverse absorption evaluation preservation.
   Its measurable input/mechanism transport, full mutual independence and
   actual original probability-model equivalence are now assembled in
   `Completeness.HLP`, for finite observed state spaces and arbitrary original
   measurable exogenous spaces, with no c-degree or positivity assumption.
4. **Inequality structures (`prop:ineqstructure`) — completed under checked
   H-systems and facet data.** Lift the checked binary
   instrumental/CHSH and PR-box affine witnesses along general graph paths,
   allowing arbitrary finite state spaces and surrounding districts. Restricted
   district reachability, Appendix Step 1 profile dependence, the literal
   instrumental-type path witness and its two-row exclusion obstruction are
   now checked, including the direct path case and actual hidden-graph district
   specialization. The instrumental path-copying profiles, full-row affine
   identity t=a+b−c, target block probabilities and affine-hull membership are
   also checked on arbitrary finite observed state spaces with chosen distinct
   member levels. The instrumental zero/one target is also proved outside the
   actual convex mixture polytope using two distinct W inputs and one common
   profile obstruction; the complete normalized affine witness is checked.
   Graph-level level choices and the nontrivial H-row are now derived from
   the manuscript's instrumental structure and cardinality assumptions for
   any checked exact H-system. The strictly positive globally Markov
   observed-law violator is assembled under the general theorem's checked
   affine-hull and genuine facet data. The instrumental branch is complete
   under those data. Bell sources and endpoints are now proved distinct,
   the two member paths and their intermediate sets are disjoint, and
   actual endpoint evaluations are invariant under changing the opposite
   external input alone. Lifted Bell copying profiles now have checked full
   evaluations and actual compatibility-column formulas. The lifted PR-box
   target now has checked normalization, the exact signed affine identity,
   affine-hull membership and convex nonmembership by CHSH. The combined
   lifted Bell affine witness is checked. Cardinalities supply all reference
   levels and give a nontrivial H-row for the actual graph district. Under
   the same checked affine-hull and proper/distinct facet data, the positive
   globally Markov observed-law witness is assembled. Both branches are
   complete under those inputs. General instances retain those inputs;
   further numerical examples are skipped under milestone 5.
5. **Algorithm/exact example certificates — further examples skipped by
   author instruction.** External V-to-H exactness is verified
   for the actual Appendix B IV matrix/H-system; subsequent examples are skipped.
   Appendix B's literal data, row/profile correspondence and all printed
   H constraints' necessity for actual IV mixtures are now checked. Reverse
   H sufficiency, an exact literal `printedHRep`, and its semantic-coordinate
   `semanticHRep` are now checked, including boundary points. The printed
   affine hull is exactly the two normalizations, with an explicit seven-
   column affine basis and direction dimension six. All twelve printed H
   rows are certified distinct proper facets with incident-hull dimension
   five and exact supporting-plane identities. The exact eight/four
   nonnegativity/nontrivial classification is now proved with explicit
   normalization-residual certificates. The Appendix B matrix-level
   certificate package is complete; subsequent example H-systems are
   deliberately not pursued for this publication pass.
   General theorems still take checked `HRep` inputs; no cdd/R output is
   silently trusted. The main completeness statements now use the full
   ancestral-moral graphical predicate. A separate active-trail presentation
   and a general arbitrary-law local-to-global converse remain outside the
   proved scope.
6. **Publication — completed locally.** The Verso book and searchable
   project API are generated and verified, following the sibling site.
   Build/preview scripts, shared navigation, scope and reading-guide chapters,
   resources, link checks and an artifact/manual-Pages workflow are provided.
   Further example certificates are skipped. Public deployment remains a
   separate optional action.

## Acceptance criteria

Every completed milestone must compile with the pinned toolchain, contain no
proof placeholders, expose its main statements through the root module and
smoke test, and document any assumptions that are not yet derived from the graph.
Do not rename an algebraic sublemma to a full manuscript proposition.
