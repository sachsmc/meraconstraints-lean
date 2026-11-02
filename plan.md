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

Integrated validation on 2026-11-02: `lake build` passed (2,321 jobs), the
source placeholder scan passed, and all 96 expanded smoke checks used only
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

## Remaining milestones

1. **Boundary completion (`rmk:positivity`) — completed.** Exact ordered
   known/free classification, converse reconstruction and original-model
   compact H-completion equivalence are checked, including zero probabilities.
2. **Graph-specific nontriviality (`prop:nontrivial`).** Construct the (N)/(O)
   matrices for globally closed sets (now checked), prove positive-kernel realization and
   ordering invariance, and identify graph-trivial equalities with their row
   span. The generic affine consequence, rank and basis-row implications are
   checked. For part (ii), the geometric incidence iff, coordinate certificate
   and rank-derived facet spans/separation are checked. Finish the
   graph-compatible violating-distribution witness.
3. **Graph transformations.** Formalize HLP (`prop:hlp`), Strong Face Splitting
   (`prop:strong`). Latent merging (`prop:merge`) is completed: merging relaxes
   the model, so merged-model constraints hold for the original model.
4. **Inequality structures (`prop:ineqstructure`).** Lift the checked binary
   instrumental/CHSH and PR-box affine witnesses along general graph paths,
   allowing arbitrary finite state spaces and surrounding districts.
5. **Algorithm/exact example certificates.** Verify external V-to-H exactness
   for the actual Appendix B IV matrix/H-system and subsequent examples.
   Checked `HRep` exactness is currently an explicit input; no cdd/R output
   is silently trusted. Relating the sufficient ordered equations to an
   explicit enumeration of all graphical d-separation CIs is also separate.
6. **Publication.** Add Verso book and API-doc builds following the sibling
   site once the remaining coverage is stable.

## Acceptance criteria

Every completed milestone must compile with the pinned toolchain, contain no
proof placeholders, expose its main statements through the root module and
smoke test, and document any assumptions that are not yet derived from the graph.
Do not rename an algebraic sublemma to a full manuscript proposition.
