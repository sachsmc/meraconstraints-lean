# meraconstraints-lean

A developing Lean 4 formalization of **Deriving Complete Constraints in Hidden
Variable Models**, by Michael C. Sachs, Erin E. Gabriel, Robin J. Evans and
Arvid Sjölander. The primary specification is
[`main-revised.tex`](sources/manuscript/main-revised.tex), with proofs in
[`appendix.tex`](sources/manuscript/appendix.tex).

The development follows the literate module style of the sibling
`causaloptim-lean` project, using Lean and Mathlib **v4.31.0**. Its finite
probability, DAG, SCM and response-function modules are adapted under the
Apache 2.0 license, retaining the original copyright and author headers.
The sibling checkout is not a build dependency.

The completeness core is now checked for **original probability models with
arbitrary measurable latent inputs**: observational district identification,
actual interventions, and a marginal-model equivalence using graph-defined
global conditional independencies and checked compact H-representations.
The latter are proof-carrying exact H-systems; external numerical conversion
output is not accepted without that proof. Boundary completion also covers
zero probabilities through the manuscript's first-zero/first-undefined rule.

## Manuscript correspondence

| Manuscript component | Lean declaration | Scope |
|---|---|---|
| Finite response-function representation | `SCM.proposition1`, `SCM.eval_eq_evalR` | Reused general SCM results |
| District with fixed external parents | `District.Graph`, `District.Profile`, `District.eval_unique` | Parent-restricted functions and unique recursive evaluation |
| Arbitrary shared latent induces finite profiles | `District.responseMap_faithful`, `District.card_profile` | Pointwise reduction; no finite original-latent assumption |
| Conditions A1/A2, districts and c-degree | `HiddenGraph.Graph`, `districtOf`, `cDegree`, `graphCDegree` | Bipartite connected components include both observed and latent vertices |
| Zero/one-latent district structure | `connected_observed_eq_of_cDegree_zero`, `child_of_cDegree_le_one` | Singleton case and shared-root star structure are proved |
| Parent-restricted original SCM | `HiddenGraph.SCM`, `HiddenGraph.SCM.eval_eq_evalR` | Arbitrary input types and explicit private disturbances; pointwise response reduction |
| Remark `rmk1` | `SCM.eval_intervene_eq_evalR`, `SCM.interventions_eq_of_same_profile` | The same canonical profile preserves all observed interventions |
| Proposition `prop:ident` | `Identification.original_measure_district_linear` | Observable product equals the compact matrix applied to the profile law induced by an arbitrary measurable original SCM |
| Proposition `causalprop` | `Identification.observableFactor_eq_externalInterventionLaw` | Observable product equals an actual external-parent intervention on the original model; no c-degree restriction |
| District normalization/nonnegativity | `District.kernel_mem_stdSimplex` | Every external-input block is a probability vector |
| Closed-in-district margin constraints | `District.marginal_eq_of_closedInDistrict` | Includes Verma-type instances; only globally ancestor-closed instances are (O) |
| Two closure notions | `HiddenGraph.fullClosed_implies_closedInDistrict`, `Examples.VermaClosure.closure_distinction` | Full observed paths may leave/reenter a district; the paper's Verma graph checks that the converse fails |
| Finite observable probability | `FiniteProbability.assignment_eq_prod_prefixConditional`, `conditional_eq_of_independent` | Ordered chain rule and supported conditioning-set replacement |
| Latent event transport | `FiniteProbability.mass_pushforward`, `pushforward_comp`, `conditional_eq_of_fiberwise_mass` | Event pullbacks, marginals and finite averaging |
| Independent district laws | `Independent.joint_mem_stdSimplex`, `rectangular_mass` | Mutual independence, not just pairwise independence |
| Global product-event identity | `GlobalModel.observed_eq_prod_factor` | Derived from structural uniqueness and independent profile laws; districts may be interleaved |
| Observable predecessor products | `GlobalModel.factor_eq_prod_prefixConditional` | Direct prefix-event factorization and cancellation identify the global-predecessor district product |
| Revised cumulative conditioning sets | `Reconstruction.conditioningVariables`, `observed_eq_prod_observableFactor` | Exactly includes external parents of every earlier district member; ordered Markov equations explicit |
| Conditional identification and finite-profile equivalence | `Identification.structuralFactor_eq_observableFactor`, `finite_profile_iff_factor_feasible` | Under the explicit ordered Markov equations, observable district products equal structural factors and feasible constraints characterize the finite profile model |
| Derived ordered Markov equations | `GlobalModel.observed_orderedMarkov`, `prefixConditional_eq_conditioning` | Proved for generated canonical finite-profile laws by prefix-factor dependence and finite averaging |
| Canonical finite-source completeness | `Completeness.finite_source_iff_HRep` | Positive canonical source laws are exactly those satisfying the ordered equations and checked H-constraints |
| Original marginal-model completeness | `Completeness.original_model_iff_global_compact_HRep` | Actual original measurable probability models are exactly the positive laws satisfying global ancestral-moral graphical independencies and checked compact H-constraints, for c-degree ≤ 1 |
| Original-source realization | `HiddenGraph.sourceDistrictEquiv`, `sourceObserved_eq_observed` | Reindexes independent actual roots/private singleton sources to district laws, requiring c-degree ≤ 1 |
| Explicit SCM realization | `HiddenGraph.profileSCM`, `sourceObserved_eq_profileSCM` | Realization is literally an SCM evaluation pushforward, with constant unused private inputs |
| Actual probability-space realization | `HiddenGraph.probabilityModelOfProfiles_observed` | Constructs a genuine probability measure and proves mutual independence of original inputs; no target constraints appear in the model fields |
| Original finite SCM canonicalization | `HiddenGraph.Canonicalization.nativeObservedLaw_eq_globalModel` | Native original input laws are transported to derived independent district profiles |
| Arbitrary measurable original inputs | `HiddenGraph.MeasureCanonicalization.observedLaw_eq_globalModel` | No finite/countable latent-state assumption; independence is derived from the original inputs |
| Compact manuscript matrix rows | `CompactDistrict.matrix_project`, `observableFactor_mem_mixture_iff_HRep` | Explicit local evaluation and exact V/H transport use only member/external-parent assignments |
| Compact original-model constraints | `Completeness.original_measure_satisfies_compact_HRep` | Every positive original measurable SCM satisfies the compact H-system and required ordered equations |
| Constructive sufficiency of H-constraints | `Completeness.realize_of_orderedMarkov_and_HRep` | Reproduces a positive law from checked constraints and explicit ordered Markov equations |
| V-representation and valid inequalities | `Polytope.mixture`, `Polytope.inequality_of_columns` | Simplex image and column certificates |
| Convex hull of compatibility columns | `Polytope.mixture_eq_convexHull` | Includes matrices with repeated columns |
| V-to-H conversion interface | `Polytope.HRep` | Requires an equivalence proof; does not verify double description |
| Remark `rmk:positivity`, complete boundary rule | `Completeness.original_model_iff_global_boundary_compact_HCompletion` | Actual original models are exactly normalized laws satisfying global graphical independencies and compact H-completions, including zero probabilities; c-degree ≤ 1 |
| First-zero/first-undefined classification | `BoundaryCompletion.known_iff_allPositive_or_firstZero`, `not_known_iff_firstUndefined` | The exact ordered known/free rule; reconstruction does not assume the target factorization |
| Boundary Markov and supported conditioning | `GlobalModel.observed_orderedMarkov_boundary`, `conditioning_supported_prefixFactor_pos_and_ratio` | Allows zero observed probabilities; ratios are asserted only on event support |
| Boundary known-entry soundness | `GlobalModel.factor_zero_of_supported_zero_conditional`, `factor_eq_prod_conditioning_of_supported` | A supported zero forces the whole row to zero despite later undefined factors; defined rows equal their conditional product |
| Proposition `prop:nontrivial` (i), equality iff | `CompactDistrict.equalityTrivial_iff_rowCombination` | Equations holding for every positive normalized globally Markov observed law are exactly affine (N)/(O) row combinations, at c-degree ≤ 1 |
| Proposition `prop:nontrivial` (i), rank count | `CompactDistrict.nontrivialEquality_rank_count` | Intrinsic district equality space modulo intrinsic graph-trivial space has the exact stacked-matrix rank difference; affine-hull exactness is a checked input |
| Proposition `prop:nontrivial` (i), selected equalities | `CompactDistrict.selected_equalities_imply_all` | Selected H equality rows spanning the full coefficient space together with (N)/(O) imply all district equalities on globally Markov observed laws; constants follow from a common compatibility column |
| Actual (N)/(O) equations | `CompactDistrict.OrderingConstraints.constraints_of_mixture`, `positive_equation_iff_rowCombination` | Full-ancestry-closed sets, explicit compact matrices and a strictly positive normalized uniform kernel |
| Positive-kernel reconstruction, fixed-order part | `GlobalModel.KernelReconstruction.reconstruct_positive_kernels` | Arbitrary positive (N)/(O) kernels produce a normalized positive law satisfying the ordered equations and recovering all supplied observable district factors; no polytope feasibility is assumed |
| Appendix `eqn:ancmargin` | `GlobalModel.KernelReconstruction.joint_ancestral_mass` | Every observed ancestral-set margin is the product of literal district margins; valid even for signed (N)/(O) kernels |
| Districts after retaining observed vertices | `HiddenGraph.retainedDistrictConnected_iff`, `inducedAncestralBlanket_eq` | Actual retained latent-incidence connectivity and blanket agree with district intersection at c-degree ≤ 1 |
| All-ancestral local Markov equations | `GlobalModel.KernelReconstruction.joint_ancestralLocalMarkov` | Positive reconstructed laws satisfy the event-level local equations for every ancestral set and sink, using actual induced blankets; general local/global equivalence for arbitrary laws remains open |
| Global graphical kernel reconstruction | `GlobalModel.KernelReconstruction.reconstruct_positive_kernels_global` | Positive normalized law, all ancestral-moral graphical independencies and exact observable-factor recovery, at c-degree ≤ 1; graph separation is defined independently |
| Positive single-district graphical image | `GlobalModel.KernelReconstruction.positive_kernel_iff_graphical_image` | A positive compact kernel satisfies (N)/(O) iff it is the exact observable factor of some positive normalized globally Markov law, at c-degree ≤ 1 |
| Realization preserving other district constraints | `GlobalModel.KernelReconstruction.realize_single_kernel_other_polytopes` | Realizes the selected positive (N)/(O) kernel while every other observable factor lies inside its actual response polytope |
| Original-model graphical necessity | `Completeness.probabilityModel_moralGlobalMarkov` | Actual measurable SCMs satisfy the global ancestral-moral predicate, including zero observed probabilities and arbitrary measurable latent inputs |
| Arbitrary-law graphical global-to-local implication | `GlobalModel.KernelReconstruction.moralGlobalMarkov_orderedMarkov` | Graphical separation implies the exact cumulative ordered equations; no positivity or extra degree assumption in this implication |
| Appendix ordering invariance | `GlobalModel.OrderingInvariance.orderProduct_eq_observableFactor`, `orderProduct_eq_compact_observableFactor` | Every valid topological order gives the existing observable district factor, on full and compact rows, for arbitrary positive globally Markov laws |
| All (N)/(O) equations are graph-trivial | `GlobalModel.OrderingInvariance.observable_constraints` | Every positive globally Markov law satisfies the actual stacked compact matrix, including every fully closed subset; no polytope feasibility or c-degree bound is assumed |
| Graph-separation semantic check | `Examples.MoralCollider.roots_separated`, `roots_not_separated_given_child` | The collider's parents are separated until its child is conditioned on |
| Proposition `prop:nontrivial` (ii), geometric criterion | `FacetCriterion.coordinate_trivial_iff_incident_zero_of_ranks` | Incidence iff and derived positive coordinate certificate from affine-hull and codimension-one facet data |
| Proposition `prop:nontrivial` (ii), actual kernel domain | `CompactDistrict.kernel_trivial_iff_incident_zero`, `coordinate_certificate_of_incident_zero` | Actual compact matrix; affine-hull normalization identifies the paper's cross-product simplex domain |
| Proposition `prop:nontrivial` (ii), observed-law witness | `CompactDistrict.observed_law_violating_only_facet` | Positive normalized globally Markov law violates the selected nontrivial facet, satisfies every H-equality, strictly satisfies other selected-district facets, and satisfies every other district inequality; checked exact H-systems and genuine facet geometry are inputs |
| Exact incidence-matrix test | `CompactDistrict.kernel_nontrivial_iff_incidence_product_pos` | Nontrivial precisely when every entry in the corresponding row of `I Bᵀ` is positive |
| Facet geometry | `FacetCriterion.facetSpan_of_codimension_one`, `strict_incident_column_of_distinct_facets` | Span and other-facet strictness derived from actual incidence direction ranks and distinct facet spans |
| Remark `prop:merge` | `Completeness.original_probabilityModel_realizable_merged` | Actual original model embeds in the merged model, with arbitrary measurable original inputs and no positivity requirement |
| HLP, both pointwise directions | `HiddenGraph.HLP.eval_ignoreEdge`, `eval_absorb` | Original and edge-added structural mechanisms simulate each other at every input realization; arbitrary input types, observed and latent parent inclusion, and a chosen common root |
| HLP, actual probability-model equivalence | `Completeness.original_model_iff_HLP`, `constraint_valid_iff_HLP` | Same marginal model and observed-law constraints, including boundary laws and arbitrary measurable original inputs; transformed input independence follows from disjoint grouping; finite observed states and a common topological labeling |
| Strong Face Splitting, both pointwise directions | `HiddenGraph.StrongFaceSplitting.split_eval_reproduced`, `original_eval_reproduced` | Actual A1-only original/split models; reverse shared replay uses the observed/crossing coverage conditions |
| Strong Face Splitting, general replay semantics | `HiddenGraph.StrongFaceSplitting.localReplayAccept_iff_global`, `firstReplay_shared`, `replayModel_eval_of_consistent` | Every D vertex checks the same candidate using only permitted parents; any accepted replay gives an original evaluation with selected/internal-C roots and C-private inputs resampled |
| Strong Face Splitting, actual boundary fibers | `HiddenGraph.StrongFaceSplitting.replayAccept_iff_boundaryFiber`, `localReplayAccept_iff_boundaryFiber` | The global and each permitted-parent local check are exactly preservation of C and all its observed parents under resampling; overlapping C sets and paths leaving and re-entering C are allowed |
| Strong Face Splitting, supported measurable replay | `HiddenGraph.StrongFaceSplitting.replayBlocks_independent`, `replayAcceptanceEvent_measurable`, `replayAcceptance_ae_positive`, `replayTrials_ae_success`, `replayTrials_joint_law` | Full original input independence gives independent external/local blocks, almost-sure positive acceptance probability, almost-sure independent-stream success and the exact context/selected-candidate joint law; original mechanisms are measurable, observed states countable (including finite), exogenous spaces arbitrary |
| Strong Face Splitting, measurable split mechanisms | `HiddenGraph.StrongFaceSplitting.localAcceptanceEvent_measurable`, `localFirstReplay_measurable`, `replayModel_mechanismsMeasurable`, `replayModel_eval_measurable` | Joint measurability of the actual permitted-parent local checks, replay selector, split mechanisms and evaluation on all arguments, including inconsistent parent assignments and the no-hit fallback; no probability law or positive-fiber premise is needed |
| Strong Face Splitting, concrete measurable coupling | `HiddenGraph.StrongFaceSplitting.encodeReplayStream_measurable`, `coupledReplayEval_measurable` | The common D root receives the trial stream, the other roots retain their original coordinates, and private inputs are retained; the actual split evaluation is measurable on original-context × stream |
| Strong Face Splitting, boundary alignment | `HiddenGraph.StrongFaceSplitting.coupledReplayEval_boundary`, `coupledReplayAccept_iff`, `coupledReplayEval_of_success` | Split and original boundary evaluations agree for every trial stream; successful split output is original evaluation after the exact conditional resampling |
| Strong Face Splitting, complete encoded-input independence | `Independent.appendInput_independent`, `HiddenGraph.StrongFaceSplitting.encodedSplitInput_independent` | Full mutual independence of every encoded split root and private input on the concrete product coupling, with checked identities to the actual structural encoding |
| Strong Face Splitting, reverse probability transport | `HiddenGraph.StrongFaceSplitting.conditionalResampledInputs_map`, `coupledReplayEval_map` | Conditional resampling preserves the entire original input law; the actual split model has exactly the original observed joint law, including zeros; finite observed states, arbitrary measurable original inputs and original measurable mechanisms |
| Strong Face Splitting, actual A1 probability-model equivalence (`prop:strong`) | `Completeness.original_model_iff_strongFaceSplitting`, `constraint_valid_iff_strongFaceSplitting` | Literal bundled probability models on arbitrary measurable sample/root/private spaces have the same observational model and every observed-law constraint; both transports prove input independence and mechanism measurability; finite observed states, the stated coverage conditions and nonempty selected family; no A2, c-degree, strict positivity or standard-Borel premise |
| Independent conditional replay | `Replay.firstReplay_measurable`, `ae_exists_accepted`, `firstReplay_map_eq_cond` | The actual structural selector is measurable; independent common-law trials hit any fixed positive measurable acceptance set almost surely and yield its exact conditional law, for arbitrary candidate measurable spaces |
| Actual independent replay stream | `Replay.trials_independent`, `trials_replay_map_eq_cond` | An explicit infinite-product probability space supplies mutually independent original-law candidates; no finite, countable or standard-Borel candidate-space assumption |
| Jointly measurable contextual replay | `Replay.contextReplay_measurable`, `contextJoint_measurable` | A jointly measurable acceptance event on context × candidate gives a jointly measurable selector and joint output, including the no-hit fallback |
| Independent random-context replay law | `Replay.context_replay_joint_law`, `independent_context_replay_joint_law` | Exact joint conditional law for the explicit product or any independent context/stream coupling; context marginal unchanged; generic acceptance-fiber positivity is required only almost surely, with the Strong Face Splitting instance now derived |
| Appendix nontriviality proof, geometric step | `Geometry.average_pos_of_no_zero_coordinate`, `exists_positive_violator` | Positive facet averages and a violating perturbation preserving other strict inequalities and affine equations; facet structure is input |
| Binary IV example | `Examples.Instrumental.instrumental` | Instrumental inequality for all sixteen-profile mixtures |
| Appendix B, literal IV data and H necessity | `Examples.Instrumental.Appendix.printedB_eq_matrix`, `printedB_inequalities`, `printedB_equalities`, `instrumental_mixture_printed_feasible` | All printed B entries correspond to the semantic response profiles via checked row/profile equivalences; all twelve H inequalities and two equalities hold for every actual IV mixture |
| Appendix B, exact IV H-representation | `Examples.Instrumental.Appendix.printed_feasible_mixture`, `printedHRep`, `instrumental_mixture_iff_printed_feasible`, `semanticHRep` | Explicit nonnegative weights reconstruct every feasible printed H vector, including boundary points; the literal and semantic-coordinate H-systems are exact; no R/cdd result is assumed |
| Appendix B, affine hull and dimension | `Examples.Instrumental.Appendix.printed_columnHull_iff`, `printed_columnHull_eq_seven`, `sevenColumn_linearIndependent`, `printed_columnHull_finrank` | The two printed normalizations describe the full signed affine hull; seven explicit response columns form an affine basis; its direction has dimension six |
| Appendix B, twelve distinct proper facets | `Examples.Instrumental.Appendix.printed_facetHull_finrank`, `printed_facets_codimension_one`, `printed_facets_distinct`, `printed_facetSpan` | Six independent incident columns per H row, strict off-plane columns and pairwise separation certify twelve distinct five-dimensional facets in the six-dimensional hull; the normalized supporting-plane identities are derived |
| Appendix B, exact eight/four classification | `Examples.Instrumental.Appendix.nonneg_slack_certificate`, `printed_facet_trivial_iff`, `printed_facet_nontrivial_iff`, `card_nonnegativeRows`, `card_nontrivialRows` | Eight rows are probability-coordinate nonnegativity, with normalization residuals only for rows 8 and 10; exactly rows 2,3,5,6 are nontrivial, by the general incidence criterion with all concrete facet data checked (one-based numbering) |
| Binary Bell example | `Examples.Bell.chsh`, `Examples.Bell.prBox_not_mem_mixture` | CHSH certificate and a normalized incompatible PR box |
| Remark `prop:ineqstructure` (ii), binary affine witness | `Examples.Bell.prBox_affine_witness` | Exact signed weights 3/16 and −1/16, affine-hull membership and polytope nonmembership |
| Remark `prop:ineqstructure` (ii), district-path geometry | `CompactDistrict.BellWitness.paths_disjoint`, `sources_ne`, `endpoints_ne`, `HiddenGraph.bell_eval_A_eq`, `bell_eval_B_eq` | Literal no-cross-reach assumptions imply distinct sources and endpoints, disjoint member paths and opposite-endpoint exclusions; actual profile evaluations are invariant when only the opposite external input varies; direct paths are included |
| Remark `prop:ineqstructure` (ii), lifted copying profiles | `CompactDistrict.BellWitness.eval_copyingProfile`, `eval_copyingProfile_at_A`, `eval_copyingProfile_at_B`, `matrix_copyingProfile` | Actual listed-parent mechanisms copy the two source bits along disjoint paths, transform only the endpoints by f and g, and set surrounding members to zero; full assignments and compatibility columns are checked on arbitrary state spaces with two chosen member levels |
| Remark `prop:ineqstructure` (ii), lifted PR-box affine identity | `CompactDistrict.BellWitness.bellTarget_at_assignment`, `bellTarget_block_probability`, `bellTarget_eq_signed_columns`, `bellTarget_mem_affineSpan_mixture` | The binary PR law is mapped to complete district assignments, with zero mass outside those assignments; normalized blocks and the exact 3/16, −1/16 combination of actual lifted columns prove affine-hull membership |
| Remark `prop:ineqstructure` (ii), full lifted Bell affine witness | `CompactDistrict.BellWitness.gameScore_le_three`, `bellTarget_gameScore`, `bellTarget_not_mem_mixture`, `bell_affine_witness` | Every actual district mixture has CHSH score at most three at four reference inputs; the target scores four; normalization, affine-hull membership and convex nonmembership are assembled, allowing extra observed state levels |
| Remark `prop:ineqstructure` (ii), actual graph nontrivial inequality | `HiddenGraph.bell_affine_witness_of_two_levels`, `bell_nontrivial_H_witness`, `bell_nontrivial_H_row` | The Bell graph structure and state cardinalities derive all level choices and a violated nontrivial H-row using `KernelTrivial`; only a checked exact district H-system is required |
| Remark `prop:ineqstructure` (ii), positive observed-law witness | `Completeness.bell_structure_positive_witness` | At c-degree ≤ 1, a strictly positive globally Markov observed law violates the selected row alone, satisfies all equalities, the other selected-district facets strictly, and all other district inequalities; uses checked affine-hull and proper/distinct facet data |
| Appendix `prop:ineqstructure`, Step 1 | `CompactDistrict.eval_eq_of_eq_on_reaching`, `HiddenGraph.eval_eq_of_eq_on_districtReaches` | Actual district profile values depend only on external inputs that reach the member through that district; changing an unreaching external input has no effect; arbitrary state spaces, with no c-degree premise |
| Remark `prop:ineqstructure` (i), path and exclusion foundation | `CompactDistrict.InstrumentalWitness.parentAssign_eq`, `outcome_eq_of_compatible`, `not_both_compatible` | Literal path/exclusion witness, including direct W→A; B is off the path, and varying W and copied intermediate values leaves B's permitted parent arguments unchanged |
| Remark `prop:ineqstructure` (i), lifted profiles and affine identity | `CompactDistrict.InstrumentalWitness.eval_copyingProfile`, `instrumentalTarget_eq_columns`, `instrumentalTarget_mem_affineSpan_mixture` | Three actual profiles copy the path through permitted observed parents and satisfy t=a+b−c on full compact rows; the target has zero/one entries and normalized external-input blocks; chosen distinct levels at district members permit arbitrary larger state spaces |
| Remark `prop:ineqstructure` (i), full lifted affine witness | `Polytope.zero_one_mixture_is_column`, `CompactDistrict.InstrumentalWitness.instrumentalTarget_not_mem_mixture`, `instrumental_affine_witness` | A zero/one mixture point must be one common column; the target's two distinct W input blocks cannot come from one profile because B's permitted parents agree; normalized blocks, affine-hull membership and convex-polytope nonmembership are checked together |
| Remark `prop:ineqstructure` (i), actual graph nontrivial inequality | `HiddenGraph.instrumental_nontrivial_H_witness`, `instrumental_nontrivial_H_row` | The literal graph structure and at-least-two-level assumptions give a violated nontrivial row of any checked exact district H-system, using the existing `KernelTrivial` definition; binary levels are derived, and irrelevant variables need only be nonempty |
| Remark `prop:ineqstructure` (i), positive observed-law witness | `Completeness.instrumental_structure_positive_witness` | At c-degree ≤ 1, a strictly positive globally Markov observed law violates the selected nontrivial row alone and satisfies every equality and all other district inequalities; uses the same checked affine-hull and proper/distinct facet data as Proposition `prop:nontrivial` (ii) |
| Independence clarification | `Examples.PairwiseIndependence.not_mutually_independent` | Author confirmed full mutual independence; the example documents why the weaker reading would not suffice |

This is **not yet a complete formalization of the paper**. The positive-law
identification and original marginal-model equivalence are checked, with the
positive and boundary iff statements using global ancestral-moral graphical
independencies in the original hidden DAG. The required cumulative ordered
equations are proved from that predicate. A general local-to-global converse
for arbitrary laws, a separate active-trail presentation and numerical V-to-H
certification are not claimed. The graph-trivial equality characterization,
rank count and sufficiency of selected spanning equality rows are checked.
The positive observed-law witness for each nontrivial facet is also checked,
under the proposition's affine-hull and distinct proper facet assumptions.
Bell path geometry, endpoint dependence and the lifted copying profiles are
checked, as are the lifted PR-box target's normalization, exact signed affine
identity, affine-hull membership and convex nonmembership by CHSH. Both
inequality-structure branches now give graph-level nontrivial H-rows and
positive observed-law witnesses under the checked H and facet data described
above. Appendix B's literal matrices and exact H-representation are checked,
including reverse reconstruction and transport to semantic IV coordinates.
The printed affine hull is exactly the two normalizations and has dimension
six, with an explicit seven-column affine basis. All twelve printed
inequalities are checked distinct proper facets of dimension five. Their
classification into eight nonnegativity and four nontrivial instrumental
facets is proved. Further concrete numerical example certificates are
deliberately skipped at the author's request; existing certificates remain.
See [plan.md](plan.md) for remaining proof obligations and
[manuscript-issues.md](manuscript-issues.md) for the audit and suggested clarifications.
No `sorry` or new axioms are used in the source. On 2026-11-04, the integrated
library and doc-gen4 build passed (3,288 jobs), and all 527 smoke-checked declarations used
only `propext`, `Classical.choice` and `Quot.sound` (or a subset).

## Build

```sh
lake exe cache get
lake build
lake env lean MeraConstraints/Test/Smoke.lean
```

The root module imports every mathematical chapter. CI builds the library,
checks for proof placeholders, and prints the axioms of the main results.
The original manuscript and reproducibility scripts remain in `sources/`.
Those R scripts provide examples to formalize; their numerical output is not
used as proof evidence.

## Literate book and API documentation

The website follows the sibling `causaloptim-lean` project: Verso renders
the literate Lean chapters directly, and doc-gen4 renders searchable
declaration signatures. Both tools are pinned to `v4.31.0`. The reading
guide organizes the manuscript results; the scope chapter states the
checked inputs, independence clarification and deliberately omitted work.

With Lean 4.31.0 and Node.js 22 or later available, build everything with:

```sh
node scripts/build-web.mjs
# Equivalently: bash build-web.sh or ./build-web.ps1
node scripts/serve-web.mjs
```

The assembled site is `_site/`; the preview server uses
`http://127.0.0.1:8000/`. Serve the site over HTTP so API search works.
The verified local site has 318 HTML pages, with 151 project API modules and
1,445 declarations. Both search interfaces and API-to-book links were
checked in the browser; all local page and asset links pass the site checker.
The build compiles the project, audits the main declarations, renders the
book, generates the project API in a single doc-gen4 prefix analysis, and
checks local links and assets. Dependency-library API pages are not bundled.
Dependency imports link to the external Mathlib API, whose version may differ
from the project's pinned release; project declarations remain local.
API source buttons lead to the corresponding literate chapter. No Git remote
is required to build or inspect the site.

On Windows, the builder detects the workspace-local Lean toolchain in
`.tools/lean-4.31.0-windows`. It supplies the `cc` name needed by native
dependencies and, when necessary, adds SHA-256-verified MSYS2 MinGW and
winpthreads headers, plus missing Clang 22.1.4 headers from a pinned LLVM
revision, inside that local toolchain. Nothing is installed globally. This
handles Lean's [documented missing-header limitation](https://github.com/leanprover/lean4/issues/10831);
the pinned packages, checksums and LLVM revision are recorded in
`scripts/setup-windows-docs.mjs`.
Other toolchain layouts need a working C compiler/SDK on their executable path.
The builder also handles Verso 4.31.0's Windows search-asset path separators
and retries a failed Windows extraction once with one Lean worker.

The book alone can also be rendered with `lake query :literateHtml`;
on Windows, use the Node builder to include the asset-path workaround.
The standard full dependency API build remains available with
`lake -R -Kenv=dev build MeraConstraints:docs`; it is much larger than the
project-only API shipped by `build-web.mjs`.

`.github/workflows/build_book.yml` builds a downloadable website artifact
on pull requests and pushes to `main`. GitHub Pages publication is an
explicit manual workflow option (`deploy=true` on `main`); set the repository's
Pages source to GitHub Actions before using that option. This task does not
publish or push a site.

`pwsh -File scripts/check-iv-appendix.ps1` checks that the Lean Appendix B
transcription matches the LaTeX and stored R output, including row order and
rcdd coefficient signs. This source audit is separate from the Lean proofs;
it neither reruns R nor certifies H sufficiency. The latter is proved in
`InstrumentalHRep.lean`. `node scripts/generate-iv-hrep.mjs` reproducibly
generates its symbolic weight certificate, whose complete output is checked
by Lean.

`node scripts/generate-iv-facets.mjs` generates integer left inverses and
incidence/separation witnesses for the twelve facets. Lean checks both the
integer identities and their correspondence to the printed real matrices.
