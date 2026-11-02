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
actual interventions, and a marginal-model equivalence using the derived
ordered conditional independencies and checked compact H-representations.
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
| Original marginal-model completeness | `Completeness.original_model_iff_compact_HRep` | Actual original measurable probability models are exactly the positive laws satisfying the derived ordered equations and checked compact H-constraints, for c-degree ≤ 1 |
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
| Remark `rmk:positivity`, complete boundary rule | `Completeness.Boundary.original_model_iff_boundary_compact_HCompletion` | Actual original models, zero probabilities, compact rows and checked H-completions; c-degree ≤ 1 |
| First-zero/first-undefined classification | `BoundaryCompletion.known_iff_allPositive_or_firstZero`, `not_known_iff_firstUndefined` | The exact ordered known/free rule; reconstruction does not assume the target factorization |
| Boundary Markov and supported conditioning | `GlobalModel.observed_orderedMarkov_boundary`, `conditioning_supported_prefixFactor_pos_and_ratio` | Allows zero observed probabilities; ratios are asserted only on event support |
| Boundary known-entry soundness | `GlobalModel.factor_zero_of_supported_zero_conditional`, `factor_eq_prod_conditioning_of_supported` | A supported zero forces the whole row to zero despite later undefined factors; defined rows equal their conditional product |
| Proposition `prop:nontrivial` (i), affine step | `EqualityConstraints.positive_consequence_iff_rowCombination` | Positive feasible consequences are exactly row combinations, including their right-hand sides |
| Proposition `prop:nontrivial` (i), rank step | `EqualityConstraints.normalization_ordering_rank_count` | Quotient dimension equals the actual stacked-matrix rank difference; graph-specific triviality remains open |
| Actual (N)/(O) equations | `CompactDistrict.OrderingConstraints.constraints_of_mixture`, `positive_equation_iff_rowCombination` | Full-ancestry-closed sets, explicit compact matrices and a strictly positive normalized uniform kernel; observed-law equality-triviality remains separate |
| Proposition `prop:nontrivial` (ii), geometric criterion | `FacetCriterion.coordinate_trivial_iff_incident_zero_of_ranks` | Incidence iff and derived positive coordinate certificate from affine-hull and codimension-one facet data |
| Proposition `prop:nontrivial` (ii), actual kernel domain | `CompactDistrict.kernel_trivial_iff_incident_zero`, `coordinate_certificate_of_incident_zero` | Actual compact matrix; affine-hull normalization identifies the paper's cross-product simplex domain |
| Exact incidence-matrix test | `CompactDistrict.kernel_nontrivial_iff_incidence_product_pos` | Nontrivial precisely when every entry in the corresponding row of `I Bᵀ` is positive |
| Facet geometry | `FacetCriterion.facetSpan_of_codimension_one`, `strict_incident_column_of_distinct_facets` | Span and other-facet strictness derived from actual incidence direction ranks and distinct facet spans |
| Remark `prop:merge` | `Completeness.original_probabilityModel_realizable_merged` | Actual original model embeds in the merged model, with arbitrary measurable original inputs and no positivity requirement |
| Appendix nontriviality proof, geometric step | `Geometry.average_pos_of_no_zero_coordinate`, `exists_positive_violator` | Positive facet averages and a violating perturbation preserving other strict inequalities and affine equations; facet structure is input |
| Binary IV example | `Examples.Instrumental.instrumental` | Instrumental inequality for all sixteen-profile mixtures |
| Binary Bell example | `Examples.Bell.chsh`, `Examples.Bell.prBox_not_mem_mixture` | CHSH certificate and a normalized incompatible PR box |
| Remark `prop:ineqstructure` (ii), binary affine witness | `Examples.Bell.prBox_affine_witness` | Exact signed weights 3/16 and −1/16, affine-hull membership and polytope nonmembership |
| Independence clarification | `Examples.PairwiseIndependence.not_mutually_independent` | Author confirmed full mutual independence; the example documents why the weaker reading would not suffice |

This is **not yet a complete formalization of the paper**. The positive-law
identification and original marginal-model equivalence are checked, using an
explicit sufficient ordered set of conditional independencies. This does not
enumerate every graphical d-separation statement or verify numerical V-to-H
output. Graph-trivial equality characterization, the observed-law witness for
nontrivial facets, further graph transformations and general path-based
inequality structures remain separate milestones.
See [plan.md](plan.md) for remaining proof obligations and
[manuscript-issues.md](manuscript-issues.md) for the audit and suggested clarifications.
No `sorry` or new axioms are used in the source. On 2026-11-02, the integrated
`lake build` passed (2,321 jobs), and all 96 smoke-checked declarations used
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
