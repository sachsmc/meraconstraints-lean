# Correspondence between the manuscript and the Lean library

This table lists the supporting declarations behind each result, grouped by the part of the manuscript they serve. For the main theorems in manuscript order, start with [`MeraConstraints/MainResults.lean`](MeraConstraints/MainResults.lean) instead.

Labels are the manuscript's LaTeX labels: `prop:ident` is Proposition 1, `causalprop` Proposition 2, `prop:complete` Proposition 3, `prop:nontrivial` Proposition 4, `prop:hlp` Proposition 5, `prop:strong` Proposition 6, `rmk1` Remark 1, `rmk:positivity` Remark 2, `prop:ineqstructure` Remark 3 and `prop:merge` Remark 4. "The instrumental variable details" are in the Supplementary Materials (`appendix:iv`). Declarations in `CompactDistrict` use the manuscript's matrix `B` with rows `(v₁, v₂)`. "Positive" means strictly positive. Lean names containing "original" refer to a structural model on the given graph with mutually independent inputs, as opposed to its response function representation.

## Graphs and districts

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Conditions 1 and 2 (`A1`, `A2`), districts and c-degree (Definitions 1 and 2) | `HiddenGraph.Graph`, `districtOf`, `cDegree`, `graphCDegree` | Districts are connected components of the graph, counting both observed and unobserved variables. |
| Districts of c-degree 0 and 1 | `connected_observed_eq_of_cDegree_zero`, `child_of_cDegree_le_one` | A district of c-degree 0 is a single observed variable; at c-degree 1 its members share one unobserved parent. |
| Structural model on the graph | `HiddenGraph.SCM`, `HiddenGraph.SCM.eval_eq_evalR` | Each variable depends only on its parents. Inputs have any type, with private noise for each observed variable. Evaluation agrees with the response function form at every input value. |
| Two kinds of closure | `HiddenGraph.fullClosed_implies_closedInDistrict`, `Examples.VermaClosure.closure_distinction` | Closed implies closed in the district. The converse fails on the manuscript's Verma graph, where paths can leave and re-enter a district. |

## Response functions and Remark 1

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Finite response function representation | `SCM.proposition1`, `SCM.eval_eq_evalR` | General results on structural models and their evaluation through response functions. |
| District with fixed external parents | `District.Graph`, `District.Profile`, `District.eval_unique` | Members' response functions depend only on their parents; given the external parents, a profile determines the members' values uniquely. |
| Shared unobserved input gives finitely many profiles | `District.responseMap_faithful`, `District.card_profile` | Each value of the unobserved inputs gives a profile, and there are finitely many profiles. The unobserved inputs need not be finite. |
| Remark 1 (`rmk1`) | `SCM.eval_intervene_eq_evalR`, `SCM.interventions_eq_of_same_profile` | The same profile gives the same observed values under every intervention on observed variables. |

## Proposition 1 and 2

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Proposition 1 (`prop:ident`) | `Identification.original_measure_district_linear` | For a measurable structural model with a positive observed distribution, the district factor is `B` times the distribution of the response function variables. |
| Proposition 2 (`causalprop`) | `Identification.districtFactor_eq_externalInterventionLaw` | With a positive observed distribution, the district factor equals the intervention distribution that sets the external parents in the structural model. No c-degree restriction. |
| District normalization and nonnegativity | `District.kernel_mem_stdSimplex` | For each value of the external parents, the entries of the district factor form a probability vector. |
| Matrix `B` with rows `(v₁, v₂)` | `CompactDistrict.matrix_project`, `districtFactor_mem_mixture_iff_HRep` | Entries of `B`, and the equivalence between the district polytope and its H-representation, use only assignments to members and external parents. |
| Product over districts | `GlobalModel.observed_eq_prod_factor` | The observed distribution is the product of the district factors. It follows from unique evaluation and independent response function variables; districts may be interleaved. |
| Factor as a product of conditionals | `GlobalModel.factor_eq_prod_prefixConditional` | A district factor is a product of conditional probabilities of its members given all earlier observed variables. |
| Conditioning sets `C_i` | `Reconstruction.conditioningVariables`, `observed_eq_prod_districtFactor` | Each conditioning set includes the external parents of every earlier district member. The ordered local Markov equations are hypotheses. |
| Identification and finite-profile models | `Identification.structuralFactor_eq_districtFactor`, `finite_profile_iff_factor_feasible` | Given the ordered local Markov equations, district factors equal the structural factors, and the finite-profile model is characterized by feasibility of the district constraints. |

## Proposition 3

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Ordered local Markov property | `GlobalModel.observed_orderedMarkov`, `prefixConditional_eq_conditioning` | Distributions generated by finite-profile models satisfy the ordered local Markov equations. |
| Completeness for finite-profile models | `Completeness.finite_source_iff_HRep` | A positive distribution comes from a finite-profile model iff it satisfies the ordered local Markov equations and the H-representation constraints. |
| Proposition 3 (`prop:complete`) | `Completeness.original_model_iff_global_compact_HRep` | For c-degree ≤ 1, a positive distribution is in the marginal model iff it has the conditional independencies implied by the graph and satisfies the H-representation constraints. |
| Realizing district distributions by a structural model | `HiddenGraph.sourceDistrictEquiv`, `sourceObserved_eq_observed` | Independent unobserved inputs and private noise correspond to distributions of the districts' response function variables. Requires c-degree ≤ 1. |
| Structural model with constant private noise | `HiddenGraph.profileSCM`, `sourceObserved_eq_profileSCM` | The realization is a structural model whose observed distribution is the given one, with constant private noise where it is not needed. |
| Probability space for the realization | `HiddenGraph.probabilityModelOfProfiles_observed` | Builds a probability space with mutually independent inputs and the given observed distribution. The model's fields contain no constraints. |
| Finite structural models and district distributions | `HiddenGraph.Canonicalization.nativeObservedLaw_eq_globalModel` | The observed distribution of a structural model with finite inputs equals that of a model with independent district profile distributions. |
| Arbitrary measurable inputs | `HiddenGraph.MeasureCanonicalization.observedLaw_eq_globalModel` | The same for arbitrary measurable inputs. No finiteness assumption; independence of the district distributions follows from that of the inputs. |
| Necessity of the H-representation constraints | `Completeness.original_measure_satisfies_compact_HRep` | Every positive distribution from a measurable structural model satisfies the district H-representations and the ordered local Markov equations. |
| Sufficiency of the H-representation constraints | `Completeness.realize_of_orderedMarkov_and_HRep` | A positive distribution satisfying the ordered local Markov equations and the H-representation constraints is reproduced by a finite-profile model. |
| Districts within a subset of observed variables | `HiddenGraph.retainedDistrictConnected_iff`, `inducedAncestralBlanket_eq` | Connection through unobserved variables, and the blanket in an ancestral set, agree with district intersection at c-degree ≤ 1. |
| Local Markov equations for ancestral sets | `GlobalModel.KernelReconstruction.joint_ancestralLocalMarkov` | Positive reconstructed distributions satisfy the local equations for every ancestral set and sink. General equivalence of local and global properties is not shown. |
| Reconstruction with all graph independencies | `GlobalModel.KernelReconstruction.reconstruct_positive_kernels_global` | At c-degree ≤ 1, positive kernels give a positive normalized distribution with all conditional independencies implied by the graph, recovering the district factors. |
| Necessity of the conditional independencies | `Completeness.probabilityModel_globalMarkov` | Distributions of measurable structural models have the conditional independencies implied by the graph, including zero probabilities and arbitrary measurable inputs. |
| From graph independencies to ordered equations | `GlobalModel.KernelReconstruction.globalMarkov_orderedMarkov` | The independencies implied by the graph give the ordered local Markov equations, for any distribution. No positivity or c-degree assumption. |
| Separation in the ancestral moral graph | `Examples.MoralCollider.roots_separated`, `roots_not_separated_given_child` | In the collider example, the two parents are separated until the child is conditioned on. |

## Remark 2

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Remark 2 (`rmk:positivity`) | `Completeness.original_model_iff_global_boundary_compact_HCompletion` | For c-degree ≤ 1, a normalized distribution, zeros allowed, is in the marginal model iff it has the graph's conditional independencies and an H-completion of its district factors exists. |
| Free entries of a district factor | `BoundaryCompletion.known_iff_allPositive_or_firstZero`, `not_known_iff_firstUndefined` | An entry is determined iff its product has all factors positive or its first non-positive factor is zero; otherwise it is free. |
| Markov equations with zero probabilities | `GlobalModel.observed_orderedMarkov_boundary`, `conditioning_supported_prefixFactor_pos_and_ratio` | The ordered local Markov equations allow zero observed probabilities. Ratios are asserted only on the support of the conditioning event. |
| Determined entries | `GlobalModel.factor_zero_of_supported_zero_conditional`, `factor_eq_prod_conditioning_of_supported` | A zero conditional probability on the support makes the whole entry zero, even if later factors are undefined. Defined entries equal their product of conditionals. |

## Proposition 4

Part (i) concerns equations, part (ii) inequalities.

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| (i), equations from closed sets | `District.marginal_eq_of_closedInDistrict` | Margins of sets closed in the district give equations, including Verma-type ones. Only sets that are closed in the graph give equations (O). |
| (i), equations (N) and (O) | `CompactDistrict.OrderingConstraints.constraints_of_mixture`, `positive_equation_iff_rowCombination` | Equations (N) and (O) for closed sets, written with the matrix `B`, using a strictly positive normalized uniform kernel. |
| (i), trivial equations | `CompactDistrict.equalityTrivial_iff_rowCombination` | At c-degree ≤ 1, an equation holds for every positive normalized distribution with the graph's independencies iff it is an affine combination of (N) and (O). |
| (i), count of nontrivial equations | `CompactDistrict.nontrivialEquality_rank_count` | The dimension of the district's equations modulo the trivial ones is a difference of ranks of stacked matrices. Assumes `H_e` defines the affine hull. |
| (i), selected equations | `CompactDistrict.selected_equalities_imply_all` | Rows of `H_e` that with (N) and (O) span all coefficients imply every district equation under the graph's independencies. Constants follow from a common column. |
| (i), reconstruction from (N) and (O) | `GlobalModel.KernelReconstruction.reconstruct_positive_kernels` | Positive kernels satisfying (N) and (O) give a positive normalized distribution with the ordered local Markov equations and these district factors. No polytope membership is assumed. |
| (i), ancestral margins | `GlobalModel.KernelReconstruction.joint_ancestral_mass` | Every ancestral-set margin is a product of district margins, also for signed kernels satisfying (N) and (O). Supplementary Materials equation `eqn:ancmargin`. |
| (i), kernels from distributions | `GlobalModel.KernelReconstruction.positive_kernel_iff_graphical_image` | At c-degree ≤ 1, a positive kernel satisfies (N) and (O) iff it is the district factor of a positive normalized distribution with the graph's independencies. |
| (i), other districts unchanged | `GlobalModel.KernelReconstruction.realize_single_kernel_other_polytopes` | A chosen positive kernel satisfying (N) and (O) is realized for one district while every other district factor stays in its polytope. |
| (i), order of the variables | `GlobalModel.OrderingInvariance.orderProduct_eq_districtFactor`, `orderProduct_eq_compact_districtFactor` | Any valid topological order gives the same district factor, on full assignments and on rows `(v₁, v₂)`, for positive distributions with the graph's independencies. |
| (i), (N) and (O) are trivial | `GlobalModel.OrderingInvariance.observable_constraints` | Every positive distribution with the graph's independencies satisfies (N) and (O) for all closed sets. No polytope membership or c-degree bound is assumed. |
| (ii), trivial inequalities | `FacetCriterion.coordinate_trivial_iff_incident_zero_of_ranks` | An inequality is trivial iff a coordinate vanishes on its facet's columns, with a positive certificate. Uses the affine hull and codimension-one facets. |
| (ii), trivial inequalities for `B` | `CompactDistrict.inequalityTrivial_iff_incident_zero`, `coordinate_certificate_of_incident_zero` | The same criterion for the matrix `B`. The affine hull equations identify the manuscript's cross-product of simplices domain. |
| (ii), violation of a nontrivial inequality | `CompactDistrict.observed_law_violating_only_facet` | At c-degree ≤ 1, a positive distribution with the graph's independencies violates one nontrivial inequality only. Assumes `H` defines the facets and affine hull. |
| (ii), incidence test | `CompactDistrict.inequality_nontrivial_iff_incidence_product_pos` | A row of `H_i` is nontrivial iff every entry of its row of `I Bᵀ` is positive. |
| (ii), facet geometry | `FacetCriterion.facetSpan_of_codimension_one`, `strict_incident_column_of_distinct_facets` | The span of a facet, and strictness on the other facets, follow from the ranks of the incident columns and distinct facet spans. |
| (ii), Supplementary Materials proof | `Geometry.average_pos_of_no_zero_coordinate`, `exists_positive_violator` | Averages over a facet are positive, and a perturbation violates one inequality while keeping the others strict and the equations. The facet structure is assumed. |

## Remark 3

Part (i) is the instrumental type, part (ii) the Bell type.

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Supplementary Materials proof, step 1 | `CompactDistrict.eval_eq_of_eq_on_reaching`, `HiddenGraph.eval_eq_of_eq_on_districtReaches` | A member's profile value depends only on external inputs that reach it through the district. Any state spaces; no c-degree assumption. |
| (i), path and exclusion | `CompactDistrict.InstrumentalWitness.parentAssign_eq`, `outcome_eq_of_compatible`, `not_both_compatible` | Includes a direct edge from W to A. B is off the path, so varying W and the copied values leaves B's parent arguments unchanged. |
| (i), profiles and affine identity | `CompactDistrict.InstrumentalWitness.eval_copyingProfile`, `instrumentalTarget_eq_columns`, `instrumentalTarget_mem_affineSpan_mixture` | Three profiles copy the path through permitted observed parents and satisfy t=a+b−c on rows `(v₁, v₂)`. The 0/1 target is in the affine hull. Larger state spaces allowed. |
| (i), affine hull and polytope | `Polytope.zero_one_mixture_is_column`, `CompactDistrict.InstrumentalWitness.instrumentalTarget_not_mem_mixture`, `instrumental_affine_witness` | A 0/1 point of the polytope is one column. The target needs two distinct W blocks that no single profile gives, so it is in the affine hull but not the polytope. |
| (i), nontrivial inequality | `HiddenGraph.instrumental_nontrivial_H_witness`, `instrumental_nontrivial_H_row` | With at least two levels, any H-representation of the district has a violated nontrivial row. Other variables need only be nonempty. |
| (i), positive distribution | `Completeness.instrumental_structure_positive_witness` | At c-degree ≤ 1, a positive distribution with the graph's independencies violates only the selected row. Uses the facet data of Proposition 4 (ii). |
| (ii), binary example | `Examples.Bell.chsh`, `Examples.Bell.prBox_not_mem_mixture` | The CHSH inequality holds on the polytope, and a normalized PR box lies outside it. |
| (ii), binary affine witness | `Examples.Bell.prBox_affine_witness` | The PR box is a signed combination of columns with weights 3/16 and −1/16, so is in the affine hull, and is not in the polytope. |
| (ii), district paths | `CompactDistrict.BellWitness.paths_disjoint`, `sources_ne`, `endpoints_ne`, `HiddenGraph.bell_eval_A_eq`, `bell_eval_B_eq` | The no-cross-reach conditions give distinct sources and endpoints and disjoint paths. Profile values are unchanged when only the opposite external input varies. Direct paths included. |
| (ii), copying profiles | `CompactDistrict.BellWitness.eval_copyingProfile`, `eval_copyingProfile_at_A`, `eval_copyingProfile_at_B`, `matrix_copyingProfile` | Profiles copy the two source bits along disjoint paths, apply f and g at the endpoints and set other members to zero. Larger state spaces allowed, with two chosen levels. |
| (ii), PR box on the district | `CompactDistrict.BellWitness.bellTarget_at_assignment`, `bellTarget_block_probability`, `bellTarget_eq_signed_columns`, `bellTarget_mem_affineSpan_mixture` | The PR box becomes a distribution on district assignments with zero mass elsewhere. It is the 3/16, −1/16 combination of columns, so lies in the affine hull. |
| (ii), affine hull and polytope | `CompactDistrict.BellWitness.gameScore_le_three`, `bellTarget_gameScore`, `bellTarget_not_mem_mixture`, `bell_affine_witness` | Every mixture has CHSH score at most three at four reference inputs; the target scores four. So it is in the affine hull but not the polytope. |
| (ii), nontrivial inequality | `HiddenGraph.bell_affine_witness_of_two_levels`, `bell_nontrivial_H_witness`, `bell_nontrivial_H_row` | The Bell structure and state counts give a violated nontrivial row of any H-representation of the district. |
| (ii), positive distribution | `Completeness.bell_structure_positive_witness` | At c-degree ≤ 1, a positive distribution with the graph's independencies violates only the selected row. Uses affine hull and distinct facet data. |

## Proposition 5

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Proposition 5 (`prop:hlp`), values of the two models | `HiddenGraph.HLP.eval_ignoreEdge`, `eval_absorb` | Structural models of the graph with and without the added edge simulate each other at every input value. Any input types; a chosen common unobserved parent. |
| Proposition 5 (`prop:hlp`), same marginal model | `Completeness.original_model_iff_HLP`, `constraint_valid_iff_HLP` | The two graphs have the same marginal model and constraints, with zero probabilities and arbitrary measurable inputs. Needs finite observed states and a common topological labeling. |

## Proposition 6

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Original and split models, values | `HiddenGraph.StrongFaceSplitting.split_eval_reproduced`, `original_eval_reproduced` | Each model reproduces the other's values at every input. Needs only Condition 1; the reverse direction uses the observed and crossing coverage conditions. |
| Resampling a candidate | `HiddenGraph.StrongFaceSplitting.localReplayAccept_iff_global`, `firstReplay_shared`, `replayModel_eval_of_consistent` | Each D vertex tests the same candidate using only permitted parents. An accepted candidate gives an evaluation of the original model with the relevant roots and private inputs resampled. |
| Acceptance as preserving C | `HiddenGraph.StrongFaceSplitting.replayAccept_iff_boundaryFiber`, `localReplayAccept_iff_boundaryFiber` | The global check, and each local check, amount to C and its observed parents being unchanged by resampling. Overlapping C sets and paths leaving and re-entering C are allowed. |
| Resampling with measurable inputs | `HiddenGraph.StrongFaceSplitting.replayBlocks_independent`, `replayAcceptanceEvent_measurable`, `replayAcceptance_ae_positive`, `replayTrials_ae_success`, `replayTrials_joint_law` | With independent inputs, measurable mechanisms and countable observed states, acceptance has positive probability almost surely and trials succeed almost surely. The joint law is the conditional one. |
| Measurability of the split model | `HiddenGraph.StrongFaceSplitting.localAcceptanceEvent_measurable`, `localFirstReplay_measurable`, `replayModel_mechanismsMeasurable`, `replayModel_eval_measurable` | The local checks, selector, split mechanisms and evaluation are jointly measurable, including inconsistent parent values and the no-acceptance fallback. No probability law is needed. |
| Coupling with the original inputs | `HiddenGraph.StrongFaceSplitting.encodeReplayStream_measurable`, `coupledReplayEval_measurable` | The common D root receives the stream of trials; other roots and private inputs keep their original values. The split evaluation is measurable on original inputs × stream. |
| Agreement on C | `HiddenGraph.StrongFaceSplitting.coupledReplayEval_boundary`, `coupledReplayAccept_iff`, `coupledReplayEval_of_success` | For every stream, the split and original models agree on C and its observed parents. A successful split output is the original evaluation after conditional resampling. |
| Independence of the split inputs | `Independent.appendInput_independent`, `HiddenGraph.StrongFaceSplitting.encodedSplitInput_independent` | All encoded split roots and private inputs are mutually independent under the product coupling, and match the structural encoding. |
| Same observed distribution | `HiddenGraph.StrongFaceSplitting.conditionalResampledInputs_map`, `coupledReplayEval_map` | Conditional resampling preserves the law of the original inputs, so the split model has the original observed distribution, including zeros. Finite observed states; measurable mechanisms. |
| Proposition 6 (`prop:strong`) | `Completeness.original_model_iff_strongFaceSplitting`, `constraint_valid_iff_strongFaceSplitting` | The two graphs have the same observational model and constraints. Needs Condition 1, finite observed states, the coverage conditions and a nonempty selected family; no c-degree or positivity assumption. The proofs use a slightly weaker form of condition 2; `ManuscriptConditions` is the printed form. |
| Resampling: selector and conditional law | `Replay.firstReplay_measurable`, `ae_exists_accepted`, `firstReplay_map_eq_cond` | The selector is measurable. Independent trials hit any fixed positive-probability measurable acceptance set almost surely, giving its conditional law. Arbitrary measurable candidate spaces. |
| Resampling: stream of trials | `Replay.trials_independent`, `trials_replay_map_eq_cond` | An infinite product probability space supplies mutually independent candidates from the original law. No finiteness, countability or standard Borel assumption. |
| Resampling with a context | `Replay.contextReplay_measurable`, `contextJoint_measurable` | A jointly measurable acceptance event on context × candidate gives a jointly measurable selector and joint output, including the no-acceptance fallback. |
| Resampling: joint law with the context | `Replay.context_replay_joint_law`, `independent_context_replay_joint_law` | The context and selected candidate have the conditional joint law, and the context marginal is unchanged. Acceptance fibers need positive probability only almost surely; this is derived for Proposition 6. |

## Remark 4

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Remark 4 (`prop:merge`) | `Completeness.original_probabilityModel_realizable_merged` | The marginal model of the original graph is inside that of the merged graph. Arbitrary measurable inputs; no positivity assumption. |

## The instrumental variable example

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Binary instrumental variable example | `Examples.Instrumental.instrumental` | The instrumental inequality holds for all mixtures of the sixteen profiles. |
| Printed matrix `B` and H-representation | `Examples.Instrumental.Appendix.printedB_eq_matrix`, `printedB_inequalities`, `printedB_equalities`, `instrumental_mixture_printed_feasible` | Every printed entry of `B` matches the response profiles. The twelve printed inequalities and two equalities hold for every mixture. |
| H-representation of the polytope | `Examples.Instrumental.Appendix.printed_feasible_mixture`, `printedHRep`, `instrumental_mixture_iff_printed_feasible`, `semanticHRep` | Every vector satisfying the printed constraints is a mixture of columns with nonnegative weights, boundary points included. The printed and profile-coordinate H-representations describe the polytope. No output of R or cdd is assumed. |
| Affine hull and dimension | `Examples.Instrumental.Appendix.printed_columnHull_iff`, `printed_columnHull_eq_seven`, `sevenColumn_linearIndependent`, `printed_columnHull_finrank` | The two printed normalizations define the whole affine hull. Seven response columns form an affine basis, so its dimension is six. |
| Twelve distinct facets | `Examples.Instrumental.Appendix.printed_facetHull_finrank`, `printed_facets_codimension_one`, `printed_facets_distinct`, `printed_facetSpan` | Each row has six independent columns on its facet, other columns strictly off it, and rows are pairwise distinct. So there are twelve distinct five-dimensional facets of a six-dimensional hull. |
| Eight trivial and four nontrivial inequalities | `Examples.Instrumental.Appendix.nonneg_slack_certificate`, `printed_facet_trivial_iff`, `printed_facet_nontrivial_iff`, `card_nonnegativeRows`, `card_nontrivialRows` | Eight rows are nonnegativity of probabilities (normalization terms only in rows 8 and 10). Rows 2, 3, 5 and 6 are nontrivial, by the incidence criterion (one-based numbering). |

## General probability and polytope results

| Manuscript component | Lean declaration | What it shows |
|---|---|---|
| Chain rule and conditioning | `FiniteProbability.assignment_eq_prod_prefixConditional`, `conditional_eq_of_independent` | The ordered chain rule, and replacing a conditioning set under independence, on the support of the conditioning event. |
| Events defined through unobserved inputs | `FiniteProbability.mass_pushforward`, `pushforward_comp`, `conditional_eq_of_fiberwise_mass` | Probabilities of event pullbacks, marginals and finite averaging. |
| Independent district distributions | `Independent.joint_mem_stdSimplex`, `rectangular_mass` | Mutual independence, not just pairwise independence, of the districts' distributions. |
| Mutual independence of the inputs | `Examples.PairwiseIndependence.not_mutually_independent` | The manuscript assumes mutual independence of the inputs. This example shows that pairwise independence would not suffice. |
| V-representation and valid inequalities | `Polytope.mixture`, `Polytope.inequality_of_columns` | The district polytope is the image of the probability simplex under `B`. A valid inequality can be certified on the columns of `B`. |
| Convex hull of the columns | `Polytope.mixture_eq_convexHull` | The district polytope is the convex hull of the columns of `B`, including matrices with repeated columns. |
| H-representation | `Polytope.HRep` | An H-representation comes with a proof that it describes the same set as the district polytope. Lean does not verify the double description computation. |
