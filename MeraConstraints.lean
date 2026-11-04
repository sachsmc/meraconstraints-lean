import MeraConstraints.Probability.Finite
import MeraConstraints.Guide
import MeraConstraints.Scope
import MeraConstraints.Probability.Conditional
import MeraConstraints.Probability.AssignmentPartition
import MeraConstraints.Probability.AssignmentConditioning
import MeraConstraints.Probability.FactorizedFibers
import MeraConstraints.Probability.CutFactorization
import MeraConstraints.Probability.CoordinateJoin
import MeraConstraints.Probability.RemovalConditionals
import MeraConstraints.Probability.Pushforward
import MeraConstraints.Probability.Independent
import MeraConstraints.Probability.IndependentMap
import MeraConstraints.Probability.IndependentGroupingMeasure
import MeraConstraints.Probability.IndependentAppend
import MeraConstraints.Probability.ReplaySelection
import MeraConstraints.Probability.ReplayLaw
import MeraConstraints.Probability.ReplayTrials
import MeraConstraints.Probability.ReplayContext
import MeraConstraints.Probability.ReplayContextLaw
import MeraConstraints.Probability.ReplaySupport
import MeraConstraints.Probability.ReplayInvariance
import MeraConstraints.Probability.MeasureFinite
import MeraConstraints.Probability.MeasureOfLaw
import MeraConstraints.SCM.Basic
import MeraConstraints.SCM.ResponseFunction
import MeraConstraints.SCM.Intervention
import MeraConstraints.HiddenGraph
import MeraConstraints.HiddenGraph.Ancestry
import MeraConstraints.HiddenGraph.InequalityStructures
import MeraConstraints.HiddenGraph.BellStructure
import MeraConstraints.HiddenGraph.BellInequalities
import MeraConstraints.CompactDistrict.BellProfiles
import MeraConstraints.CompactDistrict.BellAffine
import MeraConstraints.CompactDistrict.BellNonmembership
import MeraConstraints.HiddenGraph.InstrumentalInequalities
import MeraConstraints.HiddenGraph.AncestralSets
import MeraConstraints.HiddenGraph.AncestralBlanket
import MeraConstraints.HiddenGraph.MoralSeparation
import MeraConstraints.HiddenGraph.LocalSeparation
import MeraConstraints.HiddenGraph.EliminationOrder
import MeraConstraints.HiddenGraph.CanonicalOrder
import MeraConstraints.HiddenGraph.SelectedOrder
import MeraConstraints.HiddenGraph.Model
import MeraConstraints.HiddenGraph.Components
import MeraConstraints.HiddenGraph.Realization
import MeraConstraints.HiddenGraph.SCMRealization
import MeraConstraints.HiddenGraph.Canonicalization
import MeraConstraints.HiddenGraph.Measurability
import MeraConstraints.HiddenGraph.MeasureCanonicalization
import MeraConstraints.HiddenGraph.ProbabilityModel
import MeraConstraints.HiddenGraph.MeasureRealization
import MeraConstraints.HiddenGraph.Intervention
import MeraConstraints.HiddenGraph.Merging
import MeraConstraints.HiddenGraph.StrongFaceSplitting
import MeraConstraints.HiddenGraph.RootMeasurability
import MeraConstraints.HiddenGraph.RootProbabilityModel
import MeraConstraints.HiddenGraph.StrongFaceBundling
import MeraConstraints.HiddenGraph.StrongFaceReplay
import MeraConstraints.HiddenGraph.StrongFaceReverse
import MeraConstraints.HiddenGraph.StrongFaceFibers
import MeraConstraints.HiddenGraph.StrongFaceInputs
import MeraConstraints.HiddenGraph.StrongFaceSupport
import MeraConstraints.HiddenGraph.StrongFaceMeasurability
import MeraConstraints.HiddenGraph.StrongFaceCoupling
import MeraConstraints.HiddenGraph.StrongFaceAlignment
import MeraConstraints.HiddenGraph.StrongFaceIndependence
import MeraConstraints.HiddenGraph.StrongFaceLaw
import MeraConstraints.HiddenGraph.StrongFaceNativeTransport
import MeraConstraints.HiddenGraph.HLP
import MeraConstraints.HiddenGraph.HLPEvaluation
import MeraConstraints.HiddenGraph.HLPMeasure
import MeraConstraints.HiddenGraph.HLPInputs
import MeraConstraints.CompactDistrict
import MeraConstraints.CompactDistrict.Reachability
import MeraConstraints.CompactDistrict.InstrumentalStructure
import MeraConstraints.CompactDistrict.PathCopying
import MeraConstraints.CompactDistrict.InstrumentalProfiles
import MeraConstraints.CompactDistrict.InstrumentalAffine
import MeraConstraints.CompactDistrict.InstrumentalNonmembership
import MeraConstraints.CompactDistrict.LevelChoices
import MeraConstraints.CompactDistrict.Observable
import MeraConstraints.CompactDistrict.OrderingConstraints
import MeraConstraints.CompactDistrict.EqualityTriviality
import MeraConstraints.CompactDistrict.EqualityRank
import MeraConstraints.CompactDistrict.PositiveReference
import MeraConstraints.CompactDistrict.FacetWitness
import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.CompactDistrict.Incidence
import MeraConstraints.District
import MeraConstraints.Polytope
import MeraConstraints.Polytope.ZeroOne
import MeraConstraints.Polytope.HRepAffine
import MeraConstraints.Geometry
import MeraConstraints.EqualityConstraints
import MeraConstraints.EqualityConstraints.Rank
import MeraConstraints.FacetCriterion.RankCriterion
import MeraConstraints.FacetCriterion.Incidence
import MeraConstraints.GlobalModel
import MeraConstraints.GlobalModel.Prefix
import MeraConstraints.GlobalModel.OrderedMarkov
import MeraConstraints.GlobalModel.BoundaryMarkov
import MeraConstraints.GlobalModel.BoundaryObservation
import MeraConstraints.GlobalModel.BoundaryCompletion
import MeraConstraints.GlobalModel.KernelReconstruction
import MeraConstraints.GlobalModel.KernelIdentification
import MeraConstraints.GlobalModel.AncestralKernels
import MeraConstraints.GlobalModel.AncestralMarkov
import MeraConstraints.GlobalModel.MoralMarkov
import MeraConstraints.GlobalModel.GlobalToLocal
import MeraConstraints.GlobalModel.OrderingInvariance
import MeraConstraints.GlobalModel.CanonicalProduct
import MeraConstraints.GlobalModel.AncestralProducts
import MeraConstraints.GlobalModel.ObservableMargins
import MeraConstraints.GlobalModel.ObservableConstraints
import MeraConstraints.GlobalModel.SingleKernel
import MeraConstraints.GlobalModel.SingleKernelPolytope
import MeraConstraints.Reconstruction
import MeraConstraints.Identification
import MeraConstraints.Identification.OriginalMeasure
import MeraConstraints.Completeness
import MeraConstraints.Completeness.Compact
import MeraConstraints.Completeness.OriginalFinite
import MeraConstraints.Completeness.OriginalMeasure
import MeraConstraints.Completeness.ProbabilityModel
import MeraConstraints.Completeness.Boundary
import MeraConstraints.Completeness.Merging
import MeraConstraints.Completeness.HLP
import MeraConstraints.Completeness.StrongFaceSplitting
import MeraConstraints.Completeness.InstrumentalStructure
import MeraConstraints.Completeness.BellStructure
import MeraConstraints.Completeness.Graphical
import MeraConstraints.Completeness.Global
import MeraConstraints.Examples.Instrumental
import MeraConstraints.Examples.InstrumentalAppendix
import MeraConstraints.Examples.InstrumentalExact
import MeraConstraints.Examples.InstrumentalHull
import MeraConstraints.Examples.InstrumentalFacets
import MeraConstraints.Examples.InstrumentalClassification
import MeraConstraints.Examples.Bell
import MeraConstraints.Examples.BellAffine
import MeraConstraints.Examples.PairwiseIndependence
import MeraConstraints.Examples.VermaClosure
import MeraConstraints.Examples.MoralCollider

/-!
# Deriving Complete Constraints in Hidden Variable Models

A Lean 4 development accompanying the manuscript by Michael C. Sachs,
Erin E. Gabriel, Robin J. Evans and Arvid Sjölander.

The chapters follow the response-function, matrix and polytope argument of
`sources/manuscript/main-revised.tex` and its proofs in `appendix.tex`.
The probability and SCM foundations are adapted from `causaloptim-lean`
under Apache 2.0, preserving their attribution headers.

## Reading order and semantic boundaries

1. The probability chapters develop finite conditionals and chain rules, then
   transport between arbitrary probability measures and finite response laws.
   Disjoint grouping and measurable local maps preserve full mutual independence.
2. The SCM chapters define recursive structural evaluation and prove the
   canonical response reduction preserves all observed interventions (`rmk1`).
3. `HiddenGraph` defines Conditions `A1`/`A2`, districts and c-degree.
   Canonicalization derives finite profiles from arbitrary original measurable
   inputs. `ProbabilityModel` bundles actual SCM and probability data without
   assuming any response distribution, observed constraint, or target law.
4. `GlobalModel` proves the product-event identity from recursive equations
   and independent profile laws. Its prefix chapter is a route to observable
   identification without assuming the factorization being proved.
5. `Reconstruction` uses the manuscript's exact cumulative conditioning sets.
   `GlobalModel.OrderedMarkov` derives the required ordered equations directly
   for generated finite-profile laws. `Identification` and `Completeness`
   characterize the canonical finite model by those equations and checked
   H-representations. The original-measure identification chapter equates the
   observable product with an actual surgical intervention on the given SCM.
   Compact district rows use precisely the paper's `(v₁,v₂)` coordinates.
6. `Polytope`, `Geometry`, `EqualityConstraints` and the examples provide column
   certificates, perturbation steps, affine consequences/row combinations, the
   stacked-matrix rank formula, and exact affine witnesses.

This is a developing formalization. See README.md and plan.md for exact
coverage, and manuscript-issues.md for audited wording and correspondence
issues. Boundary completion covers zero probabilities. Latent merging proves
original-to-merged model inclusion. The concrete (N)/(O) matrices and geometric
facet incidence criterion are checked. Arbitrary positive (N)/(O) kernels now
reconstruct a normalized joint law with the fixed-order Markov equations and
the prescribed observable district factors. All ancestral-set margin identities
and induced-blanket local Markov equations are checked as well. A direct graph-cut
proof now establishes all ancestral-moral graphical independencies of the
reconstructed law, using the original DAG with explicit latent roots.
Canonicalization transfers this global property to actual original probability
models, including boundary laws. Graphical separation implies the cumulative
ordered equations, so the positive and boundary marginal-model equivalences
now use the full graphical predicate. Ordering invariance of the actual
observable district factors is proved for arbitrary positive globally Markov
laws and every valid topological order. All (N)/(O) equations are proved for
arbitrary positive globally Markov laws, including every fully closed district
subset. Graph-trivial equalities are exactly their affine row combinations;
the quotient of all district equalities by these graph-trivial rows has the
manuscript's stacked-matrix rank difference. Selected equality rows spanning
that quotient imply all equality constraints together with graphical Markov.
Every nontrivial facet has a positive globally Markov observed-law witness
violating that facet alone among the district H constraints, under checked
affine-hull and genuine distinct-facet data.
The HLP edge transformation has pointwise structural simulations in both
directions and an actual original-probability-model equivalence, derived by
measurable disjoint grouping of mutually independent original inputs.
Strong Face Splitting has both pointwise structural directions and a shared
conditional-replay construction on the A1-only raw split graph. Its reverse
probability argument has a checked independent-trial conditional-law foundation
and an explicit infinite-product sampler on arbitrary measurable spaces.
Joint measurability and the joint conditional law for an independent random
context are also checked, with almost-sure positivity of acceptance fibers.
The graph's local acceptance checks are exactly equality on C and its
observed parents after resampling. For measurable original mechanisms and
countable observed states, full original input independence gives independent
replay blocks and almost-sure positive acceptance fibers. Joint acceptance
measurability, almost-sure independent-trial success and the graph-specific
conditional joint law are checked. The actual split mechanisms and evaluation
are jointly measurable, including inconsistent local parent arguments and the
no-hit fallback. The original-context/trial-stream encoding and its split
evaluation are also measurable. Boundary contexts agree for every stream;
the complete encoded root/private family is mutually independent. For finite
observed states, conditional resampling preserves the entire original input
law, and the actual split evaluation has exactly the original observed joint
law, including zero probabilities. Both directions now construct literal
bundled A1 probability models on arbitrary measurable sample/root/private
spaces. The easy direction groups the common input with exactly one anchor
root; the reverse direction derives its native input law and uses independent
conditional replay. `Completeness.original_model_iff_strongFaceSplitting` and
`constraint_valid_iff_strongFaceSplitting` prove the manuscript's same-model
and same-constraints conclusions for finite observed states, without A2,
c-degree, strict positivity or standard-Borel assumptions.
For `prop:ineqstructure`, district-restricted reachability and profile
dependence only on external inputs that reach the member are checked. The literal
instrumental-type path witness supplies the excluded-parent obstruction for
the actual compact rows, including the direct path case. Its copying profiles
use actual listed parents, have checked evaluations on arbitrary member state
spaces with two chosen levels, and give the full-row identity t = a + b - c.
The zero/one target has normalized blocks and lies in the affine span of the
actual district mixture polytope. With distinct W and B levels, its two
reference input blocks cannot come from one profile. A zero/one mixture
point would be a single column, so the target lies outside the convex
polytope. The combined instrumental affine witness is checked. State
cardinalities supply the level choices, and any checked exact H-system gives
a nontrivial inequality row in the actual hidden-graph district. At c-degree
at most one, checked affine-hull and genuine distinct-facet data then give
a strictly positive globally Markov observed law violating that row alone.
This assembles the instrumental branch of `prop:ineqstructure`. Bell path
geometry is checked: no-cross reachability implies distinct sources and
endpoints, disjoint member paths and exclusion of opposite endpoints. Actual
profile evaluations at A and B are invariant under changing the opposite
external input alone. Lifted Bell profiles read actual listed parents on the
two paths and have checked full evaluations A=f(alpha), B=g(beta), with each
intermediate copying its own source bit and all other members zero. The
lifted PR-box target is normalized on every external-input block, has the
exact signed 3/16 and -1/16 column combination, and belongs to the actual
district polytope's affine hull. At four reference external inputs every
district mixture has CHSH score at most three, while the lifted target has
score four. The normalized affine witness outside the convex polytope is
assembled. State cardinalities supply both source levels and all member
levels, and every checked exact H-system has a nontrivial Bell inequality
row. At c-degree at most one, the same checked affine-hull and proper,
distinct facet data give a strictly positive globally Markov observed law
violating that row alone. This assembles both branches of `prop:ineqstructure`
under those checked inputs. Numerical H-conversion certification remains
a separate obligation. For Appendix B, the literal IV B matrix is checked
against all sixteen semantic response profiles via row/profile equivalences.
All twelve printed H inequalities and both equalities hold on every column
and every actual IV mixture. A symbolic bound certificate reconstructs
nonnegative profile weights from every feasible H vector, including boundary
points. Both the literal printed H-system and its semantic-coordinate
transport are bundled as exact HRep values. The printed matrix's affine hull
is exactly the two normalization equations, including signed points. Seven
explicit columns form an affine basis, and the direction dimension is six.
For each of the twelve H inequalities, six independent incident columns and
a strict off-plane column certify a proper facet of dimension five. Exact
column witnesses separate every pair of facets, and their normalized
supporting-plane identities are derived. Explicit normalization-residual
certificates identify eight nonnegativity facets; the general coordinate-
incidence criterion proves exactly rows 2,3,5,6 (one-based) nontrivial.
Further numerical examples remain separate obligations.
-/
