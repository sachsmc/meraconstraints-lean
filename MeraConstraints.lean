import MeraConstraints.Probability.Finite
import MeraConstraints.Probability.Conditional
import MeraConstraints.Probability.Pushforward
import MeraConstraints.Probability.Independent
import MeraConstraints.Probability.IndependentMap
import MeraConstraints.Probability.IndependentGroupingMeasure
import MeraConstraints.Probability.MeasureFinite
import MeraConstraints.Probability.MeasureOfLaw
import MeraConstraints.SCM.Basic
import MeraConstraints.SCM.ResponseFunction
import MeraConstraints.SCM.Intervention
import MeraConstraints.HiddenGraph
import MeraConstraints.HiddenGraph.Ancestry
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
import MeraConstraints.CompactDistrict
import MeraConstraints.CompactDistrict.Observable
import MeraConstraints.CompactDistrict.OrderingConstraints
import MeraConstraints.CompactDistrict.FacetCriterion
import MeraConstraints.CompactDistrict.Incidence
import MeraConstraints.District
import MeraConstraints.Polytope
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
import MeraConstraints.Examples.Instrumental
import MeraConstraints.Examples.Bell
import MeraConstraints.Examples.BellAffine
import MeraConstraints.Examples.PairwiseIndependence
import MeraConstraints.Examples.VermaClosure

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
facet incidence criterion are checked; the positive-kernel realization argument
for graph-trivial equalities, further graph transformations, and numerical
H-conversion certification remain separate proof obligations.
-/
