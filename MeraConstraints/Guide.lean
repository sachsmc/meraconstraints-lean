/-!
# Deriving Complete Constraints in Hidden Variable Models

A literate Lean 4 companion to the manuscript by Michael C. Sachs,
Erin E. Gabriel, Robin J. Evans and Arvid Sjölander.

This book renders the checked Lean sources directly. Each mathematical
chapter places the manuscript interpretation beside the definitions and
proofs that implement it. The API documentation provides declaration-level
search, signatures and source views; use the navigation above to switch
between the two presentations.

## Start with the result you want to check

- **Response-function reduction:** SCM, then hidden-graph canonicalization;
  `SCM.proposition1` and `SCM.eval_eq_evalR`.
- **District identification, `prop:ident`:** CompactDistrict, then
  Identification; `Identification.original_measure_district_linear`.
- **Actual interventions, `causalprop`:** the original-measure identification
  chapters; `Identification.observableFactor_eq_externalInterventionLaw`.
- **Completeness, `prop:complete`:** GlobalModel, then Completeness.Graphical;
  `Completeness.original_model_iff_global_compact_HRep`.
- **Zero probabilities, `rmk:positivity`:** reconstruction boundary chapters,
  then `Completeness.original_model_iff_global_boundary_compact_HCompletion`.
- **Nontrivial constraints, `prop:nontrivial`:** EqualityConstraints and
  FacetCriterion, then CompactDistrict; `equalityTrivial_iff_rowCombination`
  and `observed_law_violating_only_facet` in the latter namespace.
- **Graph transformations:** HiddenGraph, then Completeness.HLP and
  Completeness.StrongFaceSplitting; in particular
  `Completeness.original_model_iff_strongFaceSplitting`.
- **Instrumental and Bell structures, `prop:ineqstructure`:** CompactDistrict
  path chapters, then HiddenGraph and Completeness;
  `HiddenGraph.instrumental_nontrivial_H_row` and `bell_nontrivial_H_row`.
- **Appendix B:** Examples.InstrumentalAppendix through
  InstrumentalClassification; `Examples.Instrumental.Appendix.printedHRep`
  and `printed_facet_nontrivial_iff`.

Names use the `MeraConstraints` namespace; adjacent short names share the
namespace stated in that item. The module tree and both search tools include
the full names. The full
manuscript-to-code table is retained in the repository README, available
with the roadmap and manuscript audit under the Resources navigation link.

## Read the proofs in layers

1. **Probability and SCM foundations.** Finite conditional laws, recursive
   structural evaluation and response functions fix the basic semantics.
   The original exogenous variables need not have finite state spaces.
2. **Hidden graph and district coordinates.** Graphs encode parent access,
   districts, latent roots and c-degree. Compact rows retain precisely the
   district members and their external observed parents.
3. **Identification and reconstruction.** Observable products use the
   manuscript's cumulative conditioning sets. The measurable statements
   connect these products to the original SCM and actual interventions.
4. **Completeness and boundary laws.** Global ancestral-moral graphical
   independencies, exact H-systems and reconstruction give the original-model
   equivalences, including the boundary completion rule.
5. **Equality and facet geometry.** Row combinations, direction ranks,
   incident columns and positive perturbations supply nontriviality and
   observed-law witnesses.
6. **Transformations and inequality structures.** HLP, Strong Face Splitting,
   latent merging, instrumental paths and Bell paths are connected to their
   original probability models or actual district matrices.

Within each chapter, read the informal statement and then the complete Lean
signature. Hypotheses in the signature are part of the formal result. In
particular, an exact H-representation or a codimension-one facet certificate
is checked input data where the general theorem requests it.

## A fully checked numerical example

The Appendix B sequence checks the printed eight-by-sixteen instrumental
matrix against the response profiles and proves both directions of its
H-representation. It then certifies the six-dimensional affine hull, all
twelve distinct five-dimensional facets, and the classification into eight
nonnegativity rows and four nontrivial rows. The nontrivial rows are 2, 3,
5 and 6 in the manuscript's one-based numbering. No R or cdd classification
is accepted as a proof premise.

## What this book claims

The scope chapter separates completed theorem families, explicit checked
inputs, and omitted work. Full mutual independence is the author's intended
assumption. The original manuscript files are retained unchanged; ambiguities
and clarifications are recorded in the manuscript audit.

Further concrete numerical example certificates have been deliberately
skipped at the author's request. Existing examples remain in this book,
but their presence is not a claim that every reproducibility script has a
complete Lean certificate. A general verified V-to-H conversion algorithm
is not provided.
-/
