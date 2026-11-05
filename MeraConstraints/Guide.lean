/-!
# Deriving Complete Constraints in Hidden Variable Models

A companion, written in the Lean proof assistant, to the manuscript by Michael C. Sachs,
Erin E. Gabriel, Robin J. Evans and Arvid Sjölander.

This book is generated from the Lean sources, so the prose in each chapter sits beside
the definitions and proofs it describes. The API documentation offers search and
signatures for every declaration. Use the navigation above to switch between the two.

## Start with the main results

Read the chapter `MeraConstraints.MainResults` first. It states each main result as one
theorem, in manuscript order, explains how to read a Lean statement, and gives a
dictionary from the manuscript's notation to Lean. It needs no knowledge of Lean.

Theorems are named after the manuscript's LaTeX labels, and numbers below refer to the
manuscript version of 2026-11-03.

## Where each result is developed

- **Remark 1 and the response function transformation.** `SCM`, then
  `HiddenGraph.Model` and `HiddenGraph.Intervention`.
- **Proposition 1 (`prop:ident`) and Proposition 2 (`causalprop`).** `CompactDistrict` for the
  matrix `B`, `Reconstruction` for the district factor, then `Identification.OriginalMeasure`.
- **Proposition 3 (`prop:complete`).** `GlobalModel`, then `Completeness` and its subchapters,
  ending at `Completeness.Global`.
- **Remark 2 (`rmk:positivity`), zero probabilities.** `GlobalModel.BoundaryCompletion`, then
  `Completeness.Boundary`.
- **Proposition 4 (`prop:nontrivial`), trivial constraints.** `EqualityConstraints` and
  `FacetCriterion` for the general linear algebra and geometry, then
  `CompactDistrict.EqualityTriviality`, `EqualityRank` and `FacetWitness`.
- **Remark 3 (`prop:ineqstructure`), instrumental and Bell structures.** The path chapters in
  `CompactDistrict`, then `HiddenGraph.InstrumentalInequalities` and `BellInequalities`.
- **Proposition 5 (`prop:hlp`).** `HiddenGraph.HLP`, then `Completeness.HLP`.
- **Proposition 6 (`prop:strong`), Strong Face Splitting.** `HiddenGraph.StrongFaceSplitting` and
  the chapters following it, then `Completeness.StrongFaceSplitting`.
- **Remark 4 (`prop:merge`), merging.** `HiddenGraph.Merging`, then `Completeness.Merging`.
- **The instrumental variable details (`appendix:iv`).** `Examples.InstrumentalAppendix`
  through `Examples.InstrumentalClassification`.

## The layers of the argument

1. **Probability and structural equations.** Finite conditional distributions, recursive
   evaluation of structural equations, and response functions. The unobserved variables
   need not have finitely many values.
2. **The graph and its districts.** The hidden variables DAG, districts, c-degree, and the
   matrix `B` with rows `(v₁, v₂)` and one column per profile.
3. **Identification.** The district factor, with the conditioning sets `C_i` of Proposition 1,
   is shown to equal `B r` and the intervention distribution of Proposition 2.
4. **Completeness.** The conditional independencies and the H-representations characterize
   the marginal model, including distributions with zero probabilities.
5. **Trivial constraints.** Equations (N) and (O), rank counts, facets, and a distribution
   violating any chosen nontrivial inequality alone.
6. **Transformations and structures.** HLP, Strong Face Splitting, merging, and the
   instrumental and Bell structures.

## What a theorem assumes

A theorem's Lean signature is its complete statement. Every assumption appears there, so a
reader can compare it with the manuscript directly. In particular, the H-representation of
Proposition 3, and the facet properties of Proposition 4, are hypotheses. They are assumed
in the theorem statement, as they are in the manuscript, and no output of `R` or `cddlib` is
accepted as a proof.

For the instrumental variable example, those hypotheses are proved in full. The chapters
check the printed `B` against the response functions, prove both directions of the printed
H-representation, identify the 6-dimensional affine hull and all 12 distinct 5-dimensional
facets, and classify them into 8 nonnegativity rows and the 4 nontrivial rows 2, 3, 5 and 6.

The chapter `MeraConstraints.Scope` lists what is covered, what is assumed, and what is not
formalized. The audit in `manuscript-issues.md` records where the formalization and the
manuscript differ. Both are linked under Resources.
-/
