/-!
# Scope, assumptions and what is not formalized

This page says what the library claims. The full Lean signature of a theorem is its
authoritative statement; the prose explains how it relates to the manuscript.

## What is formalized

- Propositions 1 and 2: the district factor equals `B r` and the intervention distribution.
- Proposition 3 and Remark 2: the marginal model at c-degree at most 1, with and without
  zero probabilities.
- Proposition 4: the characterization and count of trivial equality constraints, the
  criterion for trivial inequalities, and a distribution violating a nontrivial one alone.
- Remark 3: instrumental and Bell structures imply a nontrivial inequality.
- Propositions 5 and 6: HLP and Strong Face Splitting preserve the marginal model.
- Remark 4: merging gives a marginal model containing the original one.
- The instrumental variable details: the printed matrices and the facet classification.

`MeraConstraints.MainResults` states each of these in manuscript order, and says where a
statement is stronger than the manuscript's.

## Modeling choices

- Observed variables have finitely many values. Unobserved variables may take values in
  any measurable space.
- All unobserved inputs are mutually independent, as confirmed by the author. Pairwise
  independence would not suffice, as `Examples.PairwiseIndependence` shows.
- Each observed variable has its own independent private input, which the graph does not
  draw. It plays the role of the manuscript's response function variable for a variable
  with no unobserved parent, and does not count towards the c-degree.
- Observed variables are numbered in a topological order. Any DAG can be relabeled this way.
- Conditional independencies "implied by the graph" are defined by separation in the
  ancestral moral graph, which includes the unobserved variables.

## Hypotheses in the theorem statements

General theorems take a value of `Polytope.HRep`, which contains a proof that the
inequalities and equations describe the district polytope. A numeric matrix alone does not
provide one. The results on facets in addition assume the properties in
`MainResults.DefinesFacetsAndHull`, which are the manuscript's assumption that each row of
`H_i` defines a different facet and the rows of `H_e` define the affine hull.

The instrumental variable chapters prove all of these for the printed matrices.

## Differences from the manuscript

- Some Lean statements have no c-degree hypothesis, although the manuscript assumes
  c-degree at most 1: Remark 1, Proposition 1, parts of Proposition 4, and Remark 3. Their
  proofs concern fixed values of the inputs or the matrix `B` alone. Read them in the
  manuscript's setting. They make no claim about the marginal model at higher c-degree,
  whose district factors need not form a polytope.
- Proposition 6 is proved under a weaker form of its condition 2, so the printed version
  follows from it. See `HiddenGraph.StrongFaceSplitting.Conditions`.

The audit in `manuscript-issues.md` gives details. The manuscript and the reproducibility
scripts have not been changed to match Lean.

## Not formalized

- A verified V-to-H conversion, or the existence of an H-representation (Minkowski–Weyl).
- The equivalence of ancestral moral separation with d-separation, and the implication from
  an arbitrary distribution's local Markov property to the global one. No proof depends on these.
- The conditional independencies at c-degree above 1.
- The reductions to Conditions 1 and 2 from the literature, including deleting single-child
  unobserved variables after Strong Face Splitting. Consequently no single theorem chains
  Proposition 6 into Proposition 3.
- A connection between the instrumental variable example and the general theorems. Its matrix
  is written out by hand and checked against response functions, but is not derived from a
  `HiddenGraph.Graph`, so the general theorems have no worked instance in this library.
- The relation to the nested Markov model. Two pieces exist: the margin equalities of sets closed
  in the district, proved for one district described on its own as a `District.Graph` rather than
  for a `HiddenGraph.Graph`, and the example separating the two kinds of closure.
- The other worked examples and numerical claims in the manuscript, such as the front door
  model, the tripartite Bell counts, and Table 1. Further numerical certificates were skipped
  at the author's request. The R scripts are not used as evidence for any proof.

## Verification

The project pins Lean, Mathlib, Verso and doc-gen4 to the Lean 4.31.0 release family, with
exact revisions in `lake-manifest.json`. The build rejects unfinished proofs. The file
`MeraConstraints/Test/Smoke.lean` checks that the listed declarations depend only on the
standard logical principles `propext`, `Classical.choice` and `Quot.sound`.
-/
