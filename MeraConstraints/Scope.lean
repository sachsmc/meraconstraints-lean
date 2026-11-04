/-!
# Scope, assumptions and manuscript audit

This page is the boundary of the claims made by the book. A declaration's
full Lean signature is authoritative; the informal prose explains its
relationship to the manuscript.

## Completed theorem families

The development includes original-measure district identification and actual
interventions; positive and boundary marginal-model completeness at c-degree
at most one; graph-trivial equality characterization and rank count;
facet nontriviality and positive observed-law witnesses; HLP, Strong Face
Splitting and latent merging; and the instrumental and Bell inequality
structures. The original probability models allow arbitrary measurable
exogenous spaces where the theorem states this, with finite observed states.

The Strong Face Splitting equivalence uses the A1 graph setting and does not
require A2, c-degree one, strict positivity or standard-Borel original inputs.
The global graphical predicate used in the completeness results is the
ancestral-moral formulation, with the needed ordered equations derived from it.

## Checked inputs are visible in the signatures

General constraint theorems take exact `Polytope.HRep` values. Such a value
contains a proof that the halfspaces and equations are equivalent to the
response-profile mixture polytope; a numeric matrix alone is insufficient.
The positive facet-witness theorems additionally request affine-hull
exactness and proper, distinct codimension-one facet data. These inputs
are not silently inferred from R or cdd output.

The Appendix B instrumental modules provide these matrix-level certificates
explicitly, including boundary points and the eight/four facet classification.
General theorems retain their proof-carrying inputs for other instances.

## Independence and manuscript clarifications

The author confirmed that full mutual independence is intended for the
exogenous input family. The pairwise-independence example explains why the
weaker reading would not suffice. In the instrumental target description,
only intermediate path members copy the instrument; the treatment endpoint
has its separately specified value. This resolves the target-wording
ambiguity recorded in issue 10 of the manuscript audit.

The audit also records the other conditioning, graph and scope clarifications
found during formalization. Consult the complete `manuscript-issues.md`,
published in Resources, for the reasoning and source references. The
manuscript and reproducibility sources have not been rewritten to match Lean.

## Deliberately omitted or outside scope

Further concrete example certificates are skipped at the author's request.
The binary front-door certificate and the remaining R-script examples are
not publication prerequisites. The completed Appendix B certificates and
other existing checked examples remain available.

Neither correctness of a general V-to-H conversion algorithm, a separate
active-trail presentation, nor a general arbitrary-law local-to-global
Markov converse is claimed. The current theorem proofs do not depend on
those latter two extensions.

## Verification and reproducibility

The project pins Lean, Mathlib, Verso and doc-gen4 to the Lean 4.31.0 release
family, with exact dependency revisions in `lake-manifest.json`. The
mathematical build rejects proof placeholders, and the smoke audit checks
the listed main declarations for dependence only on `propext`,
`Classical.choice` and `Quot.sound`, or a subset.

The website is built from these same Lean sources. The resources include the
README correspondence table, roadmap, manuscript audit and a build record.
The book and declaration API complement one another; neither replaces the
kernel-checked source proofs.
-/
