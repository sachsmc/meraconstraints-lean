# meraconstraints-lean

A Lean 4 formalization of **Deriving Complete Constraints in Hidden Variable Models**, by
Michael C. Sachs, Erin E. Gabriel, Robin J. Evans and Arvid Sjölander. Lean is a proof
checker: a theorem in this library has been verified by machine from its stated hypotheses.

The formalization was generated with AI assistance and then reviewed against the manuscript.
The review covered the statements of the results and what they assume. The proofs are
verified by Lean itself and were not reviewed by hand.

## Start here

**[`MeraConstraints/MainResults.lean`](MeraConstraints/MainResults.lean)** states each main
result of the manuscript as one theorem, in manuscript order. It also explains how to read a
Lean statement and has a dictionary from the manuscript's notation to Lean. No knowledge of
Lean is needed.

Other documents:

- [`correspondence.md`](correspondence.md): the supporting declarations behind each result.
- [`manuscript-issues.md`](manuscript-issues.md): where the formalization differs from the
  manuscript, and points in the manuscript the review suggests clarifying.
- [`docs/prose-style.md`](docs/prose-style.md): the vocabulary and writing guide for this library.
- [`plan.md`](plan.md): the historical working log of the formalization.

## What is proved

Numbers refer to the manuscript version of 2026-11-03 (`overleaf-version/main-revised.tex`
and `appendix.tex` in the manuscript repository). Theorem names follow the LaTeX labels.
Unless a namespace is shown, they are in `MeraConstraints.MainResults`.

| Manuscript | Lean theorem | How the Lean statement compares |
|---|---|---|
| Conditions 1, 2; Definitions 1, 2 | `HiddenGraph.Graph`, `districtOf`, `cDegree`, `graphCDegree` | Same. Condition 1 is built into the type of graph. |
| Definition 3 (response function variables) | `SCM.proposition1`, `HiddenGraph.SCM.responseProfile` | Same. Holds pointwise for any input spaces. |
| Remark 1 | `rmk1` | Same. No c-degree hypothesis, because it concerns each fixed value of the inputs. |
| Proposition 1 (`prop:ident`) | `prop_ident` | Same. The proof of `p = B r` needs no c-degree hypothesis, so the statement omits it; read it at c-degree at most 1. |
| Proposition 2 (`causalprop`) | `causalprop` | Same. The intervention is performed on the structural model. |
| Proposition 3 (`prop:complete`) | `prop_complete` | Same, with c-degree at most 1. The H-representation is a hypothesis. |
| Remark 2 (`rmk:positivity`) | `rmk_positivity` | Same. |
| Proposition 4 (i) | `prop_nontrivial_i_trivial_iff`, `prop_nontrivial_i_rank`, `prop_nontrivial_i_selected` | Same. |
| Proposition 4 (ii) | `prop_nontrivial_ii_trivial_iff`, `prop_nontrivial_ii_nonnegativity_form`, `prop_nontrivial_ii_witness`, `incidence_test` | Same. The facet and affine hull properties are hypotheses, as in the manuscript. |
| Remark 3 (`prop:ineqstructure`) | `prop_ineqstructure_i`, `prop_ineqstructure_ii` | Same. It concerns only `B` and its polytope, so the statement omits the c-degree hypothesis; read it at c-degree 1. It makes no claim about the marginal model at higher c-degree. |
| Proposition 5 (`prop:hlp`) | `prop_hlp` | Same, for variables numbered in a topological order of the larger graph. |
| Proposition 6 (`prop:strong`) | `prop_strong` | Same. The underlying proof needs a weaker form of condition 2; see `manuscript-issues.md`. |
| Remark 4 (`prop:merge`) | `prop_merge` | Same. Merges in every district. |
| Instrumental variable details (`appendix:iv`) | `Examples.Instrumental.Appendix` | The printed `B`, `H_i` and `H_e`, all 12 facets, and the split into 8 nonnegativity and 4 nontrivial rows. See the limits below. |

## What is assumed

These choices are visible in the theorem statements.

- **Finite observed variables, arbitrary unobserved ones.** Observed variables have finitely
  many values, at least one each. Unobserved inputs may take values in any measurable space.
- **Private noise.** Every observed variable also has its own independent unobserved input,
  which the graph does not draw and which does not count towards the c-degree. This is the
  manuscript's response function variable for a variable with no unobserved parent.
- **Mutual independence.** All unobserved inputs are mutually independent, as confirmed by the
  author. Pairwise independence would not be enough, as `Examples.PairwiseIndependence` shows.
- **A topological numbering.** Observed variables are numbered so that parents come first.
  Any DAG can be relabeled this way. Other orderings of a district are covered by
  `GlobalModel.OrderingInvariance`.
- **The H-representation is given.** Each result takes an H-representation with a proof that it
  describes the district polytope. Lean does not run or verify the double description method.
- **Conditional independencies.** "Implied by `𝒢`" is defined by separation in the ancestral
  moral graph, using the unobserved variables. This is a standard equivalent of d-separation.

## What is not formalized

- A verified V-to-H conversion, or the existence of an H-representation (Minkowski–Weyl).
- The equivalence of ancestral moral separation and d-separation.
- The conditional independencies at c-degree above 1. `prop_merge` concerns the district
  constraints; the manuscript's advice to take step 1 from the original graph is not formalized.
- The reductions to Conditions 1 and 2 from Evans (2016), including deleting single-child
  unobserved variables after Strong Face Splitting. So there is no single theorem chaining
  `prop_strong` into `prop_complete`.
- Any connection between the instrumental variable example and the general theorems. Its matrix
  is written out by hand and checked against response functions, but it is not derived from a
  `HiddenGraph.Graph`, so the general theorems have no worked instance in this library.
- The relation to the nested Markov model. Two pieces exist: the margin equalities of sets closed
  in the district (`District.marginal_eq_of_closedInDistrict`), proved for one district described
  on its own as a `District.Graph`, not for a `HiddenGraph.Graph`; and the example separating the
  two kinds of closure (`Examples.VermaClosure`).
- The other worked examples, tables and numerical claims in the manuscript. The R scripts are
  not used as evidence for any proof.

## Check it yourself

```sh
lake exe cache get
lake build
lake env lean MeraConstraints/Test/Smoke.lean
```

`lake build` verifies every proof. The last command prints the logical assumptions (axioms) of
the listed declarations. They should all be among `propext`, `Classical.choice` and
`Quot.sound`, the three standard ones. CI rejects `sorry`, the placeholder for an unfinished proof.

## How the library is organized

| Chapter | Content |
|---|---|
| `Guide`, `Scope`, `MainResults` | Reading guide, scope, and the main results |
| `Probability` | Finite distributions, conditionals, independence; conditional resampling |
| `SCM`, `District` | Structural equations, response functions, interventions, one district |
| `HiddenGraph` | The hidden variables DAG, structural models, moral separation, transformations |
| `GlobalModel`, `Reconstruction` | Factorization by district, the ordered local Markov property, reconstruction |
| `CompactDistrict` | The matrix `B` with rows `(v₁, v₂)`, equations (N) and (O), trivial constraints |
| `Identification`, `Completeness` | Propositions 1, 2 and 3, Remarks 2 and 4, and the transformation theorems |
| `Polytope`, `Geometry`, `EqualityConstraints`, `FacetCriterion` | General polytope and linear algebra results |
| `Examples` | Instrumental variable, Bell, Verma closure, moral collider, pairwise independence |

Finite probability, DAG, SCM and response function modules are adapted from the sibling
`causaloptim-lean` project under the Apache 2.0 license, keeping their original copyright and
author headers. That project is not a build dependency. Lean and Mathlib are pinned to v4.31.0.

## The website

The library is also rendered as a book, with an API reference. With Lean 4.31.0 and Node.js 22 or
later available:

```sh
node scripts/build-web.mjs
```

```sh
node scripts/serve-web.mjs
```

The site is written to `_site/` and served at `http://127.0.0.1:8000/`. Use the server rather than
opening the files directly, so that API search works. `.github/workflows/build_book.yml` builds a
downloadable copy on pull requests and pushes to `main`. Publishing to GitHub Pages is a manual
workflow option (`deploy=true` on `main`), which needs the repository's Pages source set to GitHub
Actions.

On Windows the builder uses the toolchain in `.tools/lean-4.31.0-windows`, and works around
[Lean's missing C headers](https://github.com/leanprover/lean4/issues/10831) by placing pinned,
checksum-verified packages inside that folder. See `scripts/setup-windows-docs.mjs`. Nothing is
installed globally.

## Checking the instrumental variable data

The manuscript sources and R scripts are not distributed with this repository. With a local copy
in `sources/`, `pwsh -File scripts/check-iv-appendix.ps1` confirms that the matrices in
`Examples/InstrumentalAppendix.lean` match the LaTeX and the stored R output, including row order
and the coefficient signs used by `rcdd`. This compares text only; the mathematics is proved in Lean.

`node scripts/generate-iv-hrep.mjs` and `node scripts/generate-iv-facets.mjs` regenerate the explicit
certificates for that example. Lean checks their output.
