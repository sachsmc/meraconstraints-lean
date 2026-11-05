# Comparing the formalization with the manuscript

This file records where the Lean formalization and the manuscript differ, why, and what the
manuscript might clarify. It compares against the version of 2026-11-03
(`overleaf-version/main-revised.tex` and `appendix.tex` in the manuscript repository).
Results are cited by LaTeX label. Numbers: `prop:ident` 1, `causalprop` 2, `prop:complete` 3,
`prop:nontrivial` 4, `prop:hlp` 5, `prop:strong` 6, and the remarks `rmk1` 1, `rmk:positivity` 2,
`prop:ineqstructure` 3, `prop:merge` 4.

No counterexample to any result in the manuscript was found. The manuscript has not been edited.

## 1. Differences between the Lean statements and the manuscript

### Proposition 6 (`prop:strong`), condition 2: Lean proves a stronger result

The manuscript requires `D ⊆ Chobs(U_j)` for every other unobserved `U_j` whose children meet
`⋃ C_i` and are "not contained in any `C_i`". The proofs in Lean use a weaker hypothesis, requiring
this only when the children are not contained in the union `⋃ C_i`. An unobserved variable whose
children all lie in `⋃ C_i`, but not in a single `C_i`, is exempt.

This is the wording of the earlier manuscript draft. The 2026-11-03 revision changed it to match
Ansanelli et al. (arXiv v3), and `sweep-findings.md` notes that the wider condition "is not claimed by
the current paper". The Lean proof establishes the wider version without relying on that paper. The
printed proposition is an immediate consequence, and the two are connected in Lean:

- `StrongFaceSplitting.ManuscriptConditions` is the printed version, and
  `ManuscriptConditions.toConditions` shows that it implies `Conditions`.
- `MainResults.prop_strong` is stated with the printed version.

**Suggestion.** Keep the printed condition, which matches the citation. If useful, a footnote could
say that the union form is also sufficient, with the Lean proof as the reference. A person should read
the replay argument in `HiddenGraph/StrongFaceReverse.lean` before claiming this in print.

Why the wider version is plausible: an unobserved variable whose children all lie in `⋃ C_i` has no
child in `D`, so it can be resampled together with the selected variables, and `D` never needs its value.

### Lean statements without the manuscript's c-degree hypothesis

These Lean statements omit the hypothesis because their proofs do not use it. They imply the
manuscript's statements and should be read in the manuscript's setting. They make no claim about the
marginal model at higher c-degree, whose district factors need not form a polytope.

- `rmk1`: it concerns each fixed value of the unobserved inputs.
- `prop:ident`: the proof of `p = B r`, where `r` is the induced distribution of the response function
  variables, does not use the bound. The bound is what makes every probability vector `r` possible, so
  that the district factors form the district polytope. Lean assumes it at that step.
- `prop:nontrivial` (ii), first two claims, and `prop:ineqstructure`: these concern only the matrix `B`
  and its polytope.

`prop:hlp` and `prop:strong` assume neither positivity nor a c-degree bound, as in the manuscript.
`prop:strong` does not need `A2`.

### Choices made in the formal statements

- **"c-degree at most 1".** Where the manuscript says a graph "has c-degree 1", Lean assumes at most 1,
  which also covers a graph with no unobserved variables. `prop:ident` already says "at most 1".
- **`MainResults.MarginalModel` includes zero probabilities.** In `prop:complete`, the manuscript's
  `𝓜(𝒢)` denotes the strictly positive distributions in the marginal model. Lean states positivity as
  a hypothesis on `p` instead. The two statements are the same.
- **`prop:merge` merges in every district.** A district of c-degree 1 is unchanged by this.
- **The ordering is the numbering.** The manuscript allows any ordering of a district consistent
  with a topological ordering. Lean numbers the variables topologically and uses numeric order.
  `GlobalModel.OrderingInvariance` shows the district factor does not depend on the ordering, for
  distributions with the conditional independencies.
- **`prop:hlp` is stated for a graph and the graph with one added edge**, numbered in a topological
  order of the larger graph, rather than for a pair of graphs.

## 2. Points the manuscript might clarify

None of these is an error in the intended result.

### Independence of response function variables is mutual, not pairwise

After the response function variable transformation, the manuscript says `Pr(R_{V_i} = a, R_{V_j} = b)`
factorizes when `R_{V_i}` and `R_{V_j}` have no undirected edge. The proofs of `prop:complete` and
`prop:nontrivial` use more: response vectors of distinct districts are mutually independent. The
author has confirmed that this is intended, and Lean uses it. Pairwise independence would not be
enough. If `R₁`, `R₂` are independent fair bits and `R₃ = R₁ xor R₂`, every pair is independent, but
`(0, 0, 1)` has probability zero rather than `1/8` (`Examples.PairwiseIndependence`).

**Suggestion.** After the transformation, add that the joint distribution factorizes as
`P(R) = ∏_D P(R_D)`, with arbitrary joint distributions within districts.

### Private noise at observed variables

The manuscript calls the model an NPSEM and removes hidden variables with fewer than two children
(`A2`), yet introduces a response function variable for every observed variable, with an arbitrary
distribution. These agree only if each observed variable keeps its own independent noise, which the
graph does not draw. Read as a deterministic system with only the drawn hidden variables, a single
observed root with no hidden parent could only be a point mass. Lean makes this noise explicit
(`HiddenGraph.SCM.privateNoise`) and does not count it towards the c-degree.

**Suggestion.** State once that each observed variable has an implicit independent disturbance, which
does not affect child sets or the c-degree.

### `k ≥ 1` in Proposition 6

The statement allows `k = 0` as written. Then the conditions are vacuous, yet the transformation would
add a new common cause of `D`, which could change the model. The instruction to choose `U_1, …, U_k`
with a child in common shows the intended reading. Lean requires a selected variable
(`selected_nonempty`). Stating `k ≥ 1` would remove the ambiguity.

### Conditional independencies at higher c-degree

`prop:merge` advises taking step 1 of the algorithm from the original graph. Lean only proves that
structural models satisfy the conditional independencies at c-degree at most 1
(`Completeness.probabilityModel_globalMarkov`). The result at higher c-degree is standard and cited in the
manuscript, but is not formalized here.

## 3. Items in earlier audits that the current manuscript resolves

Earlier versions of this file raised these against an older copy of the manuscript.

- `prop:ident` assumed c-degree 1, though the proof of `prop:complete` used it for every district,
  including singletons. It now says "at most 1".
- In the proof of `prop:ineqstructure`, the target `t` read as if `A` equals `ζ`. The Supplementary
  Materials now say that `Z_1, …, Z_r` equal `ζ` and `A = 0`.
- `prop:ineqstructure` ended with a claim about a violating distribution, from `prop:nontrivial` (ii).
  This has been removed from the remark. Lean retains it as the two theorems
  `Completeness.instrumental_structure_positive_witness` and `bell_structure_positive_witness`,
  whose extra hypotheses are the facet properties of `prop:nontrivial`.

## 4. Readings to preserve

These are not problems, but are easy to get wrong, and the Lean definitions follow them closely.

- **Two kinds of closure.** A set is *closed* if it contains every member of its district that is an
  ancestor of one of its members, along paths that may leave the district. *Closed in the district*
  concerns only parents within the district. Equations (O) use the first, and Verma constraints can
  arise from the second. In `V_1 → V_2 → V_3 → V_4` with `U → V_2, V_4`, the set `{V_4}` is closed in
  the district but not closed (`Examples.VermaClosure`).
- **The conditioning sets are cumulative.** `C_i` contains the external parents of `V_{1i}` and of every
  earlier member, not only those of `V_{1i}` (`Reconstruction.conditioningVariables`).
- **The direction of merging.** `𝓜(𝒢') ⊆ 𝓜(𝒢)`, with `𝒢'` the original and `𝒢` the merged graph.
  The manuscript's sentence that an observed variable depends on the merged variable only through its
  old parents describes the embedding of an original model, and does not restrict merged models.
- **Strong Face Splitting needs only `A1`.** The split graph can contain unobserved variables with one or
  no children, or nested child sets, until the later reductions restore `A2`. Lean uses a separate type
  of graph for this, `StrongFaceSplitting.RootGraph`.
- **Positivity.** The positive-distribution results rely on the standing assumption in the Notation
  section, and `rmk:positivity` handles zero probabilities. Individual statements need not repeat it.
- **Finiteness in the perturbation argument.** The perturbation in the proof of `prop:nontrivial` (ii)
  needs finitely many other inequalities. This holds for an H-representation, and
  `Geometry.exists_positive_violator` assumes it.

## 5. How conditional independencies are specified

The global Markov property in Lean (`GlobalMarkov`) quantifies over disjoint sets `X`, `Y`, `Z` of observed
variables that are separated in the ancestral moral graph of the hidden variables DAG. This graph includes
the unobserved variables and is the standard alternative to d-separation
([Pearl and Dechter](https://ics.uci.edu/~dechter/publications/indep-causal-graph-feedback.pdf), Section 2.1).
No theorem from that paper is used in a proof. `Examples.MoralCollider` confirms the expected behavior
on a collider. A definition by active trails, and its equivalence with this one, are not formalized.

Lean proves that separation implies the manuscript's ordered local Markov property for any distribution
(`globalMarkov_orderedMarkov`). It does not prove the converse for an arbitrary distribution, which the
proofs do not need. The direction it needs, that the reconstructed distribution satisfies the global
property, is proved directly by cutting the moral graph.

## 6. The instrumental variable example

The entries of `B`, `H_i`, `H_e`, `b_i` and `b_e` in `Examples/InstrumentalAppendix.lean` match the
Supplementary Materials and the stored output of `01-iv.R`. The printed rows are ordered by `(X, Y, Z)`;
`rcdd` prints coefficients with the opposite sign. Lean proves the printed H-representation exact in both
directions, the affine hull has dimension 6, the 12 rows are distinct facets of dimension 5, and rows
2, 3, 5 and 6 are exactly the nontrivial ones. No discrepancy was found.

The example is not connected to the general theorems, however. Its matrix is written out and checked
against response functions, rather than obtained from a `HiddenGraph.Graph` for the instrumental variable
DAG. See the Scope chapter.
