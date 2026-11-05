# Writing guide for prose in this library

Use this guide when writing module documentation (`/-! … -/`) and docstrings
(`/-- … -/`) in the Lean sources.

The readers are statisticians and causal inference researchers who have the
manuscript open and do not know Lean. A reader should be able to tell, from the
prose alone, which part of the manuscript a chapter corresponds to and what it
establishes. The authoritative text is the manuscript; use its words.

## Plain statements

Say what is true now, in the present tense. Do not narrate how the development grew.

- Remove history: "now", "previously", "the earlier", "already", "newly", "no longer".
- Remove stale promises: "remains a subsequent step", "not yet", "still requires",
  "will be". If the later result exists, name it. If a result is out of scope, say
  so plainly, or point to the Scope chapter.
- Remove defensive assurance: sentences such as "no X is assumed", "this is not
  defined by the desired conclusion", or "rather than silently assuming Y" exist to
  reassure rather than inform. The Lean signature shows what is assumed. Keep such a
  sentence only when the distinction would otherwise be misread, and state it directly.
- Remove these filler intensifiers unless they carry real meaning: "actual",
  "literal", "genuine", "precisely", "exact", "explicit", "checked", "concrete",
  "semantic", "faithful", "honest". "The actual district matrix" is just "the
  district matrix". ("Exact" is fine in "exact rational arithmetic".)
- Avoid metaphors and project jargon: "bridge", "transport", "oracle", "assembly",
  "boundary alignment" unless defined. Say what is shown. "Checked input" becomes
  "hypothesis" or "assumed in the theorem statement".

Keep sentences short. A module doc should have a title, a few sentences on what the
chapter contains and where it sits in the manuscript's argument, and the main idea of
the proof if it is not obvious. Most module docs need no more than two short paragraphs.
A docstring is usually one sentence saying what the declaration means in the
manuscript's terms. Do not restate the Lean signature in words when it adds nothing.
Do not add docstrings to minor helper lemmas that have none.

## Referring to the manuscript

Refer to results by name and LaTeX label, without line numbers, which go stale:

| Label | Name to use |
|---|---|
| `A1`, `A2` | Condition 1 (`A1`), Condition 2 (`A2`) |
| `def:districts`, `def:cdeg` | Definition 1 (districts), Definition 2 (c-degree) |
| `def:nontrivial` | Definition 4 (trivial constraints) |
| `rmk1` | Remark 1 |
| `prop:ident` | Proposition 1 (`prop:ident`) |
| `causalprop` | Proposition 2 (`causalprop`) |
| `prop:complete` | Proposition 3 (`prop:complete`) |
| `rmk:positivity` | Remark 2 (`rmk:positivity`) |
| `prop:nontrivial` | Proposition 4 (`prop:nontrivial`) |
| `prop:ineqstructure` | Remark 3 (`prop:ineqstructure`) |
| `prop:hlp` | Proposition 5 (`prop:hlp`) |
| `prop:strong` | Proposition 6 (`prop:strong`) |
| `prop:merge` | Remark 4 (`prop:merge`) |

"The appendix" is called "the Supplementary Materials" in the current manuscript.
"Appendix B" is "the instrumental variable details in the Supplementary Materials
(`appendix:iv`)". `prop:ineqstructure` and `prop:merge` are Remarks, not Propositions.
The manuscript no longer says that `prop:ineqstructure` produces a violating
distribution; that consequence comes from combining it with `prop:nontrivial` (ii).

## Vocabulary

| Manuscript term (use this in prose) | Avoid in prose | Lean name |
|---|---|---|
| unobserved variable | latent root, root | `Fin ℓ`, `G.children` |
| hidden variables DAG | hidden graph | `HiddenGraph.Graph` |
| observed variable | node, vertex (fine when discussing paths) | `Fin n` |
| observed distribution | observed law, positive law | `FullAssign val → ℝ` |
| distribution of the response function variables | profile law, source law | `q` |
| response function | mechanism (fine for the structural equation `F`) | `RespFun` |
| profile (one joint value of the response functions of a district's members) | | `GlobalModel.Profile` |
| district factor, `Pdo` | observable factor, observable product, kernel | `districtFactor` |
| structural model | SCM (fine once introduced), original model | `HiddenGraph.SCM` |
| marginal model | | `MainResults.MarginalModel` |
| members, external parents | outputs, inputs | `Member`, `ExternalParent` |
| conditional independencies implied by the graph | global graphical independencies | `GlobalMarkov` |
| ordered local Markov property | ordered equations | `OrderedMarkov` |
| H-representation | H-system, H-constraints | `Polytope.HRep` |
| V-representation, district polytope | mixture polytope | `Polytope.mixture` |
| matrix `B`, compatibility matrix | compact matrix | `CompactDistrict.matrix` |
| rows `(v₁, v₂)` | compact rows | `CompactDistrict.Row` |
| cross-product of probability simplices | kernel simplex | `InSimplexProduct` |
| closed, closed in the district | fully closed, internally closed | `FullClosed`, `ClosedInDistrict` |
| private noise (explain once: the observed variable's own independent input) | private disturbance | `privateNoise` |
| zero probabilities | boundary law | |

Lean names keep their current spelling in backticks. Do not invent new names in prose.
It is fine to use "kernel" when discussing nested Markov kernels, and for
`GlobalModel.KernelReconstruction`, where it means any candidate vector for a district
factor that need not come from a distribution.

Spell out why a Lean construction differs from the manuscript only when a reader
comparing the two would stumble: "The manuscript's matrix has rows `(v₁, v₂)`. Here the
rows are complete assignments, so rows repeat" is useful.

## Accuracy

Prose is checked against the signature. Never claim more than the Lean statement says.
If a statement is stronger than the manuscript (a weaker hypothesis), say so. If it is
weaker, or a hypothesis of the theorem is not in the manuscript's statement, say so.

Do not present a statement about the matrix `B` or its polytope as a result about the
model at c-degree above 1, where the district factors need not form a polytope. If a
theorem omits the manuscript's c-degree hypothesis because its proof does not use it, say
that, and say to read it in the manuscript's setting.

Keep the two kinds of closure apart, and keep the direction of the merging inclusion
(`𝓜(𝒢') ⊆ 𝓜(𝒢)`, original inside merged).

## Words the build rejects

The build and CI scan every `.lean` file, comments included, and fail on the whole
words `sorry`, `admit` and `axiom`. Do not use them in prose. Write "assumption",
"logical principle" or "unfinished proof", and "allow" or "accept" for "admit".

## Formatting

Module docs are rendered as Markdown by Verso. Use plain Markdown: headings, short
paragraphs, bullet lists, backticks. Do not use tables or raw HTML inside Lean files.
Wrap lines at about 80 to 90 characters, matching the surrounding files.
