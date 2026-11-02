# Review of main-revised.tex and appendix.tex

Line numbers refer to the versions of `overleaf-version/main-revised.tex` (M) and `overleaf-version/appendix.tex` (A) as first reviewed, so they no longer match the files.

**Status:** Sections 1, 2 and 4.1, 4.2, 4.4 have been applied, along with 3.1 and the mapping in 3.2, which section 2 points to. Not applied: the conjecture in 3.2, the retitling in 3.3, the letter in 3.4, the moves in 4.3, and the citation check at M684. Figures, sections and appendix letters have renumbered, so the tables in 3.4 are out of date on those points (Figures 5 and 7 in the letter are correct again).

Contents:

1. Errors to fix before this goes to coauthors
2. Smaller corrections
3. Response to the reviewers
4. Trimming (about 1,400 words and two figures from the main text)
5. What was checked, and what was not

---

## 1. Errors to fix before this goes to coauthors

### 1.1 Two proofs are missing from the Overleaf appendix

M846 says the proof of Proposition 7 is in the Appendix. It is not in `overleaf-version/appendix.tex`; it is only in the root `appendix.tex`. The short proof of Proposition 4 (`causalprop`) is also only in the root file. Copy both back.

Two improvements when you do:

**Proposition 7 can be shorter and stronger.** Step 2 of the root proof builds a distribution by hand. Proposition 6 already does this work. Replace Step 2 with:

```latex
\emph{Step 2: it suffices to find a vector $\boldsymbol{t} \in \operatorname{aff}(\mathcal{P}_D) \cap \boldsymbol{\check{P}}$ with $\boldsymbol{t} \notin \mathcal{P}_D$.} Such a vector satisfies every row of $H_e$, so it violates a row of $H_i$, and by Definition \ref{def:nontrivial} that row is nontrivial.
```

Step 1 can then drop its second fact (the margins $m_i$); only the first fact is used later, in type (ii). This saves about 300 words. In the statement (M843), replace the "More precisely" sentence with a reference to Proposition 6(ii), which gives more: a positive distribution that also satisfies the conditional independencies and every other constraint.

**Proposition 7 needs a level condition.** The proof uses at least two values for each member and for each external parent used, but the statement does not say so. With a constant $W$ the claim fails. Add "in which $A$, $B$ and the variables on the paths each have at least two levels", or state it once for all of Section 4.4.

**Proposition 4 is stated for any c-degree, but its proof uses c-degree one.** The proof of Proposition 3 relies on $T_i = \bV_1^{\leq i}$ (A298). The result still holds in general: $T_i \subseteq \bV_1^{\leq i}$, so $\boldsymbol{C}_i$ contains the Markov blanket of $V_{1i}$ and lies inside $\operatorname{pre}(V_{1i})$, and weak union gives the factor. Add that sentence, or restrict the statement to c-degree 1.

### 1.2 The e-separation paragraph is wrong in two places (M851)

**The general claim is false, and the manuscript's own example contradicts it.** M851 says that when $D$ is nonempty and $A$, $B$ are not d-separated given $C$ in the original graph, the model implies an inequality constraint. In the left graph of Figure 6, take $A = V_1$, $B = V_3$, $C = \emptyset$, $D = \{V_2\}$. These are e-separated after deleting $V_2$ and not d-separated marginally. But M776 says this graph has no inequality constraints; the e-separation only restates $V_1 \indep V_3 \mid V_2$. The chain $A \to B \to C$ is a simpler counterexample. Adding "not d-separated given $C \cup D$" does not fix it: $V_1$ and $V_3$ after deleting $\{V_2, V_4\}$ meet that stronger condition as well.

Evans's own wording is weaker: Theorem 4.2 gives a compatibility condition, and the text after it says the constraint "may be an inequality or a conditional independence" (if $D$ is empty), and that an inequality may be a weaker form of a Verma constraint.

**The Figure 6 example does not meet the theorem's hypothesis.** Theorem 4.2 requires that no vertex in $C$ is a descendant of a vertex in $D$. In "$V_1$ and $V_4$ are e-separated given $V_3$ after deleting $V_2$", $V_3$ is a child of $V_2$. Use $D = \{V_2, V_3\}$ and empty $C$. The resulting inequality is weaker than \eqref{eqn:nestedineq}, since it keeps a factor $\Pr(v_3 \mid v_2)$.

Suggested replacement for the first part of M851:

```latex
This result is related to the e-separation criterion of \citet{evans2012graphical}. Sets $A$ and $B$ are e-separated given $C$ after deleting $D$ if they are d-separated given $C$ in the graph with the nodes in $D$ removed. If, in addition, no vertex in $C$ is a descendant of a vertex in $D$, then for each value $d$ of $D$, the probabilities $\Pr(a, b, d \mid c)$ must be compatible with a distribution in which $A \indep B \mid C$ \citep[Theorem 4.2]{evans2012graphical}. This is often an inequality constraint \citep{evans2012graphical, finkelstein2021entropic}, but it need not be a new constraint: in the left graph of Figure \ref{fig:nested-ineq}, $V_1$ and $V_3$ are e-separated after deleting $V_2$, which only restates $V_1 \indep V_3 \mid V_2$. e-separation applies to graphs of any c-degree, but it gives only a sufficient condition, and it detects inequality constraints of the instrumental type: in the instrumental variable model, $Z$ and $Y$ are e-separated after deleting $X$, which yields the instrumental inequality, and in the right graph of Figure \ref{fig:nested-ineq}, $V_1$ and $V_4$ are e-separated after deleting $\{V_2, V_3\}$. As far as we can tell, it does not detect those of the Bell type. In the graph $X \rightarrow A \leftarrow U \rightarrow B \leftarrow Y$, for example, $A$ and $B$ share the unobserved $U$, which cannot be deleted, while the pairs that can be separated, such as $X$ and $B$, are marginally independent, which yields only that independence.
```

Robin should look at this paragraph, since it describes Robin's own result.

### 1.3 Appendix B misdescribes the nested Markov model (A192-A209)

This section will not survive Robin's reading:

- Equation \eqref{mbind} makes $V_k$ independent of *later* variables, in a distribution where *earlier* variables have been fixed. The ordered local Markov property runs the other way, with $V_k$ independent of earlier variables given its blanket. Fixing removes childless-in-district vertices first, which is the reverse of a topological sweep.
- The update rule at A207 (remove $V_i \to V_j$ if $V_i$ is not connected to $V_k$ through latents) is not the fixing operation, which removes edges *into* the fixed vertex.

It is also the only place that promises the fixing definition that M630 uses. Replace it with a short correct version:

```latex
\section{Nested Markov model} \label{sec:nmm}

We summarize the nested Markov model, following \citet{richardson2023nested}. A \emph{kernel} $q_{\bR}(v_{\bR} \mid v_{\bV \setminus \bR})$ is a distribution over $\bR$ for each value of the remaining variables, which are treated as fixed; in the associated graph, the edges into the fixed variables are removed. A variable $V \in \bR$ is \emph{fixable} if no other member of its district in the current graph is a descendant of $V$. Fixing $V$ divides the kernel by the conditional distribution of $V$ given the other members of its district and the parents of the district, and moves $V$ to the fixed variables. A set $\bR$ is \emph{reachable} if it can be obtained from $\bV$ by fixing one variable at a time. A distribution is in the nested Markov model if every reachable kernel obeys the global Markov property of its graph. In the discrete case, these are the only equality constraints of the marginal model \citep{evans2018margins}.

In a district of c-degree one, every subset of the members remains a single district, and fixing a member with no children among the remaining members sums over it. So the kernels reachable from the district factor are the margins $p_{\bS}$ of Section \ref{sec:nontriv}, for $\bS$ closed in the district. The example $\sum_B \Pr(D \mid A, B, C)\Pr(B \mid A) = g(D, C)$ of Section \ref{sec:nested} is such a margin, with $B$ fixed.
```

This goes from about 440 words to about 190. Please have Robin confirm the wording.

### 1.4 The 46 classes include the nonnegativity class (M1101)

M1101 says the 53,792 nontrivial inequalities fall into 46 symmetry classes. Śliwa's 46 classes cover all 53,856 facets. Class 1 in Śliwa's Table 1 has constant 1 and all single, pair and triple terms, which is $8\Pr(+,+,+) \geq 0$, the nonnegativity class. So the 53,792 fall into 45 classes. Write:

```latex
For example, the 53,856 tripartite Bell inequalities fall into 46 symmetry classes, one of which is nonnegativity \citep{Sliwa2003Symmetries}.
```

I read Table 1 through a summary of the page, so glance at the table itself to confirm. M851 ("the 46 classes in the tripartite Bell example") is fine as it stands.

### 1.5 The code in Section 6 uses an invalid vector (M1059)

The second block sums to 0.999, not 1. Your own output confirms it: `reproducibility/output/01-iv.txt` shows `FALSE` at row 14, the second normalization row, as well as at row 2, the instrumental inequality the example is meant to show. Change `0.168` to `0.169`. Row 2 stays violated ($0.548 + 0.51 = 1.058$), and row 14 passes. Update `01-iv.R` to match. A sentence saying what the output means would help the reader.

### 1.6 Merging can lose conditional independencies (M856-M868)

The Section 5 procedure merges and then runs the Algorithm, whose step 1 would list the independencies of the merged graph. These can be fewer than those of the original graph. With $U_1 \to A, B$ and $U_2 \to B, C$, the original has $A \indep C$ and the merged graph does not. Add after M868:

```latex
Step 1 of the Algorithm should still be applied to $\mathcal{G}'$, because merging can remove conditional independencies.
```

### 1.7 The proof of Remark 3 does not prove it (A502)

The proof appeals to polynomial constraints and a change of variables, and it never shows why a linear constraint of the merged model holds under the original. There is a two-line proof, and it needs no reference to Duarte et al.:

```latex
Let $U^*$ in $\mathcal{G}$ be the vector of the unobserved variables that were merged. Each observed variable in $\mathcal{G}$ can then depend on $U^*$ only through the components that are its parents in $\mathcal{G}'$, so every structural model for $\mathcal{G}'$ is a structural model for $\mathcal{G}$. Hence $\mathcal{M}(\mathcal{G}') \subseteq \mathcal{M}(\mathcal{G})$, and every constraint that holds on $\mathcal{M}(\mathcal{G})$ holds on $\mathcal{M}(\mathcal{G}')$.
```

### 1.8 The growth claim in Section 6 is off (M1064)

"Grows doubly exponentially in the number of parent categories" is not right: for one parent with $c$ categories, $|V|^{c}$ is singly exponential. Write:

```latex
This number grows exponentially in the number of parent configurations, and so doubly exponentially in the number of parents.
```

### 1.9 The intro claims a result that is not in the paper (M107)

"We also show that ... the fully characterized joint distributions are a subclass of the distributions characterized by the nested Markov model." There is no such statement anywhere, including in the original submission, which has only this sentence. What M630-M634 shows is about the equality constraints. Either state the containment with a reference to \citet{evans2018margins}, or write:

```latex
We also relate the equality constraints that we derive to the nested Markov model.
```

### 1.10 "Linear" is never connected to c-degree one (M107, Section 5 title)

The abstract and intro use "linear" and everything afterwards uses "c-degree 1". Say once that the two coincide here, for example in M107: "which in our setting are the graphs of c-degree one (Section \ref{graphmod})". Then the Section 5 title can drop "linear": "Graphs with c-degree greater than one".

---

## 2. Smaller corrections

| Line | Problem | Fix |
|---|---|---|
| M563 | Variables swapped: `Pr(Y = x, X = y \| Z = z)` | `Pr(Y = y, X = x \| Z = z)` |
| M945 | "so esides normalization", and the sentence does not parse | See 3.1 for the replacement |
| M1101 | "iequalities" | "inequalities" |
| M306 | "a undirected edge" | "an undirected edge" |
| M296 | "that remove ... and replaces" | "that remove ... and replace" |
| M125 | $\Chobs(U_i) \subseteq \bV_i$ is undefined here; "no $U_j$" should exclude $i$ | $\subseteq \bV$; "no other $U_j$" |
| M117 | Last sentence repeats the two conditions just below it | Delete |
| M128 | "a subset of another unobserved variable" | "a subset of that of another" |
| M529 | $\mathcal{G}^\dagger$ is never defined; the definition uses $\mathcal{G}(\bV, \bR)$ | Use $\mathcal{G}(\bV, \bR)$ |
| M231 | "Strong Facet-Adding rule": arXiv v2 calls it "Strong Facet-Merging" | Check against the published JCI version |
| M237 | Condition 2 says "not contained in any $C_i$"; Prop. 8 of the source says not contained in $\bigcup_i C_i$. Yours is stricter, so it is valid but narrower | Match the source: "is not contained in $\bigcup_i C_i$" |
| M403 | "and not only the observed ancestors" answers the old version; the reader has not seen it | See 4.1 |
| M511 | "Third, ... which also links ..., a pre-processing step ..., and an open-source implementation" reads as if the criterion links to the implementation; Proposition 7 is not mentioned | See below |
| M684 | \citet{pearl1995testability} is the IV paper | Check; `bhattacharya2022testability` is in your bib and is about this model |
| M824 | Ubuntu 22 here, TUXEDO OS 3 in Table 1 | Delete the machine description here; "about 19 minutes (Table 1)" |
| M830 | The final equality needs the independencies | "... $= \Pr(v_1 v_2 v_3 \mid xyz)$ under these independencies." |
| M952 | "Since $V_1$ affects $(V_4, V_5)$ only through $V_2$": under the intervention on $V_3$, it does not affect them at all | "Since $V_2$ reaches $(V_4, V_5)$ only through $V_3$, which is held fixed, $\sum_{v_2} \Pdo(\cdot)$ does not depend on $v_1$" |
| M1098 | "similar to the Verma constraints": M634 now says they *are* | "which are Verma constraints" |
| M1103 | "(Section \ref{sec:structures})" no longer supports the left-graph claim, since that paragraph was cut | See 3.2 |
| A472, A484, A490 | "Step 1(c)" but the (a)(b)(c) labels were removed from Step 1 | "Step 1" |
| A334-A384 | Notation: $\Pr(\bR_{\bV_1}=\boldsymbol{r})$ uses bold $\boldsymbol{r}$ for both vector and value; $\boldsymbol{B_j}$ vs $\boldsymbol{B}_j$; $\bR_{V^j_1}$ vs $\bR_{\bV^j_1}$; a stray "." inside the set at A420; $P$ vs $\Pr$ | Tidy |
| A387 | The sentence does not parse, and it repeats M380 | Delete the paragraph |
| Table 1 | The `[ht]` float lands on p. 47, after the references | `[!htbp]`, or place it at the end of the paragraph |
| `references.bib` | `Normaliz` has no year (BibTeX warning) | Add one |

The natbib "multiply defined" warnings come from `xr` reading the other document's `.aux`, and they are harmless.

Suggested M511, covering the Third sentence onward:

```latex
Third, we give an exact criterion for which constraints are nontrivial (Proposition \ref{prop:nontrivial}), and we use it to link the equality constraints to the nested Markov model. We also give graphical structures that guarantee inequality constraints (Proposition \ref{prop:ineqstructure}), a pre-processing step for graphs with higher c-degree, and an open-source implementation.
```

---

## 3. Response to the reviewers

| Comment | In the manuscript | Status |
|---|---|---|
| R1.1 conditioning formula, Props 2-3 | Prop. 3, proofs of 3 and 5 | Answered |
| R1.1 zero probabilities | Remark 2 and its proof | Answered; the letter describes an older version |
| R1.2 what is new | Section 2.7 | Answered, but see M511 above and "Novel" below |
| R1.2 nontrivial inequality and table | Section 5 | Answered |
| R1.3 scaling table | Table 1 | Answered; **letter box is empty** |
| R1.3 screening | Prop. 6 | Superseded; **letter describes the old rule** |
| R1.4 state the four equalities explicitly | M945 | **The display was cut, and the letter says it is there** (3.1) |
| R2.1 graphical interpretation | Prop. 7 | Answered, but the link to the examples was cut (3.2) |
| R2.2 redundancy | M1101 | Answered, can be sharper (4.3); **letter ends mid-sentence** |
| R2.3 graph criteria for differences | M1103 | Partly: needs the converse (3.2) |
| R2.4 implementation section | Section 6 | Answered, after fixing 1.5 |
| R2.5 continuous variables | M1105 | Answered |

### 3.1 R1.4: restore the display

Reviewer 1 asked you to "state the four intended equality constraints explicitly", and the letter says "These are now stated explicitly." `main-new.tex` had this display and it did not make it into `main-revised.tex`. Replace M945 with:

```latex
For the first district in the graph in Figure \ref{fig:incomp} that contains $V_1, V_3, V_6$, Proposition \ref{prop:nontrivial} finds no nontrivial constraints. Besides normalization, the equality constraints are
\[
\Pdo(V_1 = v_1, V_6 = v_6 \mid V_2 = 0) = \Pdo(V_1 = v_1, V_6 = v_6 \mid V_2 = 1), \quad v_1, v_6 \in \{0, 1\},
\]
which are of type (O) with $\bS = \{V_1, V_6\}$. The district factor is $\Pdo(v_1, v_3, v_6 \mid v_2) = \Pr(v_1)\Pr(v_6 \mid v_1)\Pr(v_3 \mid v_1, v_6, v_2)$, so $\Pdo(v_1, v_6 \mid v_2) = \Pr(v_1, v_6)$. The equalities therefore hold identically, and the inequalities reduce to nonnegativity.
```

### 3.2 R2.1 and R2.3: restore two short pieces of Section 4.4

Your cuts removed the mapping from examples to structures, and the conjecture. Most of that cut was right, but these two pieces carry weight.

**Mapping.** R2.1 asks to relate inequalities to graphical structures, and M1103 points back to Section 4.4 for the left graph of Figure 6. Add after the first sentences of M848:

```latex
Type (i) appears in the instrumental variable model, in both districts of Figure \ref{fig:seqiv}, and in the right graph of Figure \ref{fig:nested-ineq}, with $(W, A, B) = (V_1, V_2, V_4)$. Type (ii) appears in the tripartite Bell district, in $X \rightarrow A \leftarrow U \rightarrow B \leftarrow Y$, and in the district $\{B, D\}$ of $A \rightarrow B \rightarrow C \rightarrow D$ with $U \rightarrow B$ and $U \rightarrow D$. The merged second district of Figure \ref{fig:incomp} contains both. The districts in our examples without nontrivial inequality constraints contain neither: the front door model, the left graph of Figure \ref{fig:nested-ineq}, and the first district of Figure \ref{fig:incomp}.
```

`13-inequality-criterion.txt` confirms each of these classifications.

**Converse.** Without it, R2.3 is only half answered. M1103 says inequalities in one graph "can distinguish it from a candidate graph whose corresponding district contains neither structure", but Proposition 7 alone does not say that the second district lacks inequalities. Add:

```latex
We conjecture that the converse also holds, so that a district of c-degree one has inequality constraints if and only if it contains one of the two structures. We verified this for all 90 districts with two members and at most two external parents, or three members and at most one external parent, with all variables binary.
```

**Do not restore the next sentence from `main-new.tex`** ("A distribution of binary variables that is incompatible ... so this verifies the converse for these districts at all cardinalities"). The argument runs in the wrong direction. It shows that inequalities at binary levels persist at more levels. The converse needs the reverse, that no inequalities at binary levels means none at more levels. Check whether the same claim is in `13-inequality-criterion.R` or the letter.

### 3.3 "Novel Examples" (Section 4 title, M107)

Reviewer 1 wrote that recovering known IV and Bell constraints "does not show what new restrictions the method uncovers". Section 4 is then titled "Novel Examples" and contains the sequential IV inequalities (two copies of Pearl) and the tripartite Bell facets (Śliwa). Retitle it "Examples". The two examples that answer the reviewer are Figure 6, where the method separates nested Markov equivalent graphs, and Figure 8, which combines Verma and Bell-type constraints. Consider saying that plainly in Section 2.7.

### 3.4 The response letter is out of date

You did not ask me to edit it, but it is now the largest inconsistency in the package. `response-to-review.tex` follows an earlier draft:

| Letter says | Now |
|---|---|
| Prop. 1, 2, 3, 4 | Prop. 3, 4, 5, 6 |
| Prop. 6 (HLP) | Prop. 1 |
| Prop. 8, "saturated", "When does a district impose constraints?" | Prop. 7 and Section 4.4; "saturated" appears nowhere |
| Section 2.6, Section 7 (Implementation) | Section 2.7, Section 6 |
| Figure 5, Figure 7 | Figure 6, Figure 8 |
| Remark 2: limits of positive distributions, polynomial constraints | Free entries and a linear program |
| Screening: $\sum_b \max_j h_{bj} \le c$ flags "potentially nontrivial" | Prop. 6, an exact criterion |
| "We conjecture" | Not in the main text, unless you add it back |
| "under 'Comparing candidate graphs' in the Discussion" | No such heading |

Three gaps need new text: the empty R1.3 box, the unfinished R2.2 ending, and the stray comma in R2.4. The screening reply should explain why the reviewer's closed form is not used. It is correct for the product of simplices, but it depends on how the row is written (M636-M640), so Proposition 6 replaces it. R1.2 also quotes 1,118 flagged constraints; the letter should explain the change to 1,096. `reproducibility/README.md` is similarly stale in places: it mentions a referee example after Proposition 3, an inequality displayed in the first district, a conjecture, and "Redundancy" in Section 7.

---

## 4. Trimming

The main text is about 11,600 words and 47 pages. These cuts remove about 1,400 words net of the additions above, plus two figures and one long display, for about six pages. They are listed by size.

### 4.1 Cuts with replacement text

**Section 4.1, sequential IV (M688-M700): about 200 words and a half page.** Two copies of the known inequalities, and Reviewer 1 has said such recoveries are not evidence. Delete the subsection and add to the end of M650, keeping Figure 3 for the response function illustration:

```latex
The sequential instrumental variable model of Figure \ref{fig:seqiv} has the conditional independence $(V_1, V_2) \indep (V_4, V_5) \mid V_3$ and two sets of these inequalities, one for each of the districts $\{V_2, V_3\}$ and $\{V_4, V_5\}$.
```

**Discussion, continuous variables (M1105): about 170 words.**

```latex
The method is limited to DAGs with finite and discrete observed variables, though no assumptions are made about the state space of the unobserved variables. It relies on each member of a district having finitely many response functions, but two kinds of continuous variables can be handled. First, if a continuous variable $V_c$ has no observed children, as for a continuous outcome, and $g$ maps its range onto the cells of a finite partition, then $g(V_c)$ is a function of the same parents and no other structural equation changes. So $g(V_c)$ satisfies every constraint our method derives for the graph with a discrete variable in place of $V_c$. The partition-based inequalities of \citet{kedagni2020generalized} for a continuous outcome are of this type. Second, if the members of a district are discrete but an external parent $Z$ is continuous, as for a continuous instrument, we can apply the method treating $Z$ as if it took $k$ levels $z_1, \ldots, z_k$. The derivation of each resulting constraint does not depend on which values these labels stand for, so it holds for every choice of $k$ values of $Z$, or equivalently for the supremum of its left-hand side over such choices. The inequalities of \citet{kedagni2020generalized} for a continuous instrument have this form. Partitioning the range of an exogenous $Z$ and treating the cell as a categorical instrument also gives valid constraints, but weaker ones, because averaging within a cell can hide a violation between two values of $Z$ in the same cell. If a continuous variable is a parent of another member of its own district, the space of response functions is infinite-dimensional and the polytope argument does not apply. Discretizing it does not give valid constraints in general: the instrumental variable model with a continuous treatment has no testable implications \citep{gunsilius2021nontestability}, whereas the model with the treatment discretized implies the instrumental inequalities.
```

**Section 3.3, nested Markov paragraph (M630-M634): about 130 words.**

```latex
The equations (O) are nested Markov constraints, and the nontrivial equality constraints of part (i) are Verma constraints. Call a set $\bS \subseteq \bV_1$ \emph{closed in the district} if it contains every member of $D$ that is a parent of a member of $\bS$. For such a set, the members of $\bS$ are functions of $v_{\boldsymbol{E}(\bS)}$ at every column of $\boldsymbol{B}$, so $p_{\bS}$ depends on $v_2$ only through its value on $\boldsymbol{E}(\bS)$, and this is an equality constraint of $D$. These are the constraints that the nested Markov model places on the district factor: $p_{\bS}$ is the kernel obtained by fixing the members outside $\bS$, and the constraint states that it does not depend on $\bV_2 \setminus \boldsymbol{E}(\bS)$ \citep{richardson2023nested}. When $\bS$ is closed, the constraint is of type (O), and by part (i) it is implied by the ordinary conditional independencies. A set can be closed in the district but not closed, because a member can be an ancestor of another member through variables outside $D$, and then the constraint is in general a Verma constraint. In the graph $A \rightarrow B \rightarrow C \rightarrow D$ with $U \rightarrow B$ and $U \rightarrow D$, for example, the district $\{B, D\}$ has external parents $\{A, C\}$, and the set $\{D\}$ is closed in the district but not closed. Its margin is
\[
\sum_b \Pdo(B = b, D = d \mid A = a, C = c) = \sum_b \Pr(b \mid a)\Pr(d \mid a, b, c),
\]
and the constraint states that it does not depend on $a$, as in the example of Section \ref{sec:nested}. With binary variables, these are the 2 nontrivial equality constraints that part (i) finds in this district. Since the nested Markov constraints are the only equality constraints of the marginal model \citep{evans2018margins}, every nontrivial equality constraint is a Verma constraint, and in all examples in this paper, the margin equations of the sets that are closed in the district but not closed span them.
```

**Triangle (M594, M983, Figure 9): about 100 words and a figure.** The right panel of Figure 9 has one latent parent of three variables, which needs no picture. Keep the left panel only if you also want it in Section 3.2. Replace M983 with:

```latex
For the triangle scenario, merging the three unobserved variables gives a single common parent of all three observed variables, which has no nontrivial constraints. So the constraints are incomplete in this case, because of the nontrivial constraints presented in \citet{Wolfe_2019}.
```

**Front door (M652-M682, Figure 5): a figure.** Every other small example in this section is written inline. Write "the front door model $A \rightarrow M \rightarrow Y$ with $U \rightarrow A$ and $U \rightarrow Y$" at M684. Figures renumber, so keep this for last.

**Discussion, redundancy (M1101): about 70 words, and a sharper answer to R2.2.** Proposition 6(ii) already says what the reviewer asks, including the conditional independencies:

```latex
Within a district, the H-representation returned by the double description method is irredundant: each inequality defines a facet of the district polytope, and the equality constraints form a basis \citep{fukuda1996double}. By Proposition \ref{prop:nontrivial}(ii), a nontrivial inequality is also not implied by the conditional independencies together with all other constraints, including those of other districts. So the only constraints that can be removed are the trivial ones, which Proposition \ref{prop:nontrivial} identifies. For large problems, the number of constraints can be reduced further by grouping them into orbits under the symmetries of the model, such as relabelling values of a variable or permuting exchangeable nodes. For example, the 53,856 tripartite Bell inequalities fall into 46 symmetry classes, one of which is nonnegativity \citep{Sliwa2003Symmetries}.
```

### 4.2 Plain deletions

| Lines | What | Words | Why |
|---|---|---|---|
| M517 | All but the first and last ideas | 100 | Summarizes the Algorithm that follows immediately. Keep the first two sentences and the V-to-H sentence |
| M585 | All but the first sentence | 90 | Restates the proposition and its proof sketch |
| M403 | First sentence and "$\boldsymbol{C}_i$ is the smallest..." | 40 | Keep: "Under the conditional independencies implied by $\mathcal{G}$, conditioning additionally on any other variables that precede $V_{1i}$ in a topological ordering does not change the factor, but $\boldsymbol{C}_i$ cannot be made smaller in general." |
| M410 | Whole sentence | 25 | Not used again |
| M981 | Whole paragraph | 60 | Repeats M871 and Remark 3 |
| M871 | Last two sentences | 30 | Same content as Remark 3 |
| M965-M973 | The verbatim block and "Combining the first two terms" | 70 | The display at M975 is the same inequality. Keep one |
| M554-M561 | Sentence at M555 and the display at M559 | 60 | M645-M648 lists the same inequalities. The equality \eqref{eqn:ivex} can stay |
| M846 | Proof sketch | 50 | Keep "The proof is in Appendix \ref{appendix:proofs}." |
| M851 | "These form many families: ..." | 40 | Shorten to one family example |
| M856-M862 | The four-step list | 50 | One sentence: "For each district with c-degree at least 2, replace all its unobserved variables by a single unobserved parent of every member that had an unobserved parent." |
| M1064 | The IV explanation of duplicates | 50 | Keep "Different joint values of the response functions can give the same column, and these are removed before the V-to-H conversion; this reduces the ternary IV problem from 729 to 333 columns." |
| M231 | Sentences 3 and 4 | 40 | Keep "We state it in the direction that splits unobserved variables." |
| M1110 | Last sentence | 25 | Implementation already implies it |
| M107 | Overlap with Section 2.7 | 40 | M107 can leave "what is new" to Section 2.7 |

### 4.3 Structure

- **Move Section 2.3 (transformations) to Section 5.** It is 760 words of preprocessing placed before the reader has seen the method, and it forward-references "our method gives complete constraints". Section 5 then becomes "Graphs with c-degree greater than one": first reduce (Props 1 and 2), and if that fails, merge. M290 already points there. No word savings, but the setup reads straight through to Prop. 3. Propositions renumber, so do this first or last.
- **Move Section 2.7 (Relation to previous work) to the end of Section 3.** It cites Props 3, 5 and 6 before they appear. After Proposition 6 it can be read as a summary.
- **Join the IV and front door parts of Section 3.3.** M643-M650 and M684 are the same check on two models, separated by a figure if you keep it. Move both before M630, so the examples come straight after the proposition.

### 4.4 Appendix

| Lines | What | Change |
|---|---|---|
| A213-A223 | First paragraph of Appendix C | Delete; it is M412-M422 word for word. Start at "The Algorithm applied to the second district" |
| A192-A209 | Appendix B | Replace (1.3): saves 250 words |
| A502 | Proof of Remark 3 | Replace (1.7) |
| A304-A342 | $F_{1i}$, $F_{\bV_1}$ displays | Most of this is the definition of the response function recursion from Section 2.4. One sentence and the definition of $\mathcal{B}(v_1, v_2)$ are enough: about 100 words |
| A283-A293 | Restates $\Pdo$ | Delete the display: 30 words |
| A392-A423 | Restates districts, $\Delta_j$, the two inclusions | Can be shortened by about 100 words |
| A387 | Related results | Delete |
| A98-A186 | Appendix A figures | Could be replaced by a pointer to Figures 4 and 5 of \citet{evans2016graphs}, since they are adapted from there; about one page |

---

## 5. What was checked, and what was not

**Checked and correct:**

- Fig. 1 districts and c-degrees, and the Figure 2 equivalence, by reading the conditions against the graph.
- The claims about what cannot be reduced at M290.
- Propositions 3, 5 and 6, and Remark 2: I followed each proof step by step, and apart from the items above, found no gaps. This includes the swap argument in Step 1 of Prop. 6, the ancestral margin identity \eqref{eqn:ancmargin}, and the facet argument in Step 4.
- Proposition 7, root proof: the type (i) identity $\boldsymbol{t} = \boldsymbol{a} + \boldsymbol{b} - \boldsymbol{c}$ and the type (ii) weights were recomputed exactly.
- $\boldsymbol{B}$ and $H_i$ in Appendix C: rows 2, 3, 5, 6 give the displayed inequalities, and 12 distinct columns of 16.
- The Table 1 column counts by hand: 12, 28, 60, 333, 40, 48. Constraint arithmetic: 12-8=4, 48-12=36, 160-16=144, 1395-27=1368, 53856-64=53792, 64-26=38 equalities.
- Tripartite displayed inequality: maximum 0 over the 64 vertices, 41 on the facet, and no entry zero on all of them, so nontrivial.
- X→A←U→B←Y example at M636-M640, front door counts, Fig. 6 counts (6 equalities), and the 6 Verma constraints of merged Figure 8 by counting.
- Figure 8 example distribution: $7/2$, $1/256$, $7/32$ and $1/8$ all verified.
- Numbers in the text agree with the saved outputs in `reproducibility/output/` and with `table1-rows.tex`.
- Both `.tex` files compile with no undefined references.

**Not checked:**

- I did not rerun the R scripts. I read their saved output.
- Henson et al. and Evans (2016) Proposition 5 (M242), and "lines 1--8 of Algorithm 1" of Richardson et al. (M526), were not compared with the sources.
- Gunsilius (2021) was checked only through the arXiv preprint's summary. `biomet%2Fasaa003.pdf` in the root folder is Kédagni and Mourifié, not Gunsilius.
- The Ansanelli et al. comparison used arXiv v2, while your bib cites the 2026 JCI version. Numbering and names may differ there.
- Prop. 2 is not re-proved here; I only compared its statement with their Proposition 8.
