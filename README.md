<h1 align="center">S2R: Monotone Submodular Maximization with a Budget</h1>

<p align="center">An exploratory mathematical research record</p>

<p align="center">
  <strong>English</strong> · <a href="https://github.com/Haylinay/s2r-submodular-knapsack/blob/main/README.zh-CN.md">Chinese</a>
</p>

> **For reference and independent scrutiny only. This repository is an exploratory research record. The proposed proof, approximation guarantee, and resource bounds have not been independently validated and may be wrong. The correspondence between the manuscript and Lean formalization also requires independent review; a successful Lean build or audit checks only the statements encoded in the source. We do not recommend that anyone use this project as a basis for further research, implementations, applications, or other work.**

## Background

This repository documents an exploratory investigation at the intersection of AI and mathematics. Using a well-studied NP-hard optimization problem, we ask whether AI can help formulate an algorithmic idea, organize a mathematical argument, and make parts of that argument precise enough to check. The manuscript and Lean files make the proposed reasoning available for scrutiny.

The problem is **monotone submodular maximization with one budget**. Given a finite set of items $V$, a value function $f$, a positive cost $c_i$ for each item, and a budget $B\ge 0$, we seek

$$
\max_{S\subseteq V} f(S)
\qquad \text{subject to} \qquad
\sum_{i\in S} c_i \le B.
$$

The manuscript assumes $f(\varnothing)=0$. Monotonicity means that selecting more items cannot reduce value. Submodularity means diminishing returns: an item contributes no more when added to a larger selected set than when added to a smaller one. These assumptions make greedy choices worth studying, but the budget still makes the optimization problem difficult.

[Budgeted maximum coverage](https://www.sciencedirect.com/science/article/pii/S0020019099000319) is a useful example. Suppose each available item covers a group of objects and has a cost. We want to cover as many objects as possible without exceeding the budget. Once several groups have been selected, another group may add fewer *new* objects because of overlap. This is a special case of the model above and is NP-hard.

Approximation algorithms address this difficulty by seeking a feasible set whose value can be compared with the optimum. [Earlier work on this problem](https://www.sciencedirect.com/science/article/pii/S0167637703000622) already gives a $1-1/e$ approximation guarantee. The manuscript asks a narrower question: does the particular S2R construction below satisfy the same guarantee, and can its query, operation, and workspace costs be accounted for as proposed? The proposed argument has not been independently confirmed. The full bibliography is in [references.bib](references.bib).

The manuscript uses a **value-oracle model**: it counts requests for $f(S)$ while leaving the internal cost of evaluating $f$ outside the accounting. This lets the analysis focus on how many evaluations the algorithm requests. Any concrete application would need its own value function and cost model.

## Goals

**Specify the candidate procedure.** The S2R rule in [paper.tex](paper.tex) generates candidates in the following way:

1. Include the empty set and enumerate every singleton that fits the budget.
2. From each singleton seed, repeatedly choose a feasible item with the largest marginal value per unit cost. Ties use a fixed order. The path continues while an item can be added, even if its marginal gain is zero.
3. Inspect every **actual prefix** of that greedy path. At each prefix, consider adding zero, one, or two further items whenever the result stays within the budget. These additions do not restart the greedy path.
4. Return a candidate with the highest value found.

An actual prefix is a set reached by the greedy path. The continuous interpolation used later in the proof is an analytical device; it does not create extra candidates. Keeping this distinction clear matters for both the argument and the resource count.

**Examine the proposed mathematical and resource claims.** The manuscript attempts to argue that S2R returns a feasible set worth at least $(1-1/e)$ times the optimum. For $n\ge1$ items, it also proposes these bounds for an implementation described in the manuscript:

| Proposed bound | Quantity counted |
| --- | --- |
| $Q\le n^3$ | Calls to the value oracle |
| $A\le 141n^3$ | Auxiliary operations in the stated cost model |
| $P\le 66n^2$ | Peak working space in abstract words |

These numbers are **working claims to review**, not independently validated results. The resource accounting uses an exact-real, unit-cost RAM model. Oracle internals, numerical bit complexity, whole-set serialization, and Lean's evaluator heap are outside the stated bounds. The counts therefore should not be read as measured wall-clock time or physical memory use. The manuscript discusses candidate compression and processing candidate records one row at a time as part of its proposed resource analysis.

**Make the reasoning inspectable.** The Lean development encodes the optimization model, selected algorithmic constructions, an approximation statement, and a joint statement about output feasibility, value, approximation, and resources. The audit script checks named declarations and their axiom dependencies. This lets readers inspect exactly what the formal files say and compare those statements with the prose.

The mathematical claims recorded here have not been independently validated and may contain errors. A successful Lean build checks the statements encoded in Lean under their definitions and assumptions. It does not by itself show that the formal model, the intended S2R procedure, and the manuscript's natural-language argument coincide; it also does not establish novelty. Comparing these layers and checking the prior literature remain essential parts of reviewing the work.

## How to use this repository

A useful route is to understand the optimization problem, trace the candidate algorithm, compare the formal statements, and then reproduce the checks. The main files are:

| File | What it contains |
| --- | --- |
| [paper.tex](paper.tex) | English research manuscript: problem, related work, proof roadmap, S2R rule, proposed analysis, and resource model |
| [references.bib](references.bib) | Bibliographic entries cited in the manuscript |
| [verification/S2R.lean](verification/S2R.lean) | Entry point for the Lean development |
| [verification/S2R/Basic.lean](verification/S2R/Basic.lean) | Finite-set model, costs, feasibility, and value-function assumptions |
| [verification/S2R/Algorithm.lean](verification/S2R/Algorithm.lean) | Algorithmic definitions used by the formal development |
| [verification/S2R/Main.lean](verification/S2R/Main.lean) | Formal approximation statement |
| [verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) | Joint statement about output, approximation, queries, operations, and workspace |
| [verification/verify_s2r.py](verification/verify_s2r.py) | Local build and audit script for named results and axiom dependencies |
| [.github/workflows/lean.yml](.github/workflows/lean.yml) | GitHub Actions workflow that runs the Lean build and audit |

**1. Read the manuscript.** Start with the abstract, background, and proof roadmap in [paper.tex](paper.tex). Section 1 defines the model and candidate algorithm; the later proof sections develop the proposed approximation argument; Section 12 describes candidate compression and resource accounting. Use [references.bib](references.bib) to trace earlier work separately from the S2R-specific claims.

The repository keeps LaTeX and BibTeX source rather than a generated PDF. To compile a PDF locally, install a TeX distribution with XeLaTeX and BibTeX, then run these commands from the repository root:

```bash
xelatex paper.tex
bibtex paper
xelatex paper.tex
xelatex paper.tex
```

**2. Compare the formal statements.** Open [verification/S2R.lean](verification/S2R.lean) to see the imported development. [verification/S2R/Basic.lean](verification/S2R/Basic.lean) gives the instance assumptions; [verification/S2R/Algorithm.lean](verification/S2R/Algorithm.lean) defines the algorithmic objects; [verification/S2R/Main.lean](verification/S2R/Main.lean) contains the approximation theorem; and [verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) combines feasibility, value, approximation, and resource statements. Check whether the definitions of feasible sets, greedy prefixes, two-item additions, and resource counters match those used in the manuscript.

**3. Reproduce the local checks.** Install Git, Python 3, and Lean/Lake through elan. The required Lean version and Mathlib revision are recorded in [verification/lean-toolchain](verification/lean-toolchain) and [verification/lake-manifest.json](verification/lake-manifest.json). From the repository root, run:

```bash
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

The script writes a local report and logs under `verification/audit/`. That directory, downloaded dependencies, and generated PDFs are excluded from Git. The [GitHub Actions workflow](.github/workflows/lean.yml) runs the corresponding Lean build and audit for repository changes.

**4. Interpret the result.** The audit status describes the declarations and axiom dependencies that the script actually checked. Even a `COMPLETE` status is scoped to those checks. A review of the mathematical proposal should also ask whether the informal algorithm is the one encoded in Lean, whether every lemma applies under the manuscript's assumptions, whether the resource counters cover the claimed operations, and whether a counterexample exists. The repository contains no dataset, benchmark suite, or empirical performance results to reproduce.
