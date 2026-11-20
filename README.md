<h1 align="center">S2R: Submodular Knapsack Exploration</h1>

<p align="center">
  <strong>English</strong> · <a href="https://github.com/Haylinay/s2r-submodular-knapsack/blob/main/README.zh-CN.md">简体中文</a>
</p>

## Background

This repository grew out of a course report on AI and mathematical research. As the two become more closely connected, we chose a concrete NP-hard optimization problem to explore how AI might help propose an approach, organize an argument, and turn parts of that argument into statements that can be checked. The repository records this attempt and the questions it leaves open.

The problem is monotone submodular maximization under a single knapsack constraint. Each item has a cost, and the task is to choose a set within a budget whose value is as large as possible. Submodularity captures diminishing returns: adding an item cannot become more valuable as the chosen set grows. In budgeted maximum coverage, for example, an item covers fewer new elements after other items have already been selected. This is a special case of the problem and shows why exact optimization is NP-hard.

Earlier research has already given a $1-1/e$ approximation guarantee for this problem. The report examines whether the particular S2R procedure described here reaches the same factor and whether its value-query, auxiliary-operation, and working-memory costs satisfy the proposed bounds. Those analyses remain to be independently checked.

## Goals

The immediate goal is to describe S2R precisely enough to examine each step. It enumerates feasible singleton seeds, follows a feasible marginal-density greedy path from each seed, considers the path's actual prefixes, and tries adding up to two items. The manuscript lays out a proposed proof route for its approximation and resource claims, including the assumptions used to count operations and memory. Its resource bounds refer to an abstract cost model, not measured running time.

The repository also includes Lean sources that encode selected definitions and statements. Readers can compare the formal hypotheses and conclusions with the manuscript, inspect the proof dependencies, and look for gaps or counterexamples. This makes the reasoning easier to discuss and revise.

More broadly, the project uses one difficult example to explore where AI may help mathematical research and where independent review remains necessary. This is an exploratory course report. Its mathematical claims have not been independently validated and may contain errors. A successful Lean build checks the statements as encoded; it does not on its own establish that the formal model matches the intended problem or that the proposed results are new.

## How to use this repository

1. **Read the manuscript.** [paper.tex](paper.tex) contains the Chinese report. Its opening sections give the background and a proof roadmap; later sections describe the candidate algorithm and resource analysis. [references.bib](references.bib) lists the cited work. To build a local PDF, install a TeX distribution with Chinese support, XeLaTeX, and BibTeX. From the repository root, run `xelatex paper.tex`, `bibtex paper`, then `xelatex paper.tex` twice.
2. **Compare the formal statements.** [verification/S2R.lean](verification/S2R.lean) is the Lean entry point. [verification/S2R/Main.lean](verification/S2R/Main.lean) contains the approximation statement, and [verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) contains the combined output and resource statement. Check how their definitions, assumptions, and conclusions relate to the report.
3. **Reproduce the local checks.** Install Git, Python 3, and elan/Lean. From the repository root, run:

```bash
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

The audit script writes a local report under `verification/audit/` and checks the declarations and axiom dependencies it names. Read that report alongside the source rather than treating its status as an independent verdict on the mathematics. The repository contains no dataset or empirical performance experiment.
