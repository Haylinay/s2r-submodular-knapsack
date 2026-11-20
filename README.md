<h1 align="center">S2R: Submodular Knapsack Exploration</h1>

<p align="center">
  <strong>English</strong> · <a href="https://github.com/Haylinay/s2r-submodular-knapsack/blob/main/README.zh-CN.md">简体中文</a>
</p>

## Background

This repository began as a course-report experiment. As AI becomes more closely involved in mathematical research, we use an NP-hard optimization problem to explore how it might assist with ideas, arguments, and checks.

The case study is monotone submodular maximization under a single knapsack constraint: choose items within a budget to maximize a value function with diminishing returns. The approximation factor discussed in the manuscript is known from prior work; this project does not claim to discover it.

## Goals

- Document S2R, a candidate algorithm that starts from a feasible singleton, examines prefixes of a greedy path, and considers adding up to two items.
- Organize the reasoning and express selected statements in Lean so that readers can inspect them.
- Use this case to explore where AI may help mathematical research and where independent review remains necessary.

This is an exploratory course report. Its mathematical claims have not been independently validated and may contain errors. The repository does not present the proposed approximation guarantee or resource bounds as established results.

## How to use this repository

- **Read the report.** [paper.tex](paper.tex) is the Chinese manuscript source; [references.bib](references.bib) contains its references. To build a PDF locally, install XeLaTeX with Chinese support and BibTeX. From the repository root, run `xelatex paper.tex`, `bibtex paper`, then `xelatex paper.tex` twice.
- **Inspect the formalization.** Start with [verification/S2R.lean](verification/S2R.lean). The current combined statement is in [verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean). Compare the assumptions and conclusions in the source with those in the report.
- **Run the checks.** Install Git, Python 3, and elan/Lean, then run from the repository root:

```bash
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

The audit script checks specified Lean declarations and their axiom dependencies and writes a local report under `verification/audit/`. A successful build or audit does not by itself establish that the prose argument matches the formal model. This repository contains no dataset or empirical performance study.
