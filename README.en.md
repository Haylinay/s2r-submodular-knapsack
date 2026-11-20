# S2R · AI-assisted exploration of submodular knapsack

**Language / 语言：[简体中文](./README.md) · English**

> **Status: exploratory working draft. The mathematical claims have not been independently validated and may contain errors.** We share a candidate idea, a manuscript draft, and Lean source for inspection and discussion. The approximation and complexity bounds in the draft should not be treated as established results.

## What problem are we studying?

Given items with costs and a budget, how can we choose a feasible set with high value under a monotone submodular function? Submodularity models diminishing marginal returns. Budgeted coverage and monitoring-site selection are motivating abstractions. This repository contains no real-world dataset or empirical performance study.

The exact $1-1/e$ approximation factor has prior literature. We do not claim to have discovered it. We explore a particular candidate rule: start from a feasible singleton seed, examine actual prefixes of a feasible density-greedy path, and consider adding up to two items. The manuscript proposes approximation and resource bounds for this rule as **working claims that need independent scrutiny**.

## Why share this work?

We are exploring whether AI can assist research on data-related optimization problems by helping formulate questions, organize mathematical arguments, and express some claims in a machine-checkable form. This repository records that process and a candidate approach. It does not show that AI has solved the optimization problem, or establish that the manuscript is correct or novel. Readers are invited to inspect the assumptions, search for counterexamples, and compare the manuscript with the formal statements.

## What is included?

- [paper.tex](paper.tex): a Chinese working manuscript with the candidate algorithm and analysis.
- [references.bib](references.bib): bibliography used by the manuscript.
- [verification/S2R.lean](verification/S2R.lean) and the [joint theorem source](verification/S2R/StreamingComplexity.lean): Lean entry point and current main statement.
- [verify_s2r.py](verification/verify_s2r.py) and [lean.yml](.github/workflows/lean.yml): local audit script and GitHub verification workflow.

Previous GitHub Actions runs have built the Lean development and audited axiom dependencies for the formal statements as written. These checks do **not** independently establish that the informal argument matches the model, that the work is novel, or that the abstract resource bounds predict real-world performance. Consult the [Actions run for the relevant commit](https://github.com/Haylinay/s2r-submodular-knapsack/actions); the repository is currently private.

With Git, Python 3, and elan/Lean installed, run from the repository root:

```text
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

The manuscript can be compiled from source with XeLaTeX and BibTeX. PDFs, downloaded papers, and build caches stay local and are excluded from Git.

The author is **LINHAI LU**. MIMO 2.6, GLM5.3, DeepSeek v4.1 Flash, OpenAI 6 Sol, and OpenAI 6 Astra assisted the research and writing; the models are not authors. See [LICENSE](LICENSE) for licensing and [CITATION.cff](CITATION.cff) for citation information.
