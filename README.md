# S2R · AI 辅助的次模背包优化探索

[中文](#中文) · [English](#english)

## 中文

> **研究状态：探索性工作稿，数学结论尚未得到独立确认，可能存在错误。** 这里公开候选思路、论文草稿和 Lean 源码，供读者检查与讨论。请勿把草稿中的近似比或复杂度界当作已经确立的结果。

### 我们研究什么问题？

给定一组有成本的元素和一个预算，如何选择不超预算的集合，使单调次模函数衡量的收益尽可能高？次模性表达“边际收益递减”。预算最大覆盖、监测点选择可以作为这一抽象模型的例子。本仓库不包含真实数据集，也不报告实际系统的性能实验。

这一问题的精确 $1-1/e$ 近似常数已有文献先例；本项目不主张发现这个常数。我们探索一个具体的候选规则：从可行单点种子出发，考察可行边际密度贪心路径的真实前缀，再尝试补入至多两个元素。论文草稿提出相应的近似与资源界作为**待复核的工作主张**。

### 为什么公开这份工作？

我们想探索 AI 是否能帮助研究这类与数据选择有关的优化问题：提出问题、组织数学推导，并将部分主张写成可供机器检查的形式。仓库展示的是这一研究过程和一个可讨论的候选方案；它不表明 AI 已解决该优化问题，也不保证文稿结论正确或具有新颖性。欢迎读者核对假设、寻找反例，并比较论文与形式化陈述是否一致。

### 有哪些材料？

- [paper.tex](paper.tex)：包含候选算法与推导的中文工作稿。
- [references.bib](references.bib)：工作稿引用的文献。
- [verification/S2R.lean](verification/S2R.lean)、[联合定理源码](verification/S2R/StreamingComplexity.lean)：Lean 形式化入口与当前主陈述。
- [verify_s2r.py](verification/verify_s2r.py)、[lean.yml](.github/workflows/lean.yml)：本地审计脚本与 GitHub 自动核查配置。

过去的 GitHub Actions 运行对当前形式化陈述完成了 Lean 构建和公理审计。它们检查的是**代码中实际写出的定义与定理**，不能独立确认自然语言论证、建模对应、研究优先权或现实运行性能。请以具体提交对应的 [Actions 结果](https://github.com/Haylinay/s2r-submodular-knapsack/actions) 为准；仓库目前为私有。

在安装 Git、Python 3 和 elan/Lean 后，可在仓库根目录复核：

```text
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

论文可用 XeLaTeX 与 BibTeX 从源码编译。PDF、下载的文献和构建缓存都留在本地，不进入 Git 仓库。

作者为 **LINHAI LU**。项目曾使用 MIMO 2.6、GLM5.3、DeepSeek v4.1 Flash、OpenAI 6 Sol 和 OpenAI 6 Astra 辅助研究与写作；模型不是作者。授权范围见 [LICENSE](LICENSE)，引用信息见 [CITATION.cff](CITATION.cff)。

## English

> **Status: exploratory working draft. The mathematical claims have not been independently validated and may contain errors.** We share a candidate idea, a manuscript draft, and Lean source for inspection and discussion. The approximation and complexity bounds in the draft should not be treated as established results.

### What problem are we studying?

Given items with costs and a budget, how can we choose a feasible set with high value under a monotone submodular function? Submodularity models diminishing marginal returns. Budgeted coverage and monitoring-site selection are motivating abstractions. This repository contains no real-world dataset or empirical performance study.

The exact $1-1/e$ approximation factor has prior literature. We do not claim to have discovered it. We explore a particular candidate rule: start from a feasible singleton seed, examine actual prefixes of a feasible density-greedy path, and consider adding up to two items. The manuscript proposes approximation and resource bounds for this rule as **working claims that need independent scrutiny**.

### Why share this work?

We are exploring whether AI can assist research on data-related optimization problems by helping formulate questions, organize mathematical arguments, and express some claims in a machine-checkable form. This repository records that process and a candidate approach. It does not show that AI has solved the optimization problem, or establish that the manuscript is correct or novel. Readers are invited to inspect the assumptions, search for counterexamples, and compare the manuscript with the formal statements.

### What is included?

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
