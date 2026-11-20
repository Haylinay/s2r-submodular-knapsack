<h1 align="center">S2R：单背包次模优化探索</h1>

<p align="center">
  <a href="https://github.com/Haylinay/s2r-submodular-knapsack/blob/main/README.md">English</a> · <strong>简体中文</strong>
</p>

## 项目背景

本仓库源于一篇课程报告。随着 AI 与数学研究的联系日益紧密，我们选取一个具体的 NP 难优化问题，尝试了解 AI 能否帮助提出算法思路、梳理证明，并把部分论证写成可检查的形式。仓库记录了这次尝试的材料，也留下了需要继续核查的问题。

研究对象是单背包约束下的单调次模最大化。每个元素有一定成本，目标是在总预算内选出价值尽可能高的集合。次模性描述边际收益递减：已选集合越大，同一个元素带来的新增收益不会增加。例如，在预算最大覆盖问题中，先选的元素越多，后来加入一个元素通常能新增覆盖的对象就越少。预算最大覆盖是这一模型的特例，也说明精确求解具有 NP 难性。

已有研究为这一问题给出了 $1-1/e$ 近似算法。本报告围绕 S2R 这条具体的候选规则，考察它能否达到相同的近似比，以及文稿提出的价值查询次数、辅助操作次数和工作空间界能否成立。这些分析仍需独立复核。

## 项目目标

项目希望把 S2R 的步骤写清楚，方便逐项检查：枚举可行的单点种子，从每个种子出发运行可行的边际密度贪心；在贪心路径的真实前缀上，再尝试补入至多两个元素。文稿给出了候选的近似分析和资源计费过程，读者可以据此检查每一步使用了哪些假设。资源界采用文稿规定的抽象计费模型，并非实机运行时间的测量结果。

仓库还提供 Lean 源码，用来表达部分定义和数学陈述。读者可以对照文稿与 Lean 中的条件、结论和证明依赖，寻找可能的漏洞或反例。我们希望这些材料有助于继续讨论和修改这条思路。

项目也借这个具体难题观察 AI 可以怎样辅助数学研究，以及哪些地方仍需要独立审查。这是一份探索性的课程报告；文稿中的数学主张尚未得到独立确认，可能存在错误。Lean 构建通过只说明源码中写出的陈述在其假设下通过了检查，不能单独保证形式化模型与原问题完全一致，也不能证明结论具有新颖性。

## 如何使用这个仓库

1. **阅读文稿。** [paper.tex](paper.tex) 是中文报告源码，开头介绍背景与证明路线，后续章节给出候选算法和资源分析；[references.bib](references.bib) 列出引用文献。若要在本地生成 PDF，请安装支持中文的 TeX 发行版、XeLaTeX 和 BibTeX，在仓库根目录依次运行 `xelatex paper.tex`、`bibtex paper`，再运行两次 `xelatex paper.tex`。
2. **对照形式化陈述。** [verification/S2R.lean](verification/S2R.lean) 是 Lean 工程入口；[verification/S2R/Main.lean](verification/S2R/Main.lean) 包含近似陈述，[verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) 包含输出与资源界的联合陈述。建议逐项比较源码与文稿中的定义、假设和结论。
3. **复现本地核查。** 安装 Git、Python 3 和 elan/Lean 后，从仓库根目录运行：

```bash
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

核查脚本会在 `verification/audit/` 下生成本地报告，检查其中列出的 Lean 声明及其公理依赖。核查结果只覆盖脚本指定的形式化内容，仍需有人检查文稿论证与形式化模型是否对应。本仓库没有数据集或实测性能实验。
