<h1 align="center">S2R：次模背包优化探索</h1>

<p align="center">
  <a href="https://github.com/Haylinay/s2r-submodular-knapsack/blob/main/README.md">English</a> · <strong>简体中文</strong>
</p>

## 项目背景

本仓库起于一篇课程报告的尝试。随着 AI 与数学研究的联系日益紧密，我们选取一个 NP 难优化问题，探索 AI 能否辅助构思、推导和检查数学结论。

研究对象是单背包约束下的单调次模最大化：在预算内选择元素，使具有边际收益递减性质的价值函数尽可能大。文稿讨论的近似比已有前人研究，本项目不主张发现这一近似比。

## 项目目标

- 记录 S2R 候选算法：从可行单点出发，考察贪心路径的前缀，并尝试补入至多两个元素。
- 整理算法的推导，并用 Lean 表达部分陈述，供读者检查。
- 以这个具体问题探索 AI 能在数学研究中提供哪些帮助，以及哪些环节仍需独立审查。

这是一份探索性课程报告。文稿中的数学主张尚未得到独立确认，可能存在错误；仓库不将其中的近似保证或资源界作为已经确立的结果。

## 如何使用这个仓库

- **阅读报告：** [paper.tex](paper.tex) 是中文论文源码，[references.bib](references.bib) 是引用文献。若要在本地编译 PDF，安装支持中文的 XeLaTeX 和 BibTeX，然后在仓库根目录依次运行 `xelatex paper.tex`、`bibtex paper`，再运行两次 `xelatex paper.tex`。
- **查看形式化内容：** 从 [verification/S2R.lean](verification/S2R.lean) 进入 Lean 工程；[verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) 包含当前的联合陈述。请将源码中的假设和结论与报告逐项比较。
- **运行核查：** 安装 Git、Python 3 和 elan/Lean 后，从仓库根目录运行：

```bash
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

核查脚本会检查指定的 Lean 声明及其公理依赖，并在 `verification/audit/` 生成本地报告。构建和核查通过，仍不能单独确认自然语言论证与形式化模型完全对应。本仓库没有数据集或实测性能实验。
