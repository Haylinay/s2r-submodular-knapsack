<h1 align="center">S2R：预算限制下的单调子模最大化</h1>

<p align="center">一份关于 AI 辅助数学研究的探索性课程报告</p>

<p align="center">
  <a href="https://github.com/Haylinay/s2r-submodular-knapsack/blob/main/README.md">English</a> · <strong>简体中文</strong>
</p>

## 项目背景

本仓库始于一篇课程报告。随着 AI 与数学研究的联系日益紧密，我们选取一个已有丰富研究成果的 NP 难组合优化问题，尝试回答一个具体问题：AI 能否帮助提出算法思路、梳理数学论证，并把其中一部分陈述写成可以核查的形式？仓库记录了这次尝试的文稿和代码，也保留了需要继续审查的问题。

研究对象是**带一个总预算的单调子模最大化**。给定有限元素集合 $V$、每个元素的正成本 $c_i$、预算 $B\ge0$ 和集合价值函数 $f$，需要在预算范围内选出价值最高的集合：

$$
\max_{S\subseteq V} f(S)
\qquad \text{s.t.} \qquad
\sum_{i\in S}c_i\le B.
$$

文稿假设 $f(\varnothing)=0$。“单调”表示增加元素不会降低价值；“子模”表示边际收益递减，即同一元素加入较大集合时产生的新增价值，不会高于它加入较小集合时的新增价值。这些条件使贪心选择值得研究，但预算约束仍让精确优化变得困难。

[预算最大覆盖](https://www.sciencedirect.com/science/article/pii/S0020019099000319)提供了一个直观例子：每个可选集合都有成本，我们希望在预算内覆盖尽可能多的对象。如果几个集合覆盖了相同对象，后加入的集合通常只能增加少量尚未覆盖的对象。这正是边际收益递减。预算最大覆盖是上述模型的特例，并且是 NP 难问题。

面对这类问题，近似算法试图找到一个可行集合，并分析它的价值与最优值之间的关系。[相关研究](https://www.sciencedirect.com/science/article/pii/S0167637703000622)已经给出 $1-1/e$ 近似保证。本课程报告关心一个更具体的问题：文稿中的 S2R 候选算法能否达到相同保证？它需要多少次价值查询、多少辅助操作和多少工作空间？文稿提出了一条可能的分析路线，结论仍需独立复核。完整的引用信息见 [references.bib](references.bib)。

文稿采用**价值预言机模型**：算法通过查询取得 $f(S)$，计数时不包括预言机内部的计算成本。因此，价值查询次数是一项单独的资源指标。仓库目前没有针对具体数据集实现价值函数；如要用于实际问题，还需确定价值函数及其计算成本。

## 项目目标

**把候选算法说清楚。** [paper.tex](paper.tex) 中的 S2R 按以下方式生成候选集合：

1. 把空集列为候选，并枚举每个满足预算的单点种子。
2. 从每个种子出发，每一步只考虑当前仍能加入的元素，选择“新增价值 ÷ 元素成本”最大的一个。平局按固定顺序处理；只要还有可加入的元素，即使最大边际收益为零，路径也继续延伸。
3. 检查贪心路径上**实际出现的每个前缀**。对每个前缀，考察补入零个、一个或两个元素后仍不超预算的候选；补入之后不重新运行贪心。
4. 在生成的可行候选中，输出价值最高的集合。

这里的“真实前缀”是贪心路径实际到达的集合。文稿后面使用的连续插值只用于证明，不会产生新的算法候选。区分算法步骤与分析工具，是检查证明和资源计数的基础。

**检查文稿提出的数学与资源主张。** 文稿尝试论证 S2R 的输出价值至少为最优值的 $1-1/e$。对于元素数 $n\ge1$ 的情形，它还给出了以下待复核的资源界：

| 文稿提出的界 | 所计量的内容 |
| --- | --- |
| $Q\le n^3$ | 对价值函数的预言机查询次数 |
| $A\le141n^3$ | 指定计费模型中的辅助操作次数 |
| $P\le66n^2$ | 以抽象字为单位的峰值工作空间 |

这些数值是**尚未得到独立确认的工作主张**，可能存在错误。资源计数采用文稿规定的精确实数、单位成本 RAM 模型，不是实机运行时间或实际内存占用的测量。预言机内部开销、数值位复杂度、整集合序列化和 Lean 求值器堆等也不包含在这些界中。资源分析还说明如何通过候选压缩和逐行扫描控制中间结果的存储。

**让关键陈述能够逐项对照。** Lean 工程把问题模型、部分算法构造、近似陈述，以及输出可行性、价值和资源界的联合陈述写成形式化源码。核查脚本检查指定声明及其公理依赖。读者可以据此确认形式化文件中究竟写了哪些条件和结论，再与文稿逐项比较。

这个项目还希望借具体难题观察 AI 能如何辅助数学研究，以及独立审查应放在哪些环节。这是一份探索性的课程报告；其中的数学主张尚未经过独立验证，可能存在错误。Lean 构建通过说明源码中的形式化陈述在其定义和假设下通过了检查，但不能单独保证形式化模型、S2R 的原意与文稿的自然语言论证完全一致，也不能据此判断研究的新颖性。对数学推导和已有文献的核查仍然必要。

## 如何使用这个仓库

建议按照“理解问题—追踪算法—对照形式化陈述—复现核查”的顺序阅读。主要文件如下：

| 文件 | 内容与用途 |
| --- | --- |
| [paper.tex](paper.tex) | 中文课程报告，包含问题定义、已有工作、证明路线图、S2R 规则和候选资源分析 |
| [references.bib](references.bib) | 报告引用的文献条目 |
| [verification/S2R.lean](verification/S2R.lean) | Lean 工程入口 |
| [verification/S2R/Basic.lean](verification/S2R/Basic.lean) | 有限集合模型、成本、可行性和价值函数的假设 |
| [verification/S2R/Algorithm.lean](verification/S2R/Algorithm.lean) | 形式化工程使用的算法定义 |
| [verification/S2R/Main.lean](verification/S2R/Main.lean) | 近似保证的形式化陈述 |
| [verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) | 输出性质、近似保证、查询、操作和空间界的联合陈述 |
| [verification/verify_s2r.py](verification/verify_s2r.py) | 指定结果及其公理依赖的本地构建与核查脚本 |
| [.github/workflows/lean.yml](.github/workflows/lean.yml) | 在 GitHub Actions 中运行 Lean 构建与核查的配置 |

**1. 阅读报告。** 先看 [paper.tex](paper.tex) 的摘要、背景和证明路线图，了解报告试图回答什么问题。第 1 节给出模型和算法定义；后续章节展开候选近似论证；第 12 节解释候选压缩和资源计数。阅读 [references.bib](references.bib) 时，要区分文献已有的近似结果和本报告针对 S2R 提出的主张。

仓库保留 LaTeX 与 BibTeX 源码，不提交编译生成的 PDF。若需本地编译，请安装带中文支持的 TeX 发行版、XeLaTeX 与 BibTeX，在仓库根目录运行：

```bash
xelatex paper.tex
bibtex paper
xelatex paper.tex
xelatex paper.tex
```

**2. 对照形式化陈述。** 从 [verification/S2R.lean](verification/S2R.lean) 查看工程的导入入口；阅读 [verification/S2R/Basic.lean](verification/S2R/Basic.lean) 中的实例假设、[verification/S2R/Algorithm.lean](verification/S2R/Algorithm.lean) 中的算法对象，再查看 [verification/S2R/Main.lean](verification/S2R/Main.lean) 的近似定理与 [verification/S2R/StreamingComplexity.lean](verification/S2R/StreamingComplexity.lean) 的联合定理。重点比较两边对可行集合、贪心前缀、二元补入和资源计数的定义是否一致。

**3. 复现本地核查。** 安装 Git、Python 3，并通过 elan 安装 Lean/Lake。Lean 与 Mathlib 的版本记录在 [verification/lean-toolchain](verification/lean-toolchain) 和 [verification/lake-manifest.json](verification/lake-manifest.json) 中。然后从仓库根目录运行：

```bash
cd verification
lake exe cache get
lake build
python -B verify_s2r.py
```

脚本会在 `verification/audit/` 中生成本地报告和日志。该目录、下载的依赖和生成的 PDF 均不进入 Git 仓库。[GitHub Actions 配置](.github/workflows/lean.yml) 会在仓库更新时运行相应的 Lean 构建与审计。

**4. 理解核查结果。** 审计状态只说明脚本列出的声明和公理依赖完成了相应检查；即使报告显示 `COMPLETE`，其含义也限于这些项目。评估数学主张时，还应检查自然语言算法是否与 Lean 对象相同、每一步引理是否满足所需前提、资源计数是否覆盖了声称的操作，以及是否存在反例。本仓库没有数据集、性能基准或实测实验可供复现。
