// ch1.typ —— 第 1 章 引言
#import "lib.typ": *
#pagebreak(weak: true)

= 引言

2026 年 11 月 20 日，Levent Alpöge（与 Claude 合作）发布了黎曼猜想以及狄利克雷 L 函数广义黎曼猜想的证明。该证明仅以一个 Lean 4 形式化项目的形式存在：175,187 个文件、约 1740 万行代码，构建于 Mathlib 之上。它已通过独立编译，被多个独立内核复核，并得到 Lean FRO 与 Mathlib Initiative 的认证。

目前尚无对这一论证的任何人类可读的叙述。本文档是这方面的首次尝试。它是一份蓝图：精确地陈述主要定义与结果，解释每一个如何被证明，并指出证实它的 Lean 声明。正确性由 Lean 代码保证，而非由本文保证。这里的目标是理解。

== 所证为何

最终定理就是 Mathlib 自己的定义，一字未改：

$ "theorem" " riemannHypothesis" : " RiemannHypothesis" $

也就是说，黎曼 ζ 函数的每个不是负偶整数的零点，实部都是 $1/2$。在此过程中，借助 Mathlib 的 L 函数，该形式化项目还对每个模 $N$ 及每个模 $N$ 的狄利克雷特征 $chi$ 证明了：

$ L(s, chi) eq.not 0 quad upright("对") upright(" Re s > 1/2") upright("（若 χ 平凡则 s ≠ 1）"), $

再结合函数方程，这便是狄利克雷 L 函数的 GRH。见 #ref[定理 2.1] 与 #ref[定理 2.4]。

== 验证状态

- 整个源码经文本搜索确认：不含 `sorry`，不含自定义公理，也不含内核绕过手段（如 `native_decide`、`unsafe` 或 `implemented_by`）。
- 所证命题正是 Mathlib 的 `RiemannHypothesis`；整个开发中没有任何地方重新定义或遮蔽（shadow）它。
- 公告与独立检查报告指出：两个头版定理仅依赖 `propext`、`Classical.choice` 与 `Quot.sound`，且各独立内核（nanoda、con-leche、lean4lean 以及 Lean 自身的 replay）均接受导出的证明。我们并未亲自重跑这些检查。

本蓝图通过阅读源码写成，其间借助了自动化阅读工具。命题内容取自代码。凡某一步是从结构推断而来、而非逐行读出，文中都以标记#inferred[如此]注明。

== 一页纸策略

*第 1 步：一个单侧素数计数界就够用（#ref[第 2 节]）。* 由函数方程，RH 可由“$Re s > 1/2$ 右侧无零点”这一形式的 GRH 推出。而由 Landau 的一段论证，只要一个带正权、经特征扭曲的切比雪夫函数在窗口 $[Y, Y^(3/2)]$ 上满足量级为 $y^(1/2 + O(epsilon))$ 的单侧界，即可得到它。

*第 2 步：宿主域上的一个精确恒等式（#ref[第 3 节]）。* 证明由一个实分圆域与两个辅助的虚二次域 $Q(sqrt(-q))$、$Q(sqrt(-d))$ 构造出一个大的 CM“宿主”域，其中 $q$、$d$ 为巨大的辅助素数。在 $Q(sqrt(-d))$ 中惯性的素数构成一个正计数 $"ASK"$，它有精确的主项 $"MAIN"$，且一个精确恒等式表明 $"ASK" - "MAIN"$ 恰为诸特征误差的平均值。于是 $"ASK"$ 的上界就给出第 1 步。辅助素数的存在性由临界带边缘附近的经典解析数论证明。

*第 3 步：theta 塔（#ref[第 4 节]）。* 证明在定与不定酉群之间构造一座由 $m approx sqrt(x)$ 个 theta 提升组成的塔。它每一步把同一个素数计数写一遍再取平均。那个唯一的大误差项被除以 $m$，而每步只增加小误差，两者在 $x^(1/2 + O(epsilon))$ 处达到平衡。

*第 4 步：体积与乘积公式（#ref[第 5 节]）。* 每一步中，一个由模形式构成的格被夹在一个下界（算术 Hilbert–Samuel 与正性）和一个上界（小截面与斜率不等式）之间。CM 域上的乘积公式把诸格体积化为素数上 $log p$ 的和。在惯性素数处，周期可被 $p$ 的幂整除，幂次由一个高为 2 的形式群控制。精确的主项是 Chowla–Selberg 周期。

*第 5 步：伽罗瓦一侧（#ref[第 6 节]）。* 一个 Tate–Shafarevich 型群 $"Ш"^2$ 可能破坏该计数。它被逐情形地控制住：奇数部分用伯努利数，偶数部分用 Hida 理论与 Taylor–Wiles 拼合，$ell = 2$ 时用 Ferrero–Washington。所需的伽罗瓦表示由酉志村簇的 $ell$-进上同调构造，其 Frobenius 作用由 Eichler–Shimura 同余关系控制。

*函数库（#ref[第 7 节]）。* 该形式化项目还在 Lean 中证明了若干它用作工具的大型定理，其中有特征零情形的 Hironaka 奇点消解定理，以及好约化情形的 $p$-进 Hodge 比较定理。

== 依赖图

#align(center)[
  #block(spacing: 0.9em)[
    #set text(font: zhkai, size: 9.6pt)
    #box(stroke: 0.7pt + black, radius: 4pt, inset: (x: 9pt, y: 5.5pt), width: 74%)[
      #align(center)[*黎曼猜想*（#ref[定理 2.1]）]
    ]
    #v(0.35em)
    #align(center, $arrow.t$)
    #v(0.15em)
    #box(stroke: 0.7pt + black, radius: 4pt, inset: (x: 9pt, y: 5.5pt), width: 74%)[
      #align(center)[*狄利克雷 L 函数的 GRH*（#ref[定理 2.4]）\
      函数方程，归约到本原特征]
    ]
    #v(0.35em)
    #align(center, $arrow.t$)
    #v(0.15em)
    #box(stroke: 0.7pt + black, radius: 4pt, inset: (x: 9pt, y: 5.5pt), width: 74%)[
      #align(center)[*Landau 窗口判据*（#ref[定理 2.14]）\
      $[Y, Y^(3/2)]$ 上的单侧界 $y^(1/2 + O(epsilon))$]
    ]
    #v(0.35em)
    #align(center, $arrow.t$)
    #v(0.15em)
    #box(stroke: 0.7pt + black, radius: 4pt, inset: (x: 9pt, y: 5.5pt), width: 74%)[
      #align(center)[*宿主域上的平衡恒等式*（#ref[定理 3.6] 与 #ref[定理 3.8]）\
      辅助素数存在（#ref[定理 3.14]）]
    ]
    #v(0.35em)
    #grid(columns: (1fr, 1fr), column-gutter: 4%,
      align(center, $arrow.t$), align(center, $arrow.t$))
    #v(0.15em)
    #grid(columns: (1fr, 1fr), column-gutter: 4%,
      box(stroke: 0.7pt + black, radius: 4pt, inset: 7pt)[
        #align(center)[*几何一臂*\
        theta 塔（#ref[定义 4.2] 与 #ref[命题 4.7]）\
        余体积界（#ref[定理 5.13]）\
        乘积公式，局部增益（#ref[定理 5.15] 与 #ref[定理 5.19]）\
        $"ASK" <= "MAIN" + "error"$（#ref[定理 5.27]）]
      ],
      box(stroke: 0.7pt + black, radius: 4pt, inset: 7pt)[
        #align(center)[*伽罗瓦一臂*\
        Vandiver 型界（#ref[定理 6.4]）\
        伽罗瓦表示（#ref[定理 6.18]）\
        拼合（#ref[定理 6.13]）\
        轻量局部 Langlands（#ref[定理 6.26]）]
      ])
    #v(0.35em)
    #align(center, $arrow.t$)
    #v(0.15em)
    #box(fill: rgb("#efefef"), stroke: 0.7pt + black, radius: 4pt, inset: (x: 9pt, y: 5.5pt), width: 86%)[
      #align(center)[*库中已证的输入定理*（#ref[第 7 节]）\
      Hironaka、$p$-进 Hodge、平展上同调、算术 Hilbert–Samuel、斜率不等式、Ferrero–Washington、Siegel]
    ]
  ]
]

箭头从结果指向它所支撑的结果。伽罗瓦一臂经由宿主要求反哺几何一臂：Vandiver 型界是 #ref[GChi]（#ref[定理 3.17]）的一部分，且#inferred[控制 #ref[定理 5.27] 中的 $"Ш"$ 项]。

== 如何阅读本蓝图

- 每个编号结果之后都有一行 *Lean:*，给出证实它的声明及其相对于源码根目录的文件。
- “输入定理”标记在库中被证明并被当作工具使用的大型经典定理。“注意”标记 Lean 命题弱于、或不同于其同名经典定理之处。这些差异从不影响正确性：Lean 恰好检验所用的内容。
- 许多 Lean 命名与文件夹名具有误导性（例如 `AutomorphicSpectrum` 文件夹里装的是 Arakelov 几何）。我们跟随数学本身，而非这些名字。
- 该领域的初学者可以先读 #ref[第 2 节] 以及后面各节开头给出计划的几页，并跳过各证明。

== 本蓝图不做什么

它不重证任何东西：证明梗概负责解释，Lean 负责认证。它不覆盖每一条引理。整个形式化项目约有 819,000 条定理与引理。主文件导入了 175,187 个文件中的 169,418 个，而从主定理出发的依赖爬取（在某一上限处停止）就已触及其中约 104,000 个。我们描述其中承重的部分。一些深层叶子未被细读；#ref[附录 A] 列出了它们。
