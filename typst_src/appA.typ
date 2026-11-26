// appA.typ —— 附录 A 常数、命名与本次阅读的空白
#import "lib.typ": *

#show table: set text(size: 9pt)
#pagebreak(weak: true)

#heading(numbering: none)[附录 A：常数、命名与本次阅读的空白]
#heading(level: 2, numbering: none)[A.1 常数从何而来]

开发中的大多数常数是安全裕量，而非精确值。整体尺寸预算是 $b = exp(x^epsilon)$，所以 $x$ 的任何固定幂都无代价。下表记录阅读者之所见。

#table(
  columns: (3.3cm, 5.2cm, 1fr),
  align: (left, left, left),
  stroke: 0.4pt,
  inset: 4.5pt,
  table.header([*常数*], [*从何进入*], [*为何取此值*]),
  [$t = x^401$ 中的 401], [`VWin`，Vandiver 型界（#ref[定理 6.4]）], [宿主秩 $t$ 至多 $x^400$；多出的 1 为一重重标度 $x = k x'$ 买单。非精确。],
  [1/52], [$epsilon$ 的上界], [使指数 $6.5 + 19 epsilon$ 保持在 6.87 之下的最大单位分数；1/51 恰好不行。],
  [$m in [sqrt(x delta), 2 sqrt(x delta)]$], [theta 提升的个数（#ref[命题 4.7]）], [平衡 $x\/m$ 与 $m x^epsilon$；$x^(1\/2 + O(epsilon))$ 中任何 $m$ 都行（`SizeWindows` 只需 $x^(1\/2 - epsilon) <= m <= x^(1\/2 + epsilon\/2)$），而塔使用 $[sqrt(x delta), 2 sqrt(x delta)]$。],
  [$n tilde.op x^(2 + 8 epsilon)$，$k tilde.op x^(9\/2 + 10 epsilon)$], [域次数与权预算], [选得使 $m^2 <= k$ 且计数中的修正保持小。宽裕。],
  [$[Y, Y^(3\/2)]$ 中的 3/2], [Landau 窗口（#ref[定理 2.14]）], [只有 `zeroFreeAll_of_topG` 对一般 $lambda$ 陈述；很可能 $(1, 2)$ 中任何值都行。],
  [1/400，指数 1/4], [零密度盒（#ref[定理 3.18]）], [证明需要盒宽低于 1/192、指数由其分块低于约 0.18；两者都有余量。],
  [$epsilon\/5$，4/5], [$q$、$d$ 与 Ferrero–Washington 部分的尺寸], [阶梯 $3\/4 < dots.h.c < 1$ 中任何选择都行。],
  [2500、诸 8、$5^4$], [theta 截面的赋值界与上确界范数界], [2500 是一个自由的小常数；#inferred[8 是 theta 函数的权乘子；$5^4$ 来自 level 5 的 theta 常数]；上确界范数报告说任何奇 $R > 1$ 都行。],
  [“至多 15”], [高度引擎中的一个基数上限], [一个安全上限；代码证明真实界是 4。],
)

#heading(level: 2, numbering: none)[A.2 有误导性的名字]

Lean 命名是在自动化开发过程中选定的，往往夸大或误述。读源码的人应当知道：

- `OpenLiteratureStatements` 与 `OpenImageCondition` 听起来像假设。二者都被已证定理完全兑现。
- `RecTExists`（“局部 Langlands”）是一个受限的存在性命题（#ref[定理 6.26]）。
- `MoriwakiBigStatement` 是一个算术 Hilbert–Samuel 下界（#ref[输入定理 7.8]）。
- `TwistedEisensteinNonvanishing` 是一个关于有限和的局部不变性事实。
- 文件夹 `AutomorphicSpectrum` 装的是 Arakelov 与 Hodge 丛几何，不是谱理论；`AbelianVarietyTheory` 大多是格、theta 函数与酉群；`EightfoldTheory` 不含数学；`WeilJacquetShalikaLaw.lean` 装的是格赋值。
- 许多短名（`IsJ`、`PairEx`、`LemmaM`、`PropZ`、`CutAt`）在不同命名空间中被多次定义。务必检查命名空间。

#heading(level: 2, numbering: none)[A.3 本次阅读未覆盖什么]

175,187 个文件中约 1,100 个被细读，且每个文件都被扫描检查 `sorry`、公理与内核绕过。以下内容未细读：

- Taylor–Wiles 拼合内部的超滤拼合引理与一些伽罗瓦上同调引理（`s5`、`chainAbs`、`cohLim`、`galOut`）；
- 下降步骤背后的迹公式叶子；
- 从主化到奇点消解的过程（约 22,000 行）；
- 412 行的无对数零密度证明与显式公式；
- 开发中的 de Rham 上同调是否与代数 de Rham 上同调一致，以及棱柱 Dieudonné 命题的内部证明。

这些都不是那种“RH 论证失败而 Lean 未察觉”的地方。它们是标准理论的自足片段。

#heading(level: 2, numbering: none)[A.4 来源]

- L. Alpöge，宣布该证明的笔记：#link("https://alpo.ge/remark.pdf")[https://alpo.ge/remark.pdf]。
- 该开发项目发布的 Lean 源码，本蓝图直接阅读的即此。
- Lean FRO 与 Mathlib Initiative 关于验证的联合声明（2026 年 11 月）。

#pagebreak(weak: true)
#heading(numbering: none, outlined: false)[表 1：PublishedHodgeBundleTheorems 的 28 个字段。全部在库中证明。表内的分组把若干字段放在一行。]

#table(
  columns: (1.2cm, 6.0cm, 1fr),
  align: (left, left, left),
  stroke: 0.4pt,
  inset: 4.5pt,
  table.header([*字段*], [*Lean 名*], [*内容（如所陈述）*]),
  [p1], [ToroidalCompactification], [带 SNC 边界与 log Kodaira–Spencer 同构的光滑模型；仅在数域上],
  [p2, p3], [VolGe, VolNef], [算术体积 ≥（相应地 =）自相交，nef 情形],
  [p4], [ArCalc], [Arakelov 相交演算（7 条公理，存在性已证）],
  [p5], [AbelianDeRham], [阿贝尔概形的 $H_"dR"^1$：自由、滤过、基变换、刚性、对偶],
  [p8], [RayClassFieldSt], [射线类群上的 Artin 映射，非分歧素数处的 Frobenius],
  [p12], [SemistableReductionSt], [$K\/QQ_p$ 的有限扩域上的半阿贝尔约化],
  [p13], [StrongApproxSU], [秩 $>= 2$ 厄米空间的 SU 的强逼近],
  [p14], [GreenSeriesSt], [$"GL"_N (FF_g)$ 的 Green 级数（$g$ 为素数）],
  [p16], [GoodChernWeil], [Mumford：好度量的陈形式积分为陈数],
  [p19, p20], [LandherrSt, HasseNormSt], [厄米形式是局部的；Hasse 范数原理（二次）],
  [p22], [SemiAbelianHomExtension], [半阿贝尔概形的同态越过正规基延拓],
  [p23], [InducedSimpleLowestAlcove], [$"GL"_N$ 的 $nabla(lambda)$ 在最低 alcove 中对 $lambda$ 单模],
  [p25, p26], [principalPolarisationOneSection, AbMulNSt], [$h^0 (cal(A), L) = 1$；$\# cal(A)[n](k) = n^(2g)$],
  [q1], [GrothendieckMessing], [沿幂零 PD 加厚的形变],
  [q4], [PrismaticDieudonneHodge], [带 $A_"inf"$-模与 Hodge 序列性质的函子],
  [q6], [KawamataViehweg], [$H^q (K_X + N) = 0$，$N$ nef 且大],
  [q7], [NefNumerics], [$L^d >= 0$；nef 且大当且仅当顶相交为正；Riemann–Roch],
  [q8], [L2ExtensionLogCanonical], [从有限零点集的 Ohsawa–Takegoshi 型延拓],
  [q9], [ArithHilbertSamuel], [#ref[输入定理 7.7]],
  [q10, q11], [ChowFormExists, CycleHeights], [Chow 形式；循环的高度],
  [q13], [SerreHolomorphicSections], [线丛截面的 GAGA],
  [q15], [NadelVanishingAndNonKltDivisor], [Nadel 消没；孤立非 klt 除子],
  [q16], [Principalisation], [Hironaka 主化，光滑射影情形（#ref[输入定理 7.1]）],
  [q18], [FormalAlgebraisation], [形式射影概形的 Grothendieck 存在性],
)

#pagebreak(weak: true)
#heading(numbering: none, outlined: false)[表 2：库的规模，以及输入定理背后的部分。`AbelianVarietyTheory/Proofs` 的 95k 个文件中约 38.7k 是五行命题桩。169,418 个文件（96.7%）在 `Main.lean` 的导入闭包中。]

#table(
  columns: (4.6cm, 2.1cm, 2.3cm, 1fr),
  align: (left, right, right, left),
  stroke: 0.4pt,
  inset: 4.5pt,
  table.header([*库的部分*], [*文件数*], [*行数*], [*在本章中的角色*]),
  [整棵树], [175,187], [17,374,215], [一切],
  [Development（顶层文件夹）], [141,928], [12.2M], [大多数证明],
  [Formalism], [18,254], [3.2M], [斜率、无零点、宿主],
  [GroundTheory], [8,507], [1.1M], [周期环、高度、Chowla–Selberg],
  [ReciprocityTheory], [3,845], [0.56M], [Moriwaki、Poincaré–Lelong、离散序列],
  [AbelianVarietyTheory/Proofs], [95,418], [7,436,698], [大多数引理级证明],
  [ResolutionOfSingularities], [499], [140,709], [#ref[输入定理 7.1]],
  [PadicHodgeComparison], [538], [50,512], [#ref[输入定理 7.3]],
  [Development/EtaleCohomology], [1,398], [约 100k], [#ref[输入定理 7.5]],
  [GL3MeanSquares], [440], [约 78k], [#ref[输入定理 7.15]],
)
