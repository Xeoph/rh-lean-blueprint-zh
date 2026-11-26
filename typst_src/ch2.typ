// ch2.typ —— 第 2 章 从 RH 到一个单侧素数计数界
#import "lib.typ": *
#pagebreak(weak: true)

= 从 RH 到一个单侧素数计数界

本章是证明的顶端。它从 Mathlib 的黎曼猜想陈述出发，以一个明确的分析目标收尾。该目标是：加权切比雪夫误差在窗口 $[Y, Y^(3/2)]$ 上成立形如 $x^(1/2 + O(epsilon))$ 的单侧上界。本章内容全部是经典分析。它篇幅很短，Lean 对它做了完整检验。论文其余部分证明该目标。

这条链有四环。

+ 由函数方程，RH 可由 $zeta$ 的“$Re s > 1/2$ 处无零点”推出。
+ 该命题恰是平凡特征在全体狄利克雷特征命题（#ref[定理 2.4]）中的情形。
+ 全体特征命题由本原情形（#ref[定理 2.8]）推出。
+ 本原情形由一个 Landau 型论证（#ref[定理 2.14]）推出，它把素数和误差上的单侧界转化为无零点性。

最后一环是真正的内容开始之处。#ref[命题 2.20] 精确陈述了余下要证的东西。

== 最终定理与全体特征命题

#thm("2.1", "黎曼猜想，Mathlib 形式")[对每个 $s in CC$：若 $zeta(s) = 0$、对一切 $n in NN$ 有 $s eq.not -2(n+1)$、且 $s eq.not 1$，则 $Re s = 1/2$。]

#lean("riemannHypothesis", "Main.lean")

这里 $zeta$ 是 Mathlib 的 `riemannZeta`，即解析延拓。命题就是 Mathlib 自己的 `RiemannHypothesis`，而非其本地副本。文件 `Statements.lean` 将其改述为 `RiemannZetaZerosOnLine`，二者定义相等。

#proof(uses: ref[定理 2.4])[
  Lean 项是 `rhOfAll:=Formalism.VW.rh_of_everyallChi`，其中 `allChi` 即 #ref[定理 2.4]。用到两步，都在 `Formalism/GammaFactorNonvanishing/` 中。

  第一，`rh_of_every` 把全体特征命题特化到模 1 的平凡特征。由 Mathlib 的 `LFunction_modOne_eq`，这个 L 函数就是 $zeta$。于是当 $Re s > 1/2$、$s eq.not 1$ 时 $zeta(s) eq.not 0$。

  第二，`rh_of_right` 把它反射到左半平面。设 $rho$ 是满足 $Re rho < 1/2$ 的非平凡零点。Mathlib 的函数方程把 $zeta(rho)$ 写成
  $ zeta(rho) = 2(2pi)^(-(1-rho)) Gamma(1-rho) cos((pi(1-rho))/2) zeta(1-rho). $
  此时 $Re(1-rho) > 1/2$，故 $zeta(1-rho) eq.not 0$。又 $Gamma(1-rho) eq.not 0$。余弦只在被排除的平凡零点处为零，而 $rho = 0$ 的情形另行处理。于是 $zeta(rho) eq.not 0$，矛盾。故每个非平凡零点都有 $Re rho >= 1/2$，再由第一步得 $Re rho = 1/2$。
]

#rem("2.2", none)[
  `Main.lean` 导出五个定理。除 `riemannHypothesis` 外，它还证明了半平面形式的 #ref[定理 2.4]（`LFunction_ne_zero_of_half_lt_re`）。它还证明：每个狄利克雷 L 函数在 $0 < Re s < 1$ 内的每个零点都满足 $Re s = 1/2$（`LFunction_eq_zero_re`）。本原特征版本（`LFunction_eq_zero_re_of_isPrimitive`）与 $zeta$ 情形（`riemannZeta_eq_zero_re`）也在其中。这些“在线上”的命题来自 `Formalism.VW.critLine`——把同一反射论证应用于逆特征并配上本原函数方程。#ref[定理 2.1] 还有第二个证明 `UpperTheory.FinalTheorems.riemannHypothesis`，输入相同，反射论证另行成文，约 20 行。
]

#defn("2.3", "全体特征半平面命题")[
  命题 `EveryCharacter` 的含义如下。对每个 $N >= 1$、每个模 $N$ 的狄利克雷特征 $chi$（无论本原与否）、以及每个满足 $Re s > 1/2$ 且（$chi eq.not 1$ 或 $s eq.not 1$）的 $s in CC$，都有 $L(chi, s) eq.not 0$。
]

#lean("UpperTheory.EveryCharacter", "Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean")

这里 $L(chi, s)$ 是 Mathlib 的 `DirichletCharacter.LFunction`，即解析延拓。唯一被排除的数对是极点 $(chi, s) = (1, 1)$。

#thm("2.4", "广义黎曼猜想，半平面形式")[`EveryCharacter` 成立，无需额外假设。]

#lean("UpperTheory.FinalTheorems.everyCharacter", "Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean")

Lean 定理 `allChi`（位于 `Supplements/Kernels/MainTheorems.lean`）是同一命题的另一名字。

#caution("2.5")[这只是关于狄利克雷特征的 GRH。它不是 Artin、Hecke 或自守 L 函数的 GRH。半平面形式是核心。带状形式（$0 < Re s < 1$ 中的零点都落在 $Re s = 1/2$ 上）由 `Formalism.VW.critLine`（本原 $chi$）与 `Claim.strip`（全体 $chi$）导出。]

#proof(uses: ref[定理 2.8、6.4 与 6.18 及命题 2.20])[
  Lean 证明是围绕三个输入的薄封装。

  + 定理 `every_character_of_literature_of_vWin` 接收由三条“文献”陈述组成的包以及一条叫 `VWin` 的陈述，返回 `EveryCharacter`。文献包是一个 Lean 结构，其字段涵盖：极化尖点自守表示的伽罗瓦表示（`Row0b`）、$p$-进域上 $"GL"_n$ 的局部 Langlands（`RecTExists`）、以及一个局部—整体对偶（`caraianiLocalGlobalDual`）。
  + 在最终定理中，这些陈述并不被假设。`everyCharacter_of_row` 用 `recTExists` 与由一个 theta 提升命题得到的 `Row0b` 的证明（`Gal.Int.galoisLocalGlobalStrong_recParameter`）来喂入该结构，并用 `vwin_of_row` 由同样的输入构造 `VWin`。
  + `every_character_of_literature_of_vWin` 经过 `every_character_of_theta_integrals_local_matching`，其最后一步是 `every_character_of_green_v_win`。这一步把 #ref[定理 2.8] 应用于 `zeroFreeAll_of_topG` 在 $lambda = 3/2$ 的输出。这正是下文的 #ref[命题 2.20]。

  第四个输入用于 `plugWin`：Green 正则特征假设与封闭的定侧假设 `Hyps`；由它们，`shape_of` 借助 #ref[定理 5.27] 的格界产生 `TopG`。#inferred[这一环节在本蓝图中未细究。] 输入 `VWin` 与 `Row0b` 是 #ref[第 6 节] 的主题。喂给 `zeroFreeAll_of_topG` 的宿主构造是 #ref[第 3 节] 的主题。通过对整棵源码树的搜索（而非 `#print axioms`——自动化阅读器无法运行它），Lean 源码不含任何公理、`sorry`、`opaque` 或 `native_decide`。
]

== 归约到本原特征

#defn("2.6", "本原特征与无零点性")[
  本原特征是三元组 $psi = (N, chi, "proof")$，其中 $N >= 1$，$chi$ 是模 $N$ 的本原狄利克雷特征。该结构名为 `PChar`。对 $theta in RR$ 置
  $ psi."ZeroFreeAbove"(theta) : arrow.l.r.double forall s in CC, theta < Re s ==> L(chi, s) eq.not 0. $
  记 `ZeroFreeAll` 为：每个本原特征 $psi$ 都满足 $psi."ZeroFreeAbove"(1/2)$。
]

#lean("Formalism.HC.PChar", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean")
#lean("Formalism.HC.ZeroFreeAll", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean")

#caution("2.7")[
  `ZeroFreeAbove` 的定义对平凡特征并未排除 $s = 1$。在该处 Lean 的值 $L(1, 1)$ 是 Mathlib 的 `riemannZeta` 在 1 处的取值，不是极点。该命题仍被证明，故无害。这只是与 #ref[定义 2.3] 的差别，后者去掉了数对 $(1, 1)$。
]

#thm("2.8", "本原情形推出全体特征")[若 `ZeroFreeAll` 成立，则 `EveryCharacter` 成立。]

#lean("UpperTheory.Top.imprimitive", "Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean")

#proof[
  设 $chi$ 是模 $N$ 的特征，$chi^ast$ 是诱导它的、导子为 $f bar.v N$ 的本原特征。取 $Re s > 1/2$。Mathlib 的 `LFunction_changeLevel` 给出
  $ L(chi, s) = L(chi^ast, s) product_(p bar.v N) (1 - chi^ast(p) p^(-s)). $
  因子 $L(chi^ast, s)$ 由假设非零（把它应用于 $chi$ 所附着的本原特征）。对每个素数 $p bar.v N$，有 $abs(chi^ast(p)) <= 1$ 且 $abs(p^(-s)) = p^(-Re s) < 1$（因 $Re s > 1/2 > 0$），故 $abs(chi^ast(p) p^(-s)) < 1$，每个欧拉因子非零。最后，$chi eq.not 1$ 迫使 $chi^ast eq.not 1$，故 $(1, 1)$ 处的极点不进入。
]

== 窗口形式的 Landau 判据

接下来的对象是携带零点信息的加权切比雪夫误差。以下所有定义都是 Lean 中的定义。

#defn("2.9", "切比雪夫误差")[
  令 $Lambda$ 为 von Mangoldt 函数，$gamma$ 为欧拉常数。对实数 $y >= 1$ 置
  $ S_zeta(y) = sum_(n <= y) Lambda(n) lr((y/n) - 1), quad G_zeta(y) = S_zeta(y) - y log y + (1+gamma) y. $
  对模 $N$ 的狄利克雷特征 $chi eq.not 1$ 置
  $ G_chi(y) = sum_(n <= y) Lambda(n) chi(n) lr((y/n) - 1) + y (L')/L (1, chi). $
  和式中只有 $n <= y$ 的项，故权为 $max(y/n - 1, 0)$。记 $Re G_chi$ 为其实部。
]

#lean("Formalism.Gz", "Formalism/StatementOC.lean")
#lean("Formalism.HC.An.gChi", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean")

这些是 $psi(y) - y$ 与 $psi(y, chi)$ 的光滑化（Cesàro 型）版本。项 $y (L')/L (1, chi)$ 是 $chi eq.not 1$ 时的主项。它是实常数乘 $y$，故对误差的量级有影响。#inferred[权 $(y/n - 1)^+$ 是素数计数测度的第一 Riesz 平均，这正是其 Mellin 变换为 $-(zeta'/zeta)(s) \/ (s(s-1))$ 的原因。]

#defn("2.10", [级别与加权误差 $G^Lambda$])[
  一个级别 $Lambda_0$ 由以下组成：
  - 一个含平凡特征、且在 $psi arrow.bar bar(psi)$ 下封闭的有限本原特征集 $K$；
  - 一个自然数 $o$；
  - 一个可选的“伪例外”特征 $psi_K in K$，它为奇且实。

  置 $K^ast = K minus {1}$。权为：若 $psi = psi_K$ 则 $w(psi) = 1$，否则 $w(psi) = 1/(3o+1)$。加权误差为
  $ G^Lambda(y) = G_zeta(y) + sum_(psi in K^ast) w(psi) Re G_psi(y). $
  对本原 $psi$，循环级别 $Lambda_psi$ 取 $K$ 为由“诱导 $⟨chi_psi⟩$ 中元素的本原特征”组成的集合，无 $psi_K$，且 $o = abs(⟨chi_psi⟩)$。此时所有权为 $1/(3o+1)$。
]

#lean("Formalism.HC.Level", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean")
#lean("Formalism.HC.Level.Gm", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean")
#lean("Formalism.HC.Level.cyc", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean")

主路径上只使用 $Lambda_psi$。带 $psi_K$ 的情形存在于定义与 Landau 机器中，在下文的整数形式里权为 $3o+1$。

下面的命题是整个论证的引擎。它是 Landau 定理的带显式特征族的形式。

#thm("2.11", "Landau，族形式")[
  设 $(c_i)_(i in I)$ 为本原特征，$I$ 上有对合 $tau$ 使 $c_(tau i) = bar(c)_i$。设 $S subset I$ 有限、在 $tau$ 下封闭，且对 $xi in S$ 有 $c_xi eq.not 1$。设 $R >= 1$ 为整数，$0 < theta < 1$，$C_0, y_0 in RR$。假设对一切 $y >= y_0$
  $ R G_zeta(y) + sum_(xi in S) Re G_(c_xi)(y) <= C_0 y^theta. $
  则对每个满足 $Re s > theta$ 的 $s$：$zeta(s) eq.not 0$，且对所有 $xi in S$ 有 $L(c_xi, s) eq.not 0$。
]

#lean("Formalism.HC.landau_family", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean")

#proof(uses: ref[定义 2.9])[
  置 $zeta_1(s) = (s-1) zeta(s)$，它整；且
  $ P(s) = zeta_1(s)^R product_(xi in S) L(c_xi, s). $
  则 $P$ 整，且在 $Re s >= 1$ 上非零。对 $x >= 1$ 定义
  $ H(x) = C_0 x^theta - lr(R G_zeta + sum_xi Re G_(c_xi))(x). $
  假设恰好说 $H >= 0$。这是唯一用到的正性。

  对 $Re s > 1$，$-zeta'/zeta$ 与 $-L'/L (c_xi, dot.op)$ 的狄利克雷级数给出 $H$ 的 Mellin 变换的封闭形式。用 $tau$ 把 $chi$ 换成 $bar(chi)$（使对 $S$ 的和为实），得
  $ integral_1^oo H(x) x^(-s-1) dif x = (P'(s)\/P(s) - (a + b s))/(s(s-1)) + C_0/(s - theta) quad quad (Re s > 1) $
  其中 $a, b$ 为适当常数。项 $C_0/(s-theta)$ 是 $C_0 x^theta$ 的变换。#inferred[这一常数对应关系出自作者本人。]该恒等式在 Lean 中作为 `mellinSgen`、`mellinElem` 被证明。核心是 `landau_entire`：若 $P$ 整、在 $Re s >= 1$ 上非零，且 $H >= 0$ 可测并满足该 Mellin 恒等式，则 $P$ 在 $Re s > theta$ 无零点。
]

#rem("2.12", "为何单侧就够")[
  #inferred[这是我们对 `landau_entire` 结构的解读，并非逐行核对。]论证是关于非负函数 Mellin 变换的 Landau 引理。令 $F(s)$ 为恒等式左端。因 $H >= 0$，$F$ 在收敛半平面上解析，且收敛横坐标是 $F$ 的实奇点（`landauEq` 把恒等式向左延拓）。右端在 $P$ 无零点处解析。$P$ 的实零点 $rho in (theta, 1)$ 给出 $P'/P$ 的一个正留数极点。由于 $rho(rho - 1) < 0$，这使 $F(sigma) arrow.r -oo$（当 $sigma ↘ rho$）。但 $F(sigma) >= 0$ 对收敛区域中的实 $sigma$ 成立。所以 $theta$ 右侧没有实零点，从而没有奇点，从而 $F$ 在整个 $Re s > theta$ 上解析。复零点会成为 $F$ 的极点，故也没有。

  不需要对 $G$ 的下界。权的正性（$R + sum Re chi(n) >= 0$）并不被 Landau 使用。它正是使上界能在素数一侧得到证明的原因（见 #ref[第 3 节]）。
]

由族形式出发，Lean 库导出级别版本。

#lem("2.13", "级别形式的 Landau")[
  设 $Lambda_0$ 是一个级别，$0 < theta < 1$，$y_0 in RR$。若对一切 $y >= y_0$ 有 $G^Lambda(y) <= y^theta$，则对一切 $psi in K$ 有 $psi."ZeroFreeAbove"(theta)$。
]

#lean("Formalism.HC.zero_free_of_Chebyshev_growth", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean")

#proof(uses: ref[定理 2.11])[
  对指标集 ${(psi, j) : psi in K^ast, 1 <= j <= k_psi}$ 应用 #ref[定理 2.11]。取 $k_psi = 3o+1$（若 $psi = psi_K$）否则 $k_psi = 1$，$R = 3o+1$，$tau(psi, j) = (bar(psi), j)$。则 $R G^Lambda = R G_zeta + sum_psi k_psi Re G_psi$。界 $G^Lambda <= y^theta$ 以 $C_0 = R = 3o+1$ 给出假设。
]

只需要在窗口上成立这个界，而不需要它对每个大的 $y$ 成立。这正是让素数一侧的论证能在有限信息下运作的关键。

#thm("2.14", "Landau，窗口形式")[
  设 $F$ 是由模 $N_i$ 的特征 $chi_i$ 与权 $a_i > 0$ 组成的有限族，其中每个 $i$ 满足 $N_i = 1$ 或 $chi_i eq.not 1$。置
  $ G_F(y) = sum_i a_i Re G_(chi_i)(y), $
  其中 $N_i = 1$ 的项为 $G_zeta$。设 $0 < theta < 1$，$delta > 0$，$C in RR$。假设对每个 $Y_0$ 存在 $Y >= Y_0$ 使
  $ G_F(y) <= C y^theta quad upright("对一切") y in [Y, Y^(1+delta)]. $
  则对所有 $i$ 与所有满足 $Re s > theta$ 的 $s$ 有 $L(chi_i, s) eq.not 0$。
]

#lean("Deduction.zeroFree_of_rpow_window", "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean")

#proof(uses: ref[定理 2.11])[
  Lean 通过 `Deduction.lemmaL` 与 `landau_window` 证明它。假设先被转化为窗口假设 `WindowHyp`：在 $[Y, Y^(1+delta)]$ 上有一个非负控制函数 $R >= G_F$，满足对每个 $eta > 0$ 有 $integral R(y) y^(-theta-1) dif y <= Y^eta$。证明然后用由 Mellin 恒等式得到的解析函数 $Phi$ 的高阶泰勒系数，阶数 $k$ 约为 $log Y$。尾部估计（`landau_tails`）与增长矛盾（`landau_growth_contra`）给出形如 $c\/d^k <= M\/e^k + C e^(eta U)\/E^k$ 的不等式对无穷多个 $k$ 成立。若零点位于 $theta$ 右侧，这对大的 $k$ 不成立。#inferred[泰勒系数机制的梗概来自各引理的陈述，而非来自阅读它们的证明。]若 $Re s >= 1$ 则结论经典，故只需对 $theta < Re s < 1$ 作论证。
]

#lean("Deduction.lemmaL", "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean")

主路径上使用的 Lean 版本是级别版。它就是谓词 `FormB`。

#defn("2.15", "窗口谓词与 FormB")[
  集合 $S subset RR$ 有指数 $lambda$ 的窗口，若对每个 $y$ 存在 $Y >= y$ 使 $[Y, Y^lambda] subset S$。对级别 $Lambda_0$ 与 $lambda > 1$，$"FormB"_lambda(Lambda_0)$ 说：对所有 $0 < theta < 1$，若 ${x : G^Lambda(x) <= x^theta}$ 有指数 $lambda$ 的窗口，则对一切 $psi in K$ 有 $psi."ZeroFreeAbove"(theta)$。$"FormB"(Lambda_0)$ 表示对一切 $lambda > 1$ 都有 $"FormB"_lambda$。
]

#lean("Formalism.HC.Level.FormBAt", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean")

#cor("2.16", "每个级别满足 FormB")[对每个级别 $Lambda_0$，$"FormB"(Lambda_0)$ 成立。]

#lean("UpperTheory.ComparisonâĆĆ.formB", "Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean")

#proof(uses: ref[定理 2.14])[
  引理 `level_family` 把级别变成 #ref[定理 2.14] 意义下的族 $F$，满足 $G_F = G^Lambda$ 并有相同的无零点半平面。以 $delta = lambda - 1$、$C = 1$ 应用 #ref[定理 2.14]。
]

#rem("2.17", none)[
  只含 $zeta$ 的类比也已被形式化。`riemann_hypothesis_of_power_bound` 说：若对所有小 $epsilon$ 与大 $x$ 有 $G_zeta(x) <= x^(1/2 + C epsilon)$，则 RH 成立。它使用 `zetaLandauEps` 与同样的 Mellin 论证。#inferred[它不在 #ref[定理 2.1] 的路径上，后者使用级别版本以覆盖全体特征。]
]

#lean("Formalism.LFunctionChainParameters.ConditionalMainTheorem.riemann_hypothesis_of_power_bound", "Formalism/SizeWindowBrackets/ChainSlopeWindows/RiemannHypothesisOfPowerBound.lean")

== 目标界

现在陈述论文其余部分必须证明的东西。指数取自 Lean 文件。

#defn("2.18", "窗口幂界")[
  设 $psi$ 为本原特征，$Lambda_psi$ 为其循环级别。称 $psi$ 具有窗口幂界，若存在常数 $A > 0$ 与 $epsilon_1 > 0$，使得对每个 $epsilon in (0, epsilon_1)$，存在集合 $W_epsilon subset [1, oo)$ 与 $x_1$，满足：
  (i) $W_epsilon$ 有指数 3/2 的窗口；
  (ii) 对 $W_epsilon$ 中一切 $x >= x_1$ 有 $G^(Lambda_psi)(x) <= x^(1/2 + A epsilon)$。

  在 Lean 证明中 $A = e_D + e_L + 7$，其中 $e_D$、$e_L$ 是来自宿主构造的常数，而 $W_epsilon$ 是由以 $epsilon$ 标号的宿主族的集合 `Win`。
]

#lean("Formalism.HC.ChebyshevInequalityOnWindows", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean")
#lean("Formalism.HC.ChebyshevInequalityAtWindowScale", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean")

这是两个 Lean 谓词的打包改述。在 Lean 中它们对抽象的宿主族族 `Fam` 陈述，带一个携带尺寸数据的“tied”谓词。第一个谓词给出 (ii)，第二个给出 (i) 与族的存在性。

#lem("2.19", "窗口幂界推出无零点性")[若 $psi$ 具有窗口幂界，则对每个 $Re s > 1/2$ 有 $L(chi_psi, s) eq.not 0$。]

#lean("Formalism.HC.level_of_tiedWin", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean")

#proof(uses: ref[推论 2.16 与定义 2.18])[
  固定满足 $Re s > 1/2$ 的 $s$，置 $sigma = min(Re s - 1/2, 1/2)$。选 $epsilon < epsilon_1$ 使 $A epsilon <= sigma/2$。则对 $W_epsilon$ 中 $x >= max(x_1, 1)$ 有 $G^Lambda(x) <= x^(1/2 + A epsilon) <= x^theta$，其中 $theta = 1/2 + sigma/2 < Re s$。于是 ${x : G^Lambda(x) <= x^theta}$ 包含 $W_epsilon$ 的尾部，且它有指数 3/2 的窗口。由 #ref[推论 2.16]，$psi."ZeroFreeAbove"(theta)$。因 $theta < Re s$，断言得证。
]

最终命题的假设用到 Lean 库的三个对象。这里只描述它们。

- `HostExW(lambda, P)`：对每个 $epsilon < 1/52$，存在常数与一个带窗口 $[Y, Y^lambda]$ 的尺度集合，使该集合中每个尺度上都载有一个“宿主”（一个秩数据、一个宿主域数据与一个素数 $q_0$），满足尺寸界与性质 $P$。宿主在 #ref[第 3 节] 构造。
- 要求 #ref[GChi]$(psi)$：性质 $P$ 说宿主满足 $Lambda_psi$ 的显式公式误差条件（`EAtH`），且其域 $E$ 有小的伽罗瓦上同调群 `VVle(E, t, b)`（#ref[第 6 节] 的意义下）。
- `TopG`：对每个 $lambda > 1$ 与每个宿主要求 $G$，若 `HostExW(lambda, G)` 且相应族满足尺寸假设 `HypV`，则满足 $G$ 的族类是“族连通”的。族连通指：存在常数 `eD`、`eL`、$epsilon_1$，且对每个小 $epsilon$，存在族，其成员在其窗口集合中的所有 $x$ 上满足链式 tied 尺寸界。

#lean("Formalism.HC.HostExW", "Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean")
#lean("UpperTheory.Top.GChi", "Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean")
#lean("UpperTheory.Top.TopG", "Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean")

#prop("2.20", "论文其余部分的目标")[
  假设 `TopG`，并假设对每个本原特征 $psi$ 有 $"HostExW"(3/2, #ref[GChi] (psi))$。则 `ZeroFreeAll` 成立：每个本原狄利克雷 L 函数在 $Re s > 1/2$ 无零点。更精确地说，在这些假设下，每个本原特征都有 #ref[定义 2.18] 的窗口幂界（窗口 $[Y, Y^(3/2)]$），且界为
  $ G^Lambda(x) <= x^(1/2 + (e_D + e_L + 7) epsilon). $
]

#lean("UpperTheory.Top.zeroFreeAll_of_topG", "Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean")

#proof(uses: ref[定理 2.14、3.6、3.8，推论 2.16，引理 2.19，定义 3.1])[
  Lean 证明是对 `zeroFreeOn_of_tiedWin_cyc` 以循环级别 $Lambda_psi$ 与 $lambda = 3/2$ 的直接调用。它对每个 $psi$ 需要三个输入。

  + 窗口化切比雪夫不等式 `ChebyshevInequalityOnWindows`（即 (ii)）。它来自 `level_gm_le_on_family_scales`，后者使用 `core_gm` 与 `ch_core`。后者是 #ref[第 3 节] 的显式公式型步骤（#ref[定理 3.8]），连同其平衡恒等式 #ref[定理 3.6]。
  + Landau 窗口形式 $"FormB"(Lambda_psi)$，来自 #ref[推论 2.16]。
  + 族与窗口的存在性 `ChebyshevInequalityAtWindowScale`（即 (i)）。它由 `TopG` 以 $G = #ref[GChi] (psi)$、$lambda = 3/2$ 与假设 $"HostExW"(3/2, #ref[GChi] (psi))$ 得到。

  于是 #ref[引理 2.19] 给出每个 $psi$ 处的无零点性。
]

#rem("2.21", "常数 3/2、7 与 1/52")[
  - #inferred[$lambda = 3/2$ 或许可以换成 $(1, 2)$ 中的任何数；Lean 证明在 `winPairs` 与 `supplyChi` 中固定了 3/2。]只有 `zeroFreeAll_of_topG` 对一般 $lambda$ 陈述。它必须大于 1（为了 `HostExW` 与 #ref[定理 2.14]），且必须小于 2，因为输入 `VWin` 只在窗口 $[Y, Y^2]$ 上可用，而重标度 $x = k x'$ 要付出 $(k W)^(3/2) <= W^2$ 的代价，即 $k^3 <= W$（#ref[第 6 节]）。
  - $1/2$ 是单侧界的基础指数。令 $epsilon arrow.r 0$ 便得到每个 $theta > 1/2$。
  - $7 = 3 + 3 + 1$：$C = e_D + e_L + 3$ 被喂给 `ch_core`，后者再损失 $+3$，再有一个 $epsilon$ 吸收 $"SigA" <= 4^o x^(1/2 + epsilon)$（`core_gm`）。
  - $epsilon < 1/52$：$1/52$ 是使指数 $6.5 + 19 epsilon$ 保持在 6.87 之下的最大单位分数 $1\/N$（$epsilon = 1/51$ 时得 $6.8725 > 6.87$）。
]

== 传递下去的东西

- #ref[命题 2.20] 是通往论文其余部分的接口。要完成证明，只需对每个本原特征 $psi$ 提供假设 $"HostExW"(3/2, #ref[GChi] (psi))$，以及单独一条命题 `TopG`。
- #ref[第 3 节] 构造宿主：域 $E$、素数 $q$、$d$，以及把正素数和的上界转化为 $G^Lambda$ 的界的恒等式（#ref[定理 3.6]、#ref[定理 3.8]、#ref[定理 3.14]）。
- #ref[第 4–6 节] 给出素数和的上界，以及宿主中 `VVle` 的微小性（`VWin`，#ref[定理 6.4]）。
- #ref[第 7 节] 列出被用作工具的大型经典与现代定理。

于是 #ref[定理 2.1] 与 #ref[定理 2.4] 如上由 #ref[定理 2.8] 与 #ref[命题 2.20] 得出。
