// ch3.typ —— 第 3 章 宿主域、平衡恒等式与辅助素数
#import "lib.typ": *
#pagebreak(weak: true)

= 宿主域、平衡恒等式与辅助素数

本章是证明的素数一侧。最终目标是对 $Re s > 1/2$ 证明 $L(s, chi)$ 无零点。由一个 Landau 型论证（#ref[第 2 章]），只需对一个由光滑化切比雪夫误差构成的正组合 $"Gm"(x)$ 证明单侧界 $"Gm"(x) <= x^(1/2 + O(epsilon))$。本章把这个目标转化为：在一个恰当选取的数域上，关于一个显式正素数和 $"ASK"$ 的命题。

计划分四部分。首先构造数域（宿主）与两个辅助素数 $q$、$d$。其次证明一个精确恒等式（#ref[定理 3.6]）：$"ASK"$ 减去一个显式主项是诸切比雪夫误差的有限 Fourier 平均。第三，#ref[定理 3.8] 说明 $"ASK"$ 的上界给出 $"Gm"$ 的界。第四，证明辅助素数存在。这要用到一个零密度估计（#ref[定理 3.18]）、Siegel 定理与一个平方平均论证。$"ASK"$ 自身的上界来自格一侧（#ref[第 5 章]）。

== 宿主域

宿主是一个伽罗瓦 CM 域 $E$，其伽罗瓦群是显式的。记 $"HGrp"_e = (ZZ\/2^(e+2))^times\/⟨-1⟩$。这是 $QQ(zeta_(2e+2))$ 的实子域的伽罗瓦群。

#defn("3.1", "宿主域")[
  一个标架（frame）$phi$ 由以下组成：一个整数 $e >= 2$；一个阶为 $phi dot.op "ord"$ 的有限交换群 $A = phi dot.op "A"$；一个满射 $h : A arrow.r "HGrp"_e$；以及一个生成元 $a_0 in A$，满足：$h(k a_0) = 0$ 蕴含 $k a_0 = 0$（对一切 $k in ZZ$）。置 $G_phi = ({plus.minus 1} times {plus.minus 1}) times A$，按乘法记。令 $"cc" in G_phi$ 为复共轭（$A$ 分量平凡、符号分量非平凡；#inferred[具体符号未读出]），$"iod" = ((1, -1), 1)$ 为 $d$ 处的惯性生成元。

  $phi$ 的一个宿主（即结构 `HostAx`）是如下数据。

  - 素数 $q$、$d$ 与一个整数 $Q_S$：满足 $2^(e+2) bar.v Q_S$、$"gcd"(Q_S, q d) = 1$，且对每个整除 $Q_S$ 的奇素数 $ell$ 有 $lr((-d)/ell) = 1$。
  - 一个伽罗瓦数域 $E\/QQ$，连同同构 $"Gal"(E\/QQ) tilde.op G_phi$。
  - 一个元素 $sqrt(-d) in E$，满足 $lr((sqrt(-d)))^2 = -d$ 且 $sigma sqrt(-d) = epsilon_2(sigma) sqrt(-d)$，其中 $epsilon_2$ 是伽罗瓦群的第二个符号坐标。
  - 一个嵌入 $E arrow.r.hook QQ(zeta_(Q_S q d))$，以及一个 Artin 映射 $(ZZ\/Q_S q d)^times arrow.r G_phi$，满足 $"art"(-1) = "cc"$。
  - Frobenius、惯性与分解群事实的完整清单：在不整除 $Q_S q d$ 的 $p$ 处 Frobenius 为 $"art"(p)$；$d$ 处的惯性为 ${1, "iod"}$；素数 $q$ 与整除 $Q_S$ 的素数的分解群落在 $Psi = "ker"(epsilon_2)$ 内；等等。

  推论事实（域 `der`）：$E$ 是 CM 域，$[E : QQ] = 4 phi."ord"$，且极大全实子域 $F$ 的次数为 $2 phi."ord"$。
]

#lean("HostAx", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean")
#lean("HostRaw", "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean")

用平常的话说：$E$ 是在分圆域内由同余条件切出来的。这一点由谓词 `IsChiField` 精确表达，它就是伽罗瓦一侧（#ref[第 6 章]）所看到的东西。

#defn("3.2", [ψ-域])[
  设 $psi$ 为本原狄利克雷特征，$e, q, d$ 为整数。称数域 $E$ 是 $(e, q, d)$ 的 $psi$-域，若存在 $N$，满足 $2^(e+2) bar.v N$、$"cond"(psi) bar.v N$、$q bar.v N$、$d bar.v N$，存在 $N$ 次本原单位根 $zeta$ 与嵌入 $j : E arrow.r.hook QQ(zeta)$，使得对每个满足 $tau zeta = zeta^a$ 的 $tau in "Gal"(QQ(zeta)\/QQ)$ 有
  $ tau "fixes" j(E) arrow.l.r.double quad a equiv plus.minus 1 mod 2^(e+2) ∧ psi(a) = 1 ∧ lr((a)/q) = 1 ∧ lr((a)/d) = 1. $
]

#lean("IsChiField", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")

于是 $E$ 是四块域的合成。

- 实二次幂分圆域 $QQ(zeta_(2e+2))^+$，其伽罗瓦群为 $"HGrp"_e$。
- 由 $psi$ 切出的域（即 $psi$-域，由 $psi$ 在群上的取值生成）。
- $QQ(sqrt(-q))$，由 $lr((dot.op)/q)$ 切出。#inferred[符号是 $-q$，因为在容许对中 $q equiv 3 mod 8$。]
- $QQ(sqrt(-d))$，由 $lr((dot.op)/d)$ 切出，其中 $d equiv 7 mod 16$。

导子是 $Q_S q d$，次数是 $4 phi."ord"$。标架的尺寸通过页条件 $2^e approx x^(2 + 8 epsilon)$（`PageN`）与尺度 $x$ 相绑定。Lean 数据带有秩参数 $t <= x^400$。输入 `VWinAt` 以 401 陈述，多出的 1 为 `winPairs` 中的重标度 $x = k x'$ 买单（$k^400 <= x'$）。

#defn("3.3", "宿主供给")[
  对 $lambda > 1$ 与宿主上的要求 $P$，$"HostExW"(lambda, P)$ 的含义如下。对每个 $0 < epsilon < 1\/52$，存在常数 $C_(T_2), C_8, C_5, c_6, C_b, x_0$ 与一个尺度集合 $S$，后者对任意大的 $Y$ 都包含一个窗口 $[Y, Y^lambda]$。对 $S$ 中每个尺度 $x >= x_0$，存在秩数据 $R$、$R$ 的一个宿主 $H$ 与一个素数 $q_0$，满足 `RankVal`、`HostGood` 与要求 $P$。
]

#lean("HostExW", "Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean")

证明将使用 $lambda = 3/2$ 与要求 $(G_chi)."req"$，它说宿主满足特征 $chi$ 的显式公式条件 `EAtH`，以及 Tate–Shafarevich 型和的界 `VVle`。常数 $1\/52$ 是使指数 $6.5 + 19 epsilon$ 保持在 6.87 之下的最大单位分数 $1\/N$（$epsilon = 1\/51$ 时得 $6.8725 > 6.87$）。

== 量 ASK 与 MAIN

置 $E_0 = ZZ\/2 times ZZ\/2$，并设 $H$ 为有限交换群。相关的伽罗瓦群是 $E_0 times H$。令 $Phi subset E_0 times H$ 为第一个坐标的核，并令 $chi_C : E_0 times H arrow.r {plus.minus 1}$ 为核为 $Phi$ 的二次特征。#inferred[$E_0$ 的第一坐标对应本章抽象设定中的 $QQ(sqrt(-d))$；在上面的标架 $G_phi$ 中两个符号坐标的次序是互换的。Lean 代码在 `ArithData` 内部不需要这个对应。]记 $"cconj" = ((1,1), 0)$ 为复共轭，$"sgc" _0 = ((1, 0), 0)$ 为 $d$ 处的惯性生成元，并置 $"partner"_t (g) = "cconj" + g + "topPl"(t)$。

#defn("3.4", "算术数据与和 ASK")[
  一个 `ArithData` $D$ 是一对素数 $q_1, d$，并对每个素数 $p$ 带有一个惯性子群 $I_p <= E_0 times H$ 与一个 Frobenius 元 $"frob"_p in E_0 times H$。称素数 $p$ 是惯性的（inert），若 $p$ 为素数、$p in.not {2, q_1, d}$、且 $"frob"_p in.not Phi$。对 $a > 0$、$t in H$、$N in NN$ 与权 $w : E_0 times H arrow.r RR$，置
  $ "askP"(p) = sum_(1 <= i <= N, i "frob"_p in.not Phi) max(a/(p^i) - w("partner"_t (i "frob"_p)), 0), $
  $ "askD" = sum_(i=1)^N sum_(g in.not Phi, g - i "frob"_d in I_d) max(a/(d^i) - w("partner"_t (g)), 0), $
  $ "ASK"(D, N, a, t, w) = sum_(p <= N, p "惯性") 2 log p dot.op "askP"(p) + log d dot.op "askD". $
]

#lean("ASK", "Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean")

用平常的话来读#inferred[（这一改述对照#ref[定理 3.6] 的代数核对过，并非 Lean 中陈述）]：
$ "ASK" = sum_(n <= N) Lambda(n) (1 - chi_(-d)(n)) lr((a)/n - w_"class"(n))_+. $

这里 $i "frob"_p in.not Phi$ 意味着 $i$ 为奇数且 $p$ 在 $QQ(sqrt(-d))$ 中惯性。于是 $1 - chi_(-d)(p^i) = 2$，这解释了因子 $2 log p$。在 $p = d$ 处有 $chi_(-d)(d) = 0$，这解释了单个的 $log d$。所以 $"ASK"$ 是在 $QQ(sqrt(-d))$ 的非平凡类上对素数幂取的非负项之和。辅助素数的选取使得每个 $<= Y^(epsilon\/5)$ 的奇素数与 $q$ 都整除 $d + 1$。于是 $-d$ 在它们每个模下都是平方，故它们全都分裂，而惯性素数都位于 $Y^(epsilon\/5)$ 之上。

对 $E_0 times H$ 的特征 $psi$，狄利克雷型取值 `primValD`(ψ, n) 是对满足 $p^k parallel n$ 的素数幂、在陪集 $k "frob"_p + I_p$ 上取 $psi$ 平均后的乘积。光滑化切比雪夫误差是
$ G_psi(y) = sum_(n <= y) Lambda(n) "primVal"_D(psi, n) lr((y)/n - 1) + y ell(psi) quad (psi eq.not 0), $
而 $G_0 = G_z$ 是 $zeta$ 相应的误差。这里 $ell(psi)$ 代表 $L'\/L (1, psi)$（在 Lean 陈述中是一个自由参数，即 $psi$ 的函数）。

#lean("GPsi", "Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean")

#defn("3.5", "主项")[
  设 $ell$ 如上。对 $a > 0$ 与在 $Phi$ 上为正的 $w > 0$，
  $ "MAIN"(ell, a, w) = a lr(log a - 1 - gamma + ell(chi_C) - 1/abs(Phi) sum_(rho in Phi) log w(rho)), $
  其中 $gamma$ 为欧拉常数，且 $ell(chi_C) = L'\/L (1, chi_(-d))$。
]

#lean("MAIN", "Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean")

作为一个合理性检查#inferred[（不在 Lean 中）]：$sum_(n <= Y) Lambda(n)(Y\/n - 1) = Y log Y - (1 + gamma) Y + G_z(Y)$，而对非平凡 $chi$，带 $chi$ 的同一个和给出 $-Y L'\/L (1, chi) + G_chi(Y)$。取 $Y = a\/w$ 并乘以 $w$，恰好得到 $"MAIN"$ 的形状。同一个表达式也从几何一侧出现，是四项（一个 log-阶乘、一个 Chowla–Selberg 周期、一个 Hecke 素数与一个误差项）的精确相消。那是#ref[第 5 章] 的内容。

== 平衡恒等式

结构 `HostFactsS`(D, S) 打包了下文使用的事实。它包含：$d$ 是素数；$2 in S$、$q_1 in S$、$d in.not S$；$D$ 在 $S union {d}$ 之外不分歧；$S$ 中素数处的 Frobenius 落在 $Phi$ 内；$d$ 处的惯性为 ${0, "sgc"_0}$。

#lean("HostFactsS", "Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean")

#inferred[源码中只读了前四个字段；其余取自该结构在各证明中的角色。]

#thm("3.6", "平衡恒等式")[
  设 $D$ 是 $H$ 上的算术数据，满足 `HostFactsS`(D, S)。设 $a > 0$、$t in H$，且 $w : E_0 times H arrow.r RR$ 在 $Phi$ 上为正、并对一切 $rho in Phi$ 有 $a\/w(rho) <= N$。则在 $CC$ 中
  $ "ASK"(D, N, a, t, w) - "MAIN"(ell, a, w) = "De"(D, ell, a, t, w), $
  其中
  $ "De" = 1/abs(Phi) sum_(g in.not Phi) sum_(psi in hat(E_0 times H)) overline(psi(g)) w("partner"_t g) G_psi lr((a)/(w("partner"_t g))). $
]

#lean("ch_balance", "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean")

#proof(uses: ref[定义 3.4 与 3.5])[
  这是 $E_0 times H$ 上的有限 Fourier 分析。第一，特征在素数幂上的正交性（引理 `OrthoUnram`、`OrthoRam`）把 $"ASK"$ 改写为
  $ 1/abs(Phi) sum_(g in.not Phi) sum_psi overline(psi(g)) sum_(n <= N) Lambda(n) "primVal"_D(psi, n) lr((a)/n - w("partner"_t g))_+. $
  这就是 `AskExpansion`。第二，引理 `sum_cut` 求出每个内和：它等于 $w S_psi(a\/w)$，其中 $S_psi(y) = sum_n Lambda(n) psi(n) (y\/n - 1)_+$，且对 $psi eq.not 0$ 有 $S_psi(y) = G_psi(y) - y ell(psi)$。第三，剩下的项 $y ell(psi)$ 与 $G_z$ 的主项用 `ColourSum` 求和：$overline(psi(g))$ 对 $g in.not Phi$ 的和当 $psi = 0$ 时为 $abs(Phi)$、当 $psi = chi_C$ 时为 $-abs(Phi)$、否则为 0。这产生项 $a(log a - 1 - gamma)$ 与 $a ell(chi_C)$。映射 $"partner"_t$ 是从 $Phi$ 的补集到 $Phi$ 的双射（`PartnerBij`），它把 $log w("partner"_t g)$ 的和变成 $log w(rho)$ 在 $Phi$ 上的平均。
]

该恒等式是精确的，没有误差项。所有分析都藏在诸 $G_psi$ 的尺寸里。在 $H$ 上平凡的特征 $psi$ 对应 $zeta$ 与 $L(s, chi_(-d))$。#inferred[其余低阶特征中哪些属于 $q$ 与 $d$ 处的二次域，未与定义对照。]更高阶的特征对应目标 $chi$。

== 从 ASK 的上界到 G_m 的界

下一个定理是通往格一侧的桥。它以下述上界为假设
$ "gap"_A(u) = sum_(t in TT) sum_(j < m) lr("ASK"(D, N, a_t, t, w_(u,j)) - Re "MAIN"(ell, a_t, w_(u,j))) <= x^(C epsilon) "Err"(x), quad quad (3.1) $
对每个 $u in A_0$ 成立，其中 $"Err"$ 是显式括号
$ "Err" = n_T a_E lr(1 + m^2/k) + m lr(2 n m b x^epsilon + (n_(T_2) k b x^epsilon)/(n(n x^(-epsilon)))) $
（这里 $n = abs(H)$、$n_T = abs(TT)$、$n_(T_2) = abs(T_2)$；`errorBracketSizeWindows`）。它给出诸 $G_psi(x)$ 的加权和的一个界。

#lean("errorBracketSizeWindows", "Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean")
#lean("gapA", "Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean")

#defn("3.7", "保留和与余项")[
  设 $A_0 <= H$ 为子群，`PsiA`(A₀) 为满足 $psi(0, s) = 1$（$s in A_0$）的特征 $psi$ 的集合，且 $K_p subset "PsiA"(A_0)$ 为由“保留”特征组成的有限集。对常数 $c$，置：若 $psi$ 在 $H$ 上平凡则 $"wt"(psi) = 1$，否则 $"wt"(psi) = c$。
  $ "GmA"(x) = sum_(psi in K_p) "wt"(psi) Re G_psi(x), quad quad "SigA"(x) = sum_(psi in "PsiA"(A_0) ∖ K_p) norm(G_psi(x)). $
]

#lean("GmA", "Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean")
#lean("SigA", "Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean")

#thm("3.8", "核心估计")[
  对一切满足 $C >= 0$、$epsilon > 0$、$abs(c) <= 1$ 的 $C, epsilon, C_E, K_o, c, M$，存在 $x_1$，使得对一切 $x >= x_1$ 下述成立。设 $H$ 为有限交换群，$D$ 为满足 `HostFactsS`(D, S) 的算术数据。假设尺寸条件 `SizesA`、细尺度界 `ThinScales`、条件 `CostWindows`、`RestSize`、特征条件 `CharsA`、窗口界 $m <= x^(1/2 + epsilon\/2)$ 与 $x m <= k$，以及 (3.1) 对每个 $u in A_0$ 成立。则
  $ "GmA"(x) <= x^(1/2 + (C + 3) epsilon) + "SigA"(x). $
]

#lean("ch_core", "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean")

这些假设用文字说就是：

- `ThinScales`：$norm(G_psi(y)) <= y^theta$ 对一切 $psi$ 与一切 $y >= X'\/3$。这是一个便宜的弱界。
- `CharsA`：$0 in K_p$；每个保留的 $psi$ 在 $A_0$ 与 $"sgc"_0$ 上平凡；$abs("PsiA"(A_0)) <= M$；对在 $H$ 上非平凡的保留 $psi$，有 $sum_(t in TT) psi(0, t) - c abs(TT) <= M x^(-1 + epsilon) abs(TT)$（集合 $TT$ 的均匀分布）；对保留的 $psi$ 有 $norm(ell(psi)) <= K_o$，对其余的有 $<= C_E log x$。
- $a_t$、$w$、$b$、$b'$ 的尺寸（`SizesA`）：$abs(a_t \/ b - x) <= 1$；权在“厚”类上约为 $b$、在其余类上至多 $2 b'$；且 $a_t \/ w <= N$。

#proof(uses: ref[定理 3.6 与 5.27])[
  固定 $u in A_0$ 与 $t in TT$。应用 #ref[定理 3.6] 并对 $u in A_0$、$t in TT$ 取平均（引理 `sum_Th`、`th_le`）。正交性分离出 $sum_(psi in "PsiA") psi(e_1 t) G_psi$。对权 $w$ 小的类，细界平凡地控制 $G_psi$。对厚类，用 $y$ 方向的 Lipschitz 估计（`LipW`、`DerivInt`）比较 $G_psi(a_t \/ w)$ 与 $G_psi(x)$，因为 $a_t \/ b$ 与 $x$ 相差不超过 1。$TT$ 的均匀分布把 $psi(0, t)$ 的平均变成权 $"wt"(psi)$。结果是：$"GmA"(x)$ 至多等于 gap 界（假设 (3.1)）除以因子 $P = n_T m b n_(T_2) \/ (2 n)$，再加上未保留的特征。窗口尺寸条件随后给出指数。项 $x\/m$（来自 $a_E (1 + m^2\/k)$）与项 $m$ 在 $m approx x^(1\/2)$ 处平衡，给出 $1\/2$。其余损失加起来是 $x^(21 epsilon\/8) dot 2^6 <= x^(3 epsilon)$，只要 $2^6 <= x^(3 epsilon\/8)$（这就是指数中的常数 $C + 3$）。保留特征带着有界的 $ell$-值，故没有进一步损失。
]

#rem("3.9", none)[
  该定理把 (3.1) 作为假设。它由 `ch_top` 供给：后者把格界 $"ASK"_u - "Main"_u <= x^(C epsilon) "Err"$（来自 #ref[第 5 章] 的 #ref[定理 5.27]）改写成 (3.1) 的形式。
]

#lean("ch_top", "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean")

#thm("3.10", "逐特征界")[
  设 $Lambda$ 是一个级别（由本原特征组成的有限集 `KEPT`，带计数 $o$ 与可选例外特征 $psi_K$），并置
  $ G^Lambda_m (y) = G_z(y) + sum_(psi in "KEPT" ∖ {1}) "wt"(psi) Re G_psi(y), $
  其中若 $psi = psi_K$ 则 $"wt"(psi) = 1$，否则 $"wt"(psi) = (3o + 1)^(-1)$。对一切常数 $e_D, e_L, K, c_"HH", e_K, C$ 与 $epsilon > 0$，存在 $x_1$，使得对一切 $x >= x_1$、每个标架 $phi$、$phi$ 的宿主 $H$ 与 $TT subset phi dot.op "A"$，若 `EAtH`（宿主的显式公式条件）与 `CoreAtH`（格一侧数据，含 (3.1)）成立，则
  $ G^Lambda_m (x) <= x^(1/2 + (e_D + e_L + 7) epsilon). $
  这里 $e_D, e_L >= 0$，作为 `CoreAtH` 的一部分。
]

#lean("UpperTheory.ComparisonâĆĆ.core_gm", "Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean")

#proof(uses: ref[定理 3.8 与命题 3.11])[
  以 $C = max(e_D + e_L, 0) + 3$、$c = (3o + 1)^(-1)$、$M = 4^o$ 与 $K_o = sum_(psi in "KEPT") norm(L'\/L (1, psi))$ 应用 #ref[定理 3.8]。`CoreAtH` 中的格数据供给 #ref[定理 3.8] 的全部假设（结构 `U0`、`Top`、`m`、`f`、窗口界），而 `ch_top` 供给 (3.1)。保留特征经由 `ReadsKept` 与宿主群的特征等同。余项 `SigA` 由 #ref[命题 3.11] 控制。指数是 $1/2 + (C + 3) epsilon$，其中 $C + 3 = max(e_D + e_L, 0) + 6$，多出的 $epsilon$ 吸收 $4^o x^(1/2 + epsilon) <= x^(1/2 + 2 epsilon)$。#inferred[最后的簿记未逐行追踪。]
]

#prop("3.11", "余项 SigA")[
  在如上的 $Lambda$、$phi$、$H$、$TT$、$x$、$epsilon$、$C$ 下，若 `EAtH` 成立且 $ell$ 与宿主相容，则
  $ "SigA"(x) <= 4^o x^(1/2 + epsilon). $
]

#lean("UpperTheory.ComparisonâĆĆ.sigA_le", "Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean")

#proof(uses: ref[定义 3.13])[
  `"PsiA" ∖ K_p` 中的每个特征在第一因子上平凡，在 $"iod"$ 上的阶整除 2。于是它是某个保留特征的 $(q, d)$-扭曲，或者就是 $q$、$d$ 扭曲本身，因此落入宿主的有界特征之列（引理 `chr_bounded`）。对条件 `PairGood.bounds`（#ref[定义 3.13]）中的每一个都有 $norm(G) <= y^(1/2 + epsilon\/2)$，无条件成立。它们的个数至多 $abs("PsiA") <= 4^o$。
]

#caution("3.12")[
  在 #ref[定理 3.8] 与 #ref[定理 3.10] 中，界是对加权实部 $"Gm"$ 的，而且是单侧的。它只是上界，并且只对窗口上的 $x$（存在宿主的那些尺度）成立，而非对一切大 $x$。Landau 定理（#ref[定理 2.14]）正是把这种单侧窗口界转化为无零点性的形式。
]

== 辅助素数

宿主需要两个素数 $q$、$d$，带有三条性质。它们必须落在规定的尺寸窗口与同余类中。它们必须使所有小素数在 $QQ(sqrt(-d))$ 中分裂。而经扭曲特征的诸切比雪夫误差必须在 $[Y, Y^K]$ 上很小。

#defn("3.13", "容许对")[
  `WinPair`(ε, Y, q, d) 意为：$q$、$d$ 为素数；$q equiv 3 mod 8$；$d equiv 7 mod 16$；$1\/2 Y^(epsilon\/5) < log q <= Y^(epsilon\/5)$；$1\/2 Y^(epsilon\/5) log^2 Y < log d <= Y^(epsilon\/5) log^2 Y$；$q bar.v d + 1$；且每个 $<= Y^(epsilon\/5)$ 的奇素数都整除 $d + 1$。

  `PairGood`(M, ε, Y, X, q, d) 意为：
  (a) `WinPair`(ε, Y, q, d)。
  (b) $"gcd"(M, q d) = 1$。
  (c)（界）对每个模 $M$ 的特征 $xi$、每个 $(i, j) in {0,1}^2 ∖ {(0,0)}$、以及每个由 $xi$ 经 $lr((dot.op)/q)^i lr((dot.op)/d)^j$ 扭曲（导子整除 $2 M q d$）诱导的特征 $chi$：对一切 $y in [Y, X]$，有 $norm(G_chi(y)) <= y^(1/2 + epsilon\/2)$ 与 $norm(L'\/L (1, chi)) <= 4 log y$。
  (d)（盒）对每个导子整除 $8M$ 的实本原 $rho$，$rho$ 的每个此类扭曲 $chi$ 在高为 $8M exp(Y^(epsilon\/5)) exp(Y^(epsilon\/5) log^2 Y)$、实部 $> 1 - 1\/400$ 的盒内无零点（`ZeroBox`）。
]

#lean("PairGood", "Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean")
#lean("WinPair", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")

#thm("3.14", "对的存在性")[
  `PairEx` 成立：对每个 $M > 0$、$0 < epsilon < 1\/52$ 与 $A >= 1$，存在 $Y_1$，使得对每个 $Y >= Y_1$ 存在 $q$、$d$ 满足 `PairGood`(M, ε, Y, Y^A, q, d)。
]

#lean("PairEx", "Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean")

证明经由以下命题进行，它位于文件夹 `MeanSquareBounds` 中。存在 $C > 0$，使得对所有 $epsilon in (0, 1\/52)$、$tau > 0$、$K >= 1$ 与 $N_0 > 0$，存在 $Y_0$，使得对 $Y >= Y_0$、$X <= Y^K$ 以及窗口 $[Y^(epsilon\/5) log^2 Y, K^2 Y^(epsilon\/5) log^2 Y]$ 中的 $z'$，存在素数 $q > N_0$ 与 $d$，满足 `Rows`$(Y^(epsilon\/5), z', q, d)$（同余与整除条件）、`GoodQ`$(N_0, C, tau, Y, X, dot.op, q)$ 与 `GoodD`$(N_0, C, tau, Y, X, dot.op, z', q, d)$。这里 `GoodQ` 说：由 $xi J_q$（$xi$ 为模 $N_0$ 特征，$J_q$ 为 Jacobi 符号）诱导的所有特征都非平凡、导子 $<= N_0 e^z$、在盒内无零点（`ZeroFreeBox`）、满足 $norm(L'\/L (1)) <= C log Y$，且在 $[Y, X]$ 上 $norm(G_chi(y)) <= y^(1/2 + tau)$。`GoodD` 对 $xi J_q^a J_d$（$a in {0, 1}$）同样。

#lean("pair_exists", "Development/AutomorphicArithmetic/MeanSquareBounds/PairExists.lean")

#proof(uses: ref[定理 3.18 与 3.21，输入定理 7.14，命题 3.22])[
  引理 `pair_share`（`PairShare.lean`）表明：对多数满足 $e^z < q <= e^(z')$（$z = Y^(epsilon\/5)$）的素数 $q equiv 3 mod 8$，性质 `GoodQ` 成立。这里“多数”指：对任意固定的 $eta > 0$，这些素数中至少 $1 - eta$ 的比例。然后，对多数满足 $e^(z') < d$、$d equiv 7 mod 16$、且 $d + 1$ 被 $q$ 乘以直到 $z$ 的奇素数之积整除（即 `oddM`(z, q)）的素数 $d$，`GoodD` 成立。于是任取一个好的 $q$，再任取一个好的 $d$。“多数”在引理 `stage1` 与 `stage` 中通过组合四种原料得到。

  + （`meanSqK`）算术级数中素数上的平方平均界：$sum_q sum_n c_N(y, n) kappa(n) (n/q)^2 <= C y log y abs(P)$。它由 `twistK` 导出：级数中素数 $q$ 上的 Jacobi 符号 $(q\/s)$ 之和，对一切 $<= Y^A$、与模互素的奇 squarefree $s$ 都极小，至多除去一个例外 $s$。该输入是带可能例外零点的算术级数素数定理（`pnt_progressions_relative_weak_holds`）。
  + （`bad_share`）Markov 不等式加上 $[Y, X]$ 的二进分解：使某个 $y in [Y, X]$ 有 $abs(S) > y^(1/2 + tau)\/2$ 的 $q$ 的比例至多是任意固定的 $eta > 0$。
  + （`count_bad`、`count_bad_core`）使得某个导子 $f q <= Q$（$f <= F < q$）的本原特征在盒 $Re s > 1 - 1\/400$、$abs(Im s) <= Q$ 内有零点的素数 $q$ 的个数至多是 $C Q^(1\/4)$。映射 $q arrow.r$（这样一个特征）是单射，因为 $q > F >= f$，故这是 #ref[定理 3.18] 应用于其像。
  + （`count_a`）算术级数中的素数定理（例外零点由 Siegel 定理控制）表明候选素数集非空且具有正下密度。

  坏 $q$ 的计数是 $≪ Q^(1\/4)$，其中 $Q = exp(O(Y^(epsilon\/5)))$，而 $log q approx Y^(epsilon\/5)$ 的素数 $q$ 之个数是 $exp(Y^(epsilon\/5))$ 量级。所以幂次的节省就足够了。
]

#caution("3.15")[
  #ref[定理 3.14] 中的所有常数都是非实效的（它们来自 Siegel 定理）。该命题是对每个大 $Y$ 的存在性命题，而且也只是这样被使用。
]

从素数对到宿主，链条如下。设 $psi$ 本原，`VWinAt`(ψ, 401) 表示伽罗瓦侧的界 `VVle` 对某尺度窗口上的一切 $psi$-域成立。这是 #ref[第 6 章]（#ref[定理 6.4]）的输出。

#thm("3.16", "素数对的窗口")[
  对每个本原 $psi$、$0 < epsilon < 1\/52$ 与 $c >= 1$：若 `VWinAt`(ψ, 401) 与 `PairEx` 成立，则存在 $J >= 1$，使得对每个 $y$ 存在 $Z >= y$，使得对每个 $x in [Z, Z^(3\/2)]$ 存在 $Y$、$q$、$d$、$e$ 构成一个 `WinDatum`。该数据包含：`PairGood`($"cond" psi, epsilon, Y, x, q, d$)、$x^(1\/J) <= Y <= x$、$x^(2 + 8 epsilon) <= c 2^e <= 2 x^(2 + 8 epsilon)$，以及对每个 $psi$-域 $E$ 的 $"VVle"(E, floor(x^400), exp(x^epsilon))$。
]

#lean("UpperTheory.Top.winPairs", "Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean")

#proof[
  步骤按此顺序。
  + `VWinAt` 给出 $J$ 与阈值 $X_0$。
  + 取大的 $X$ 并在尺度 $X^(1\/J)$ 应用 `PairEx`，$M$ 取 $psi$ 的导子。这给出满足 `PairGood` 的 $q$、$d$。
  + 再一次应用 `VWinAt`，现在是对这一对素数。它给出 $W$ 与一个窗口 $[W, W^2]$，使伽罗瓦侧的界 `VAt` 在其上成立。
  + 重标度。选 $k >= 1$ 使 $k^(2 + 8 epsilon) = c$，写 $x = k x'$。于是 $x'$ 的页条件变成 $x$ 的页条件，而 $k^400 <= x'$ 把 401 版对 $x'$ 的界变成 400 版对 $x$ 的界。

  指数 3/2 出现的原因：一旦 $k^3 <= W$ 就有 $(k W)^(3\/2) <= W^2$。
]

#thm("3.17", "宿主供给")[
  对每个本原 $psi$，
  $ "VWinAt"(psi, 401) ==> "HostExW" lr(3\/2, (G_(chi_psi))."req"). $
]

#lean("UpperTheory.Top.supplyChi", "Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean")

#proof(uses: ref[定理 3.16、3.23、3.24 与定义 3.1、3.2])[
  证明是一个封装。引理 `admissibleClassesTwistedChar` 对每个具有正确阶的标架给出满足 `RankVal` 与 `admitted` 的秩数据 $R$。引理 `fieldChi` 用由 $psi$ 与二次幂分圆部分生成的群，为任何满足假设的 $q$、$d$ 构造标架与一个 `HostAx`。`hostOfField`（见下）把后者变成完整的 `Host`。尺度窗口来自 #ref[定理 3.16]。最后 `isChiField` 表明该域是 $psi$-域，故 `VVle` 由 `VWinAt` 得出。
]

命题 `hostOfField` 以 `PairGood`、`PairWin`、`FieldRows` 与 `admitted` 为假设，产生一个真正的 `Host` $R$，满足 `HostGood` 与要求 `Shares`。它使用两个算术输入 `ShortNorm` 与 `SmallOne`，它们在 #ref[第 3.7 节] 中兑现。

#lean("UpperTheory.Top.hostOfField", "Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean")

整族宿主的存在性（使得那些全称量化的设计命题不落空）是另一条链。谓词 `DesignChoices`(C, C₀, c_T) 是存在性的：存在 $epsilon_0 > 0$，使得对每个 $epsilon <= epsilon_0$ 与每个被搬运的数据 $K$，存在满足类 $C$ 的族 `Fm`，连同一条性质清单（厚集、选定的坏集、盒、码界，等等）。它由 `designS` 证明，输入是宿主供给 `HostExW` 以及每个宿主的格对象与自守对象的存在性。

#lean("DesignChoices", "Formalism/SharpRestriction/DesignExistsOfChoices.lean")
#lean("designS", "Development/AutomorphicArithmetic/CharacterBoxes/DesignS.lean")

#inferred[粘合步骤 `exists_famP_of_kits` 与 `kit_of_points` 在各阅读器报告中被描述为“装配”，而非数学。]

== 零密度盒

#thm("3.18", "零密度盒")[
  存在常数 $C$，使得对每个实数 $Q >= 3$ 与每个由数对 $(N, chi)$ 组成的有限集 $S$（$chi$ 为模 $N + 1$ 的狄利克雷特征），若每个 $(N, chi) in S$ 满足
  - $chi$ 本原且 $N + 1 <= Q$，并且
  - 存在 $s in CC$ 使 $Re s > 1 - 1\/400 = 399\/400$、$abs(Im s) <= Q$ 且 $L(chi, s) = 0$，

  则 $abs(S) <= C Q^(1\/4)$。这里 $L(chi, s)$ 是狄利克雷 L 函数的解析延拓（整函数延拓）。
]

#lean("zero_density_box", "Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean")
#lean("ZeroDensityBox", "Formalism/GL3MeanSquares/ZeroDensityBox.lean")

注意：这数的是特征而非零点，而且一次性数所有 $<= Q$ 的模。平凡特征（模 1）是允许的。Lean 陈述就是谓词 `ZeroDensityBox`，它作为定理 `zero_density_box`（一个两行项）被证明。该谓词在另一个命名空间里还有一个语法上完全相同的副本；#inferred[二者定义相等，但这一等同未被核对。]

#caution("3.19")[
  这比 Montgomery 与 Huxley 的经典密度定理弱得多：后者给出 $Q^3$ 的幂次、指数里带一个小倍数的 $1 - sigma$，即在 $sigma = 399\/400$ 处大约 $Q^0.02$ 到 $Q^0.04$。#inferred[（与文献的比较来自阅读者的背景知识，而非来自 Lean 树。）]这种弱是故意的：只需要幂次的节省。
]

#heading(numbering: none, outlined: false)[证明梗概.]
固定大的 $Q$。置 $q_0 = ceil(Q)$、$Y = q_0^4$、$J = 8(floor(log_2 q_0) + 1)$、$N = 2^J$、$s_0 = 399\/400$。

+ 缓和子（`mollifier_identity`）。对 $Y <= N$ 与任意 $chi$、$s$，
  $ lr(sum_(n <= N) chi(n) n^(-s)) lr(sum_(a <= Y) mu(a) chi(a) a^(-s)) = 1 + sum_(Y < n <= Y N) "mco"(n) chi(n) n^(-s), $
  其中 $"mco"(n) = sum_(a b = n, a <= Y, b <= N) mu(a)$。这是纯有限代数：$"mco"(1) = 1$，且对 $2 <= n <= Y$ 有 $"mco"(n) = 0$，因为 $sum_(d bar.v n) mu(d) = 0$。又 $abs("mco"(n)) <= d(n)$，故由除数界得 $sum_(U < n <= 2U) lr(abs("mco"(n)) n^(-s_0))^2 <= C U^(-197\/200)$（`coefficient_square_bound`）。
+ 零点检测（`zero_detection`）。设 $rho$ 是 $L(chi, dot.op)$ 的零点，$Re rho > s_0$、$abs(Im rho) <= Q$。由部分求和与非主特征的平凡界 $sum abs(chi(n)) <= q + 1$，部分和 $P = sum_(n <= N) chi(n) n^(-rho)$ 满足 $norm(P) <= 2(q + 1)(1 + abs(rho)\/Re rho) N^(-Re rho)$，故 $norm(P) <= 1\/2$。缓和子之和的范数至多是 $Y$。由于 $P dot.op "Mo" = 1 + D$ 且 $norm(P dot.op "Mo") <= 1\/2$，尾部 $D$ 满足 $norm(D) >= 1\/2$。把 $D$ 切成 $J$ 个二进块，则有一个块满足 $sum_(Y 2^j < n <= Y 2^(j+1)) "mco"(n) chi(n) n^(-rho) >= 1\/(2J)$。
+ 对偶性（`duality_inequality`）。对向量 $v_i$ 与系数 $b_n$：若 Gram 矩阵 $sum_j sum_n v_i(n) overline(v_j(n))$ 的每个行和至多是 $Delta$，则 $sum_n b_n v_i(n)$ 的平方和 $<= Delta sum_n abs(b_n)^2$。这就是用 Cauchy–Schwarz 写出的 Schur 检验。
+ 不用大筛的 Gram 界（`pair_twist_bound`）。对两个不同的本原 $chi$、$chi'$，乘积 $chi overline(chi')$ 是模 $q q'$ 的非主特征，故其部分和至多是 $q q'$。部分求和给出：对 $Re w > 0$，$sum_(U < n <= 2U) chi overline(chi')(n) n^(-w) <= 2 q q' (1 + abs(w))$。Gram 矩阵的非对角元至多是 $8 Q^3$。
+ 块计数（`blockCount`）。取 $b_n = "mco"(n) n^(-s_0)$ 与 $v_chi(n) = chi(n) n^(-(rho_chi - s_0))$。对角元至多是 $U$，非对角元至多 $8 Q^3$。对偶性给出：所选块长度为 $U$ 的特征个数至多是 $8 J^2 C U^(3\/200)$，只要 $8 Q^3 C U^(-197\/200) <= 1\/(8 J^2)$。
+ 装配（`final_bound_of_assembly`、`numeric_constants`）。对 $J$ 条纤维求和，用 $U <= Y N <= 2^20 Q^12$。于是 $J^3 (2^20 Q^12)^(3\/200) ≪ Q^(7\/100 + 9\/50) = Q^(1\/4)$。$Re rho >= 1$ 的零点由 $L$ 在 $Re s >= 1$ 上的非零性（Mathlib）排除。小的 $Q$ 与平凡特征被吸收进 $C$。

#rem("3.20", "未使用 RH")[
  本章的任何地方都不假设 RH、GRH，也不假设超出经典范围的无零点区域。#ref[定理 3.18] 的证明只用：$L$ 的解析延拓（Mathlib）、除数界、平凡部分和界、以及 $Re s >= 1$ 上的非零性。它对 $Re s < 1$ 的零点完全没有使用任何信息。其余解析输入都是经典且无条件的：带至多一个例外实零点的 de la Vallée-Poussin 无零点区域、Deuring–Heilbronn 排斥，以及对单个模的无对数零密度估计。这里的逻辑不是循环的：零密度只用来选取 $q$、$d$；这给出正素数和的一个界；这给出切比雪夫误差的一个单侧界；然后 Landau 论证给出无零点性。对文件夹 `MeanSquareBounds`、`ShortNorms`、`GL3MeanSquares` 与 `LandauZeroFreeBounds` 的扫描没有发现名为 RH 或 GRH 的假设，也没有发现 `sorry`。
]

== 经典输入

以下各条在库中作为已证的定理陈述。它们的常数都是非实效的或存在性的。

#thm("3.21", "Siegel")[
  对每个 $epsilon > 0$ 存在 $c > 0$，使得对每个模 $q$ 的实非平凡特征 $chi$ 有 $L(1, chi) >= c q^(-epsilon)$。由此，对每个模 $q$ 的实非平凡特征 $chi$ 与 $L(s, chi)$ 的每个实零点 $beta$，有 $beta <= 1 - c q^(-epsilon)$（`ExcBound`，由 `SiegelLower` 经 `excBound_of_siegelLower` 得到）。
]

#lean("siegelLower", "Formalism/LandauZeroFreeBounds/FinalSiegel.lean")

这与经典陈述相符。它由 `siegel_theorem_of` 证明，输入是乘积特征的存在性与 $L(1, dot.op)$ 的一个上界。基础一章把它列为输入定理 7.14。[用到 #ref[输入定理 7.14]]

#prop("3.22", "无零点区域、Deuring–Heilbronn、无对数密度")[
  以下三个经典事实在库中被无假设（RH 型）地证明。
  + 对 $M >= 3$ 与小的 $c_1 > 0$，至多存在一个数对 $(chi, beta)$：$chi^2 = 1$，$beta$ 是相应本原特征的实零点，且 $1 - c_1\/log M < beta < 1$（例外对；`IsExc`）。它满足 $chi eq.not 1$ 与 $1 - beta >= c\/(M^2 log M)$。模 $M$ 的特征的每个其余零点 $rho$（$Re rho < 1$）满足 $Re rho <= 1 - c \/ log(M(abs(Im rho) + 2))$（常数 $c$ 依赖于 $c_1$）。
  + （Deuring–Heilbronn）例外零点对 1 附近其余零点的排斥。
  + （无对数密度，Linnik 型）$sum_(chi mod q) N(sigma, T, chi) <= C (q T)^A (1 - sigma)^(A(1 - sigma)) quad (1 - eta <= sigma <= 1)$。
]

#lean("GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion", "Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegionStatement.lean")

#inferred[第 (1) 条的文件路径来自阅读器报告；(2)、(3) 只作为陈述被读过。它们的证明（(3) 用 Turan 幂和方法）未被核对。]

合起来，它们给出带相对误差与一个例外零点修正项的算术级数素数定理（`primesRel_holds`）。

#thm("3.23", "级数中的小素数（Linnik）")[
  存在 $A >= 1$，使得对每个 $M >= 2$ 存在素数 $p equiv 1 mod M$ 满足 $p <= M^A$。
]

#lean("UpperTheory.T3.smallOne", "Development/AutomorphicArithmetic/ShortNorms/Primes.lean")

#proof(uses: ref[命题 3.22])[
  这是对带相对误差的算术级数素数定理应用 `smallOne_of`。对 $M >= 3$ 取 $X = M^2 N$ 使相对误差低于 $1\/200$。于是计数为正。$M = 2$ 的情形是 $p = 3$。
]

#thm("3.24", "短范数素数")[
  存在 $A, c, c' > 0$，使得对每个满足 $d equiv 3 mod 4$、$d >= 100$ 的素数 $d$、每个 $M >= 3$、$X >= 1$ 与 $h$（满足 $log(4 d M^2) <= c log X$ 与 $e^(-c log X) <= h <= 1$），形如 $4 p = alpha^2 + d beta^2$（其中 $M bar.v beta$、$2 M bar.v alpha - 2 - beta$）的素数 $p in (X, X(1 + h)]$ 的个数至少是
  $ (c' h X)/((4 d M^2)^A log X). $
]

#lean("UpperTheory.T3.shortNorm", "Development/AutomorphicArithmetic/ShortNorms/Primes.lean")
#lean("ShortNorm", "Development/AutomorphicArithmetic/ShortNorms/ShortNorm.lean")

用文字说：这些是给定 $QQ(sqrt(-d))$ 的某个射线类中、落在短区间内的元素的范数素数。这是（虚二次域上的）Hecke 特征版的短区间素数定理。证明是标准的显式公式路线，误差为 de la Vallée-Poussin 型的 $e^(-c sqrt(log X))$ #inferred[（无零点输入是经典的；证明只读了前 30 行）]。这些素数正是用来在 `hostOfField` 的构造中造出满足 $pi overline(pi) = g_i$ 的 Hecke 素数 $pi$ 的那些。

== 总结与传递

本章证明了什么。

- 一个精确恒等式（#ref[定理 3.6]）：把宿主上的正素数和 $"ASK"$、显式主项 $"MAIN"$ 与光滑化切比雪夫误差的 Fourier 平均联系起来。
- 核心估计（#ref[定理 3.8]、#ref[定理 3.10]）：上界 $"ASK" - "MAIN" <= x^(C epsilon) "Err"$ 给出 $"Gm"(x) <= x^(1/2 + (e_D + e_L + 7) epsilon)$，相差一个余项 $"SigA" <= 4^o x^(1/2 + epsilon)$（#ref[命题 3.11]）。
- 具有所需性质的辅助素数 $q$、$d$ 的存在性（#ref[定理 3.14]），经由零密度盒（#ref[定理 3.18]）、Siegel 与平方平均；以及宿主自身的存在性，来自伽罗瓦输入 `VWinAt`（#ref[定理 3.17]）。

本章需要什么。

- 来自#ref[第 5 章]：上界 $"ASK" - "MAIN" <= x^(C_E epsilon) "Err"$，即 #ref[定理 5.27]，经由 `ch_top` 以 (3.1) 进入。这是格几何进入素数和的唯一入口。
- 来自#ref[第 6 章]：对一切 $psi$-域的 Tate–Shafarevich 型和的界 `VWinAt`(ψ, 401)（#ref[定理 6.4]）。
- 来自#ref[第 7 章]：Siegel 定理（输入定理 7.14）。

本章传递什么。在存在宿主的尺度上，窗口化单侧界 $"Gm"(x) <= x^(1/2 + O(epsilon))$ 被传递给主干章（#ref[第 2 节]）。在那里，Landau 论证（#ref[定理 2.14]）把它变成 $L(s, chi)$ 对 $Re s > 1/2 + O(epsilon)$ 的无零点性。令 $epsilon arrow.r 0$ 并对全体本原 $chi$ 应用该结果，便得 #ref[定理 2.8]，进而得 #ref[定理 2.1]。
