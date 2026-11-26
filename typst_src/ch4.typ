// ch4.typ —— 第 4 章 theta 塔
#import "lib.typ": *
#pagebreak(weak: true)

= theta 塔

本章描述 Lean 证明中替代 Stepanov 方法所缺失的“重数”的那一部分。在整数上，不存在具有高消失阶的辅助多项式。证明用一个替代品来填补：在一个 CM 域上的酉群之间做 $m$ 次迭代的 theta 提升，其中 $m approx sqrt(x)$。每次提升给出一个余体积受控的厄米格。对 $m$ 次提升求和给出素数和的上界，而 $m$ 与和的长度 $x$ 之间的平衡给出误差项 $x^(1/2 + O(epsilon))$。

我们陈述四件事。第一，塔本身及其数值约束（#ref[第 4.1 节] 与 #ref[第 4.2 节]）。第二，使余体积估计得以成立的逐提升假设（#ref[第 4.3 节]）。第三，theta 积分：Rallis 内积、Siegel–Weil、Eisenstein 延拓，以及局部与整体常数的匹配（#ref[第 4.4 节]）。第四，稳定范围内定 $U(n) times U(d)$ 的 theta 提升，含其非零性、自守性与局部 Satake 公式（#ref[第 4.5 节]）。

全文中，#inferred[……] 标记阅读者由命名与结构推断、而非逐行读出的材料。路径相对于 Lean 源码根目录。

== 塔

#defn("4.1", "秩数据")[
  秩数据是由自然数组成的四元组 $("ord", k, m, t)$（连同全实域的一个标架数据），其中 $k$、$m$ 为偶数，$t$ 为奇数，并满足下列不等式：
  $ 2 <= m, quad m + 3 <= k, quad m <= 2 "ord" <= k, quad k + m - 1 + 5 <= t, quad 3m < t, quad m^2 <= k + m(t + 1). $
  置 $n = "ord"$（全实域 $F$ 的次数）、$f = 2n$（CM 域 $E$ 的次数），并置
  $ r = k + m - 1, quad quad N(j) = k + j(t + 1), quad quad "rank"_Y (j) = r + j t, quad quad sigma_W (j) = (k + j - 1, m - j). $
]

#lean("Formalism.BasicNotions.Ranks", "Formalism/LocalRingCardinality/Params.lean")

注意 $r$ 是奇数，因为 $k + m$ 是偶数。对 $1 <= j <= m$，数对 $sigma_W(j)$ 加起来是 $r$。它是 $r$ 维厄米空间 $W_j$ 的符号差。对 $j = m$ 我们得到 $sigma_W(m) = (r, 0)$，故最后一个空间是定的。Lean 文件证明了 $N(j + 1) = N(j) + (t + 1)$（“`FactNStep`”）以及 $"rank"_Y(m) = r + m t$。该文件还证明了另外两个事实：$N(j)$ 是偶数（`FactNEven`），以及 $N(m) = "rank"_(X') + 1$（`FactXm`）。#inferred[第 $j$ 步的群对是 $(U(W_j), U(Y_j))$，其中 $"rank" Y_j = "rank"_Y (j)$；代码给出的是秩与符号差，群层面的配对是从命名读出的。]

#defn("4.2", "塔数据")[
  设 $R$ 是一个秩数据。$R$ 上的一个塔数据（tower datum）$D$ 由以下组成。

  + 一个域 $L$，连同嵌入 $L arrow.r.hook CC$、一个环 $cal(O) arrow.r L$，以及 $L$ 的一族位与共轭 $w arrow.r bar(w)$。
  + 有限维 Hilbert 空间 `EE`（基空间），以及：对每个元组 $mu$ 与每个 $j in {0, dot.op, m}$，一个重数空间 $"Mult"(mu, j)$。
  + 等距同构 $"Mult"(mu, 0) tilde.op "EE"$ 与 $"Mult"(mu, m) tilde.op "Amb"(mu)$，其中 $"Amb"(mu)$ 是顶空间，其上有一个 $cal(O)$-格 $tilde(M)(mu)$。
  + 线性映射 $"io"_(mu, j) : "Mult"(mu, j + 1) arrow.r "Mult"(mu, j)$。
  + 对 $1 <= j <= m$：一个带格 $M_j^"lat"$ 的 Hilbert 空间 $M_j$，一个映射 $theta_P : tilde(M)_(mu, j) arrow.r M_j$，一个同型分解 $M_j = ⊕_pi "isot"_j (pi)$，标量 $lambda_P (mu, j, pi) >= 0$，以及在哪个嵌入处的 Harish-Chandra 数据 $kappa_j^"big" in ZZ^(k + j - 1)$、$kappa_j^"small" in ZZ^(m - j)$。
  + 整数 $I_j (mu, w)$、$j_w (mu, j)$（提升 $j$ 在位 $w$ 处的局部指标）与非负有理数 $"shaLen"(l, e)$（Selmer 型群的长度）。

  定义 $iota_mu : "Amb"(mu) arrow.r "EE"$ 为全部 $m$ 个映射 $"io"$（连同两个等距）的复合，并置
  $ theta_mu^arrow.t := iota_mu^ast : "EE" arrow.r "Amb"(mu). $

  令 $V_0 = "range"(e_mu)$（$e_mu$ 为某个自伴幂等元），$U_"sp" = V_0 ∩ "ker" iota_mu$，$Q_"sp" = V_0 ∩ U_"sp"^perp$，以及
  $ Lambda_mu = {"pr"_(Q_"sp") (x) : x in tilde(M)(mu) ∩ V_0}, quad quad "RR"_mu = iota_mu(Lambda_mu) subset "EE". $
]

#lean("Formalism.BasicNotions.Rows.Data", "Formalism/LocalRingCardinality/DataRows.lean")
#lean("Formalism.BasicNotions.Rows.Data.thetaUp", "Formalism/LocalRingCardinality/DataRows.lean")

集合 $"RR"_mu$ 是 `EE` 中的格，后续各章对它的余体积给出界。映射 $theta_mu^arrow.t$ 是沿塔上行的 $m$-重 theta 提升。Lean 字段 `LamPDef` 说 $theta_P theta_P^ast$ 在 $"isot"_j (pi)$ 上的作用是标量 $lambda_P (mu, j, pi)$。#inferred[这些标量是提升的 Rallis 型特征值；代码只把它们记录为一个抽象字段。]提升 $j$ 在 $w$ 处的局部指标是 $A_j (w) = I_j (mu_w, w) + I_j (mu_w, bar(w)) + j_w (mu_w, j)$，且 $"VV"(l) = sum_(e = 1)^(t - 1) "shaLen"(l, e)$。

#caution("4.3")[
  结构 `Data` 是一捆抽象假设，不是构造。theta 提升并未在其中定义。它与真实酉群的联系由 #ref[第 4.3 节] 的逐提升条件以及 #ref[第 4.5 节] 的对象完成。有几个 Lean 命名被重复使用：有两个 `Ranks`（这一个，以及 `Formalism/PeriodIntegrals/TwistedEisensteinNonvanishing.lean` 中一个字段相同的副本），还有两个 `thetaUp`，分别在 `Formalism/LocalRingCardinality/DataRows.lean` 与 `PrincipalHermitianLattice.lean` 中。
]

== 尺寸约束与指数平衡

常数绑定于一个尺度数据：参数 $x >= 3$ 与一个小量 $epsilon$。我们写 $b = exp(x^epsilon)$ 为提升权的尺寸，$a = x b$ 为素数和的长度，$delta_1 = x^(-epsilon\/8)$。（这些是报告读到的字段 `Scale.b`、`Scale.x`、`Scale.delta1`。）

#defn("4.4", "RankVal")[
  称秩数据 $R$ 在尺度 $(x, epsilon)$ 处具有容许尺寸，若
  $ x^(2 + 8 epsilon) <= n <= 2 x^(2 + 8 epsilon), quad quad quad sqrt(x delta_1) <= m <= 2 sqrt(x delta_1), $
  $ x^(9\/2 + 10 epsilon) <= k <= 2 x^(9\/2 + 10 epsilon), quad quad quad r + t = 8 f sqrt(r) + 4 + "TO" dot.op n_W. $
  这里 $"TO"$ 与 $n_W$ 是两个显式的辅助参数（`TOv`、`nWv`）。
]

#lean("Formalism.BasicNotions.RankVal", "Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean")

于是 $m approx x^(1/2 - epsilon\/16)$，$k approx x^(9\/2 + 10 epsilon)$。这里 $"TO" = ceil(x^377)$（`TOv`）。Lean 定义 `nWv` 为 $8 ceil(10 r (f + f^2 (k - 1)^3 L^2 \/ m) \/ 8)$，其尺寸约为 $x^(21.5 + O(epsilon))$（相差尺度数据带来的因子 $L^2$）。所以 $r + t <= x^400$，特别地 $t <= x^400$。$t$ 的尺寸是无害的：$x$ 的一切多项式因子都被 $b = exp(x^epsilon)$ 吸收。

#rem("4.5", none)[
  项 $8 f sqrt(r) + 4$ 只是 $t$ 的一小部分。$t$ 的大部分是 $"TO" dot.op n_W$。
]

平衡并不是直接从 `RankVal` 证明的。Lean 把数值内容抽象成一个单独的谓词。

#defn("4.6", "SizeWindows")[
  对实数 $C, epsilon, x, b, k, a_E, "Err"$ 与自然数 $n, n_T, n_(T_2), m$：谓词 `SizeWindows` 成立，若 $3 <= x$、$0 < epsilon$、$0 <= C$、$0 < n$、$0 < b$、$0 <= a_E <= 2 x b$，且
  $ x^(-epsilon\/8) n\/2 <= n_T, quad x^(-epsilon) <= n_(T_2)\/n, quad n_(T_2) <= n, $
  $ x^(1/2 - epsilon) <= m <= x^(1/2 + epsilon\/2), quad x m <= k <= n^2 x^(1/2 - epsilon), quad 2^6 <= x^(3 epsilon\/8), $
  $ "Err" <= x^(C epsilon) lr(n_T a_E lr(1 + m^2/k) + m lr(2 n m b x^epsilon + (n_(T_2) k b x^epsilon)/(n(n x^(-epsilon))))). $
]

#lean("Formalism.SizeWindowBrackets.SizeWindows", "Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean")

在 `SizeWindows` 中，$n$ 是宿主群的阶 $abs(H)$（`Fintype.card H`），而不是 #ref[定义 4.1] 的域次数 $"ord"$。由 `PageN`（$2^e tilde.op x^(2 + 8 epsilon)$）与 `RankVal`，它与 $"ord"$ 落在同一个窗口里。

#prop("4.7", "指数平衡")[
  设 $C, epsilon, x, b, k, a_E, "Err", G$ 为实数，$n, n_T, n_(T_2), m$ 为自然数，且 `SizeWindows` 成立。假设
  $ (n_(T_2)\/n)/2 G - 4 x^(1/2 + epsilon) <= "Err" + (2 n_T m b)/x. $
  则 $G <= x^(1/2 + (C + 3) epsilon)$。
]

#lean("Formalism.SizeWindowBrackets.GrowthSizeBound", "Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean")
#lean("Formalism.LFunctionChainParameters.ThickSetMeanBounds.proposition_size_bound", "Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean")

#proof[
  置 $P = n_T m b n_(T_2) \/ (2 n)$。则 $G <= 4 x^(1/2 + epsilon) + ("Err" + 2 n_T m b\/x)\/P$。把误差括号的三部分除以 $P$，并用各窗口逐项估计。下面的链条是阅读者自己的代数，已逐行对照各窗口核对；Lean 的证明用四个引理 `SZ.T1` 到 `SZ.T4` 完成。
  + 项 $n_T a_E (1 + m^2\/k)$ 至多给出 $4 x^(1 + epsilon) (1 + m^2\/k)\/m$。由 $m <= x^(1/2 + epsilon\/2)$ 与 $k >= x m$，得 $m^2\/k <= m\/x <= x^(-1/2 + epsilon\/2) <= 1$。于是这一项至多贡献 $8 x^(1/2 + 2 epsilon)$（除以 $m$ 时用了 $m >= x^(1/2 - epsilon)$）。
  + 项 $2 n m^2 b x^epsilon$ 至多给出 $8 m x^(epsilon + epsilon\/8 + epsilon)$。用 $m <= x^(1/2 + epsilon\/2)$，它至多是 $8 x^(1/2 + 21 epsilon\/8)$。
  + 项 $m n_(T_2)^2 k b x^(2 epsilon)\/n^2$ 至多给出 $4 (k\/n^2) x^(17 epsilon\/8)$。用 $k <= n^2 x^(1/2 - epsilon)$，它至多是 $4 x^(1/2 + 9 epsilon\/8)$。
  + 项 $2 n_T m b\/x$ 给出 $4 x^(epsilon - 1)$，可以忽略。

  四项的数值常数相加为 $8 + 8 + 4 = 20$，假设中单独的项 $4 x^(1/2 + epsilon)$ 再加 4，第 4 项可忽略。所以总和低于 $2^6$。假设 $2^6 <= x^(3 epsilon\/8)$ 把它变成一个因子 $x^(3 epsilon\/8)$。由于 $21\/8 + 3\/8 = 3$，我们得到 $G <= x^(1/2 + (C + 3) epsilon)$。
]

第一项像 $x\/m$ 那样递减，第二项像 $m$ 那样递增。它们在 $m = sqrt(x)$ 处相遇，这正是 $m$ 的窗口以 $sqrt(x)$ 为中心的原因。$k$ 的窗口两端使 $m^2\/k$ 保持小、并使第三项保持 $x^(1/2)$ 的量级。#inferred[“$m tilde.op sqrt(x)$ 是 $x\/m + m$ 的最优值”这一读法是阅读者对窗口的解释；Lean 文本只规定了窗口。]代码从不在概念上论证 $m approx sqrt(x)$；它只施加该约束。

#cor("4.8", "GrowthBoundGivesRiemannHypothesis")[
  设 `GrowthInequalityDataExists`(C, ε, x) 是如下命题：存在有限交换群 $H$、算术数据、一个带权 $w_(u^0, j)$ 的 $m$ 重提升窗口、参数 $b, b', eta, X', theta, C_d, C_L, "Err", k, a_E$、宿主事实、增长不等式、小代价条件，以及 `SizeWindows`(C, ε, x, |H|, |TT|, |T₂|, m, …)。假设存在一个与 $epsilon$ 无关地固定的 $C$ 与 $epsilon_1 > 0$，使得对一切 $0 < epsilon < epsilon_1$ 它对一切大 $x$ 成立（Lean 中为 $forall C epsilon_1$）。则黎曼猜想成立。更精确地说，在该情形下，对主干章的素数和量 $G_z(x)$ 有 $G_z(x) <= x^(1/2 + (C + 3) epsilon)$。这条路线只给出 $zeta$ 的 RH（经由 $G_z$）。`Main.lean` 把 `riemannHypothesis` 证明为 `rhOfAll`，即 #ref[第 2 节] 经由 `ch_core` 与 `core_gm`（#ref[第 3 节]）的全体特征路线。本推论是通往同一终点的第二条、只含 $zeta$ 的路线。#inferred[我们未核查它是否在主路径上被使用。]
]

#lean("Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis", "Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean")
#lean("Formalism.LFunctionChainParameters.ThickSetMeanBounds.proposition_final", "Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean")

证明是逐点界 `proposition_at_point`（把 #ref[命题 4.7] 应用于增长不等式）与主干章的 Landau 窗口论证的复合。[用到 #ref[命题 4.7 与定理 2.14]] `GrowthInequalityDataExists` 的完整定义很长；我们只读了它的形状。

== 逐提升条件

每个格 $M_i$ 的余体积被逐提升地控制住，关于 $i$ 一致。族条件是一个对所有大参数的全称命题。

#defn("4.9", "LiftsCondition")[
  设 $Q(p, i, "PP", C)$ 是族上关于点 $p$ 的性质，$i in {0, dot.op, m - 1}$ 是一个提升指标，$"PP"$、$C$ 为实数。命题 `LiftsCondition`(Q) 说：对一切小 $epsilon$，存在 $epsilon_1$-一致的数据，使得对某个常数 $C >= 0$，最终在每个容许族的所有点 $p$ 上，$Q(p, i, "PP", C)$ 对每个 $i < m$ 成立。命题 `CoversCondition`(Q) 相同，但把指标限制在 $i + 1 < m$，并要求对志村簇的每个好覆盖 $Y$ 成立。
]

#lean("GlobalTheory.CovTop.LiftsCondition", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LiftLambdaBound.lean")

固定一个提升 $i$（于是提升编号为 $j = i + 1$）。存在一个由提升形式构成的、带 Petersson 型范数 `nrm` 的格 $Lambda_"all"$。其内部坐着一个好子格 $Lambda_"good"$、一个型子格 $Lambda_"type"$ 与一个小的坏部分 $Lambda_"bad"$。记 $mu$ 为该范数下的斜率（每秩的度）、$mu_max$ 为最大斜率、$u$ 为误差的单位 `unitE`、$T_i$ 为主项 `mainT`。尺度给出 $b <= u <= x^A b$。

#defn("4.10", "逐提升条件")[
  以下是 `LiftsCondition` 打包的条件。
  `GramAt`：范数是厄米的（有 Gram 矩阵），$Lambda_"all"$ 有限生成，$Lambda_"good" eq.not 0$，且权在定群上是好的。
  `RecAt`：$"lcv"(M_i)\/D <= -mu(Lambda_"good")$。每秩余体积至多是好提升形式斜率的相反数。
  `CutAt`：好部分由一个自伴幂等元 $e$ 切出：$e$ 关于该范数正交、把 $Lambda_"type"$ 保持到因子 $abs(G_p)$ 以内，且 $2 log abs(G_p) <= b$。
  `BadAt`：$"rk" Lambda_"bad" <= 3 e^(-x^(e_z\/7)) "rk" Lambda_"type"$。
  `LamAt`(A)：$mu_max (Lambda_"all") <= x^A b$。
  `SizeAt`(PP, A)：$1 <= b <= u <= x^A b$；$abs(T_i) <= x^A b$；$abs(T_i) <= "PP" dot.op kappa_i$；$b <= "PP" kappa_i$；且若 $i + 1 < m$，计数数落在范围内（$3 dim "Flag" + 5 <= "lenT"$ 且两个比值 $< 1$）。
  `MeasAt`(C)：对每个嵌入 $sigma$ 存在 $c > 0$，$abs(log c) <= C u$，使得对每个具有正确权的尖点形式 $f$ 有 `nrm`(lift of f) $= c dot.op "Pet"(f)$。
  `RatAt`：$Lambda_"type"$ 由落在型子空间中的格向量张成。
  `CoreAt`(C)：$mu_"core" - C u <= mu(Lambda_"type")$。
  `LowAt`(C)：$-T_i - C u <= mu_"core"$。
  `AnchorAt`(C)：$T_i$ 与 $(p - q) dot.op "anchor" dot.op log Omega_"CM"$ 在各嵌入上的某个显式和相差不超过 $C u$；且 $f^r n_V L <= b$。
]

对满足 $i + 1 < m$ 的覆盖 $Y$，还有 `RingAt`（$mu(Lambda_"deep") - 2 b <= mu_"core"$）、`MapsAt`（一族 $n$ 个联合单射的映射，范数平方至多 $e^(2b)$，从权 $-c$ 的形式映入工作权的形式，且 $n "rk" Lambda_"deep" <=$ 目标的秩）、秩、次数与平坦性的簿记条件，以及算术 Hilbert–Samuel 下界（`ShareAt`、`HeightAt`、`HSAt`）。

对 $i + 1 = m$（定的一步），只要求 `LowAt`，即 `LowDefectCondition`。

#lean("GlobalTheory.CovTop.GramAt", "Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean")

`LamAt` 与 `SizeAt` 在使用时可以带不同的指数 $A$ 与 $B$（见 #ref[命题 4.11]）。Lean 名称是上文文件中的 `GramAt`、`RecAt`、`CutAt`、`BadAt`、`LamAt`、`SizeAt`、`MeasAt`、`RatAt`、`CoreAt`、`LowAt`、`AnchorAt`、`RingAt`、`MapsAt`。Hilbert–Samuel 计数用 $"lenT" = ceil("PP"^2 dim "Flag"^2 k\/m)$，于是权预算 $k$ 在 $m$ 个提升之间分摊。#inferred[`MeasAt` 是被当作范数比较使用的 Rallis 内积，`AnchorAt` 用 CM 周期固定主项。代码只陈述不等式。]

#prop("4.11", "单个提升的余体积")[
  假设 $x > 0$、$0 <= C_1$、$0 <= C_2$，且
  $ 12 e^(-x^(e_z\/7)) lr(x^A + x^B + C_1 + C_2 + 1) <= 1, $
  并假设对提升 $i$ 有 `GramAt`、`RecAt`、`CutAt`、`BadAt`、`LamAt`(A)、`SizeAt`(PP, B)、`CoreAt`(C₁) 与 `LowAt`(C₂)。则
  $ ("lcv"(M_i))/(D) <= T_i + (C_1 + C_2 + 1) u, $
  其中 $D$ 是 $M_i$ 的秩。尺寸条件对一切大 $x$ 成立（引理 `exists_loss_le`），这就是为什么后文的使用都带“最终”二字。
]

#lean("lcv_le", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean")

#proof[
  证明是四个不等式的链条。
  + `RecAt`：$"lcv"(M_i)\/D <= -mu(Lambda_"good")$。
  + 引理 `slope_good_ge`，使用 `CutAt`、`BadAt`、`LamAt` 与 `SizeAt`：$mu(Lambda_"good") >= mu(Lambda_"type") - 12 e^(-x^(e_z\/7)) (x^A + x^B + C_1 + C_2 + 1) u$。损失极小，因为坏的秩占比是指数级小的。
  + `CoreAt`：$mu(Lambda_"type") >= mu_"core" - C_1 u$。
  + `LowAt`：$mu_"core" >= -T_i - C_2 u$。

  因子 $12 e^(-x^(e_z\/7)) (dots.h.c)$ 由尺寸条件至多为 1，故损失至多是 $u$。
]

定理 `CovolumeBoundOfX` 为全部提升装配这条链，其输入是覆盖估计（`topCovolG_alt_alt`）。在这个定理内部，损失不沿塔累加。对 $j$ 的求和发生在稍后的素数和不等式中：除子条件 `Count` 给出 $log T approx m log b = m x^epsilon$（每个提升把整除因子 $T$ 大约乘上 $b$），而最终的界形如 $u_"mean" "ASK" <= u_"mean" "Main" + "ErrX"$（域 `MeanBoundSecondForm`）。#inferred[误差有一个不带因子 $m$ 的部分 $n_T a L_a$，以及一个关于 $m$ 线性的部分；除以 $m$ 正是 #ref[命题 4.7] 的增益所在。] #used[#ref[命题 4.7]]

== theta 积分

逐提升条件是关于格的不等式。它们与酉群的联系经由 theta 积分。这些命题是在树中被证明的，而非假设。

#env("输入定理", "4.12", "倍增法输入")[
  以下命题在库的其他地方被证明，并在此处使用。
  - `ResidueKilled.DM`：倍增法（来自尖点形式的快速衰减与 Siegel Eisenstein 延拓）。
  - `SiegelWeilUnitaryConvergent` 与 `WeilThetaConvergence`：酉 Siegel–Weil 积分与 Weil theta 核的收敛性。
]

#thm("4.13", "Rallis 内积")[
  设 $A$、$B$ 是 CM 数据上的厄米空间，$"rk" A < "rk" B <= 2 "rk" A$，且 Witt 指标 $w(B)$ 满足 $w(B) = 0$ 或 $"rk" A + w(B) < "rk" B$。设 $U$ 是 $U(A)$ 的不可约尖点子表示，其所有低阶 theta 提升为零。对 $(A, B)$ 上的 Weil 数据、测试向量 $Phi_1, Phi_2$ 与形式 $f_1, f_2 in U$：theta 提升 $theta(Phi_i, f_i)$ 收敛，在 $U(B)$ 上平方可积，且
  $ 1/"vol" lr(theta(Phi_1, f_1), theta(Phi_2, f_2))_"Pet" $
  等于 $(f_1, f_2)$ 的一个倍增 zeta 积分，作用于在点 $s_0 = s_0 (A, B)$ 处取值的 Siegel Eisenstein 级数的截面。
]

#lean("GlobalTheory.Published.RallisInnerProductConvergent", "Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/LowerLiftsZeroOfWittIdxEqZero.lean")
#lean("UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm", "Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean")

#proof(uses: ref[输入定理 4.12])[
  Lean 定理 `rallis_of_dm` 是一个蕴涵
  $ "ResidueKilled.DM" arrow.r "SiegelWeilUnitaryConvergent" arrow.r "WeilThetaConvergence" arrow.r "RallisInnerProductConvergent". $
  它是一个约六十行的证明。它使用酉 Weil 表示、形式 $f_i$ 的尖点快速衰减，以及 Schwartz 型截面在正确的退化主级数中的成员资格。从倍增法中它提取出提升的收敛性以及在 $s_0$ 处的 zeta 恒等式。
]

#caution("4.14")[
  该命题并没有说这个 zeta 值非零。它只是把提升的 Petersson 范数等同于一个倍增 zeta 值，仅此而已。#ref[定理 4.24] 的非零论证从不提取这个值。
]

#thm("4.15", "Siegel–Weil，定侧")[
  设 $A$ 是维数 $m >= 1$、符号差 $(r, s)$ 的厄米（相应地，斜厄米）空间，$Y$ 是维数 $n >= 1$ 的斜厄米（相应地，厄米）空间，且 $min(r, s) = 0$。设 $chi$ 是具有正确类型的 Hecke 特征，$Phi$ 是一个平移张成有限维空间的 Schwartz 函数。设 $D$ 是 $U(A)(F) backslash U(A)(bb(A))$ 对 Haar 测度 $mu$ 的基本域。则由 $Phi$ 构造的 Siegel Eisenstein 级数在 $s = (m - n)\/2$ 处的正则化值为
  $ c dot.op 1/(mu(D)) integral_D sum_x omega(g) Phi(x) dif mu(g), quad quad c = cases(1\, n < m, 2\, n >= m). $
]

#lean("GlobalTheory.ThK.Dbl.SiegelWeilStd", "Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesS.lean")
#lean("PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd", "Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilStandard/SiegelWeilStd.lean")

Lean 陈述是
$ "EisValueAt" lr("flat section", (m - n)\/2) (x) = c dot.op mu(D)^(-1) integral_D "thetaSum"(omega(x) ("Sg" Phi)) dif mu. $

值 `EisValueAt` 是在可能极点处的有限阶 Laurent 值；它之所以有意义，是因为下文的 #ref[定理 4.17]。

#caution("4.16")[
  这里只覆盖 $A$ 为定的情形（$min(r, s) = 0$），$c in {1, 2}$。它不是 Kudla–Rallis 对不定空间的完整正则化 Siegel–Weil 公式。
]

#proof(uses: ref[定理 4.17])[
  Lean 证明是 `siegelWeilStd:=siegelWeilStd_of_ct(ctSplit_of...)`，它给 `siegelWeilStd_pre` 喂入两个输入。第一是局部紧群中格的 Poisson 求和（`TW.Twp.poisson`）。第二是常数项分裂 `CTSplit`。该分裂由三条定律 `AbsConv`、`FirstEq`、`SecLaw` 构造，取三者阈值之最大。
]

#thm("4.17", "Eisenstein 延拓，EisBL")[
  设 $Y$ 是 CM 数据上秩 $n >= 1$ 的厄米或斜厄米空间，$E(s, f)$ 是倍增群 $G_2 (Y) = U(n, n)$ 上由 Siegel 抛物诱导表示的截面 $f$（配 Hecke 特征 $chi$ 与高度函数 $a$）构造的 Siegel Eisenstein 级数。则
  $ E(s, f)(x) = sum_gamma gamma a(gamma x)^(s - s_1) f(gamma x) $
  对某个 $t$ 当 $Re s > t$ 时收敛且全纯。对每个 $s_0 in CC$，存在整数 $k >= 0$、$s_0$ 的邻域 $U$，以及一个中等增长的连续函数族 $H(s)$——它与任何增长泛函配对时在 $U$ 上关于 $s$ 全纯——满足
  $ H(s) = (s - s_0)^k E(s, f) quad (s in U, s eq.not s_0). $
]

#lean("GlobalTheory.ThK.Dbl.EisBL", "Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesE.lean")
#lean("PositivityTheory.RgEis.Hd.eisBL", "Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinHalfPlane/SchwartzBruhatMajorants/SiegelMultOf.lean")

#caution("4.18")[
  这是带有限阶极点与中等增长的亚纯延拓。它对 $E(s, f)$ 的零点什么也没说。其中唯一的非零性陈述是：一个标量乘子 $A(s)$ 是一个不恒为零的整函数。
]

#proof[
  装配是 `eisBL:=eisBL_ofeisenstein_half_holds(siegelMult_of...)local_factorisation`。用到三个输入。
  + 右半平面上的收敛性与全纯性（`eisHalf`），由 Weierstrass M-判别法与一个 Godement 型收敛界完成。
  + 一个乘子定理（`siegelMult_of`）：一个不恒为零的整函数 $A$ 与一个整的中等增长族 $H$，在某个半平面上 $H = A dot.op E$。这是一个 Langlands 型的多元延拓，对行数归纳，用管域（Bochner 与 Hartogs）论证。基础情形经由 Epstein zeta 延拓与 Tate zeta 积分在绝对收敛区域中完成。
  + 一个单变量因子分解（`local_factorisation`）：一个不恒为零的整函数在任一点附近有有限阶零点及一个不取零值的全纯余因子。

  于是 $hat(E) = H\/A$（半平面之外）给出延拓。
]

#thm("4.19", "混合模型上 theta 函数的 Parseval")[
  设 $V$、$V'$、$W$ 为厄米空间，带一个迷向分裂 $V arrow.l.r$（迷向部分）$⊕ V'$。对 $V ⊗ W$ 的 Weil 模型上的 theta 型函数 $f_1$、$f_2$，函数
  $ u arrow.bar integral_(F') "Rf"_1 (u)(x) overline("Rf"_2 (u)(x)) dif x $
  在环面 $M_x (W, r)$ 上连续可积，且
  $ integral_(F_0) f_1 overline(f_2) dif mu_0 = integral_u integral_(F') "Rf"_1 (u) overline("Rf"_2 (u)) dif x dif u. $
]

#lean("GlobalTheory.MixParseval.parseval", "Development/AbelianVarietyTheory/Proofs/TwistedOperators/MixedModelParsevalThetaInnerProduct.lean")

这里 $R$ 是到混合模型的限制。Lean 陈述带许多关于单位余体积测度与迷向分裂的假设，我们未予复述。它的用途是替代 Gauss 和的相消：系数的平方和被一个上确界范数控制。#inferred[这是 Parseval 在提升塔中的角色；代码陈述了该恒等式以及一个可和性推论 $norm("Rf"(xi + u))^2 <= C_f^2$。]

#thm("4.20", "theta 积分相合，局部匹配")[
  设 $(V, V', W)$ 是一个 Weil 三元组：维数 $a$、$a'$ 与 $a + a'$ 的厄米空间，带两个 Weil 模型，由 Hecke 特征 $alpha$、$beta$ 扭曲。以下两条命题 `ThetaIntegralsAgree` 与 `LocalMatching` 成立：
  + （`LocalMatching`）对每个这样的三元组，存在实映射 $R$ 与有限位映射 $"Rf"$，匹配两个 Weil 表示的局部 theta 提升商。
  + （`ThetaIntegralsAgree`）两个 theta 积分以中等增长收敛。对匹配的数据，存在唯一非零常数 $c$ 使 $I_V (Phi) = c dot.op I_(V') (Phi')$（作为 $U(W)$ 上的函数），且好位处的余不变量相合。
  + （`StepBeta`、`StepAlpha`）当 $V'$（相应地 $V$）失去一个双曲平面时，常数通过 $c dot.op L(nu, S_0, s) = u c_1$（带显式因子）相联系，对 $V$ 亦然。这些因子是 Hecke L-值（`charL`）与 epsilon 因子或 Gauss 因子。
]

#lean("GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree", "Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean")
#lean("GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching", "Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean")
#lean("PositivityTheory.ThKR.theoremK_head2", "Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean")

#proof(uses: ref[定理 4.15 与 4.17])[
  关键定理是
  $ "theoremK_head2" : "EisBL" arrow.r "SiegelWeilStd" arrow.r "ThetaIntegralsAgree" ∧ "LocalMatching". $
  它是 `theoremK_head2_of_mod` 应用于一个已证的球面模块命题 `modSt2`。后者是 `closeSph`，一个 13 输入的装配（局部与整体闭性事实：取值、锥、稳定子存在性、双曲平面剥离 `TowerA`、`TowerB`、Bernstein 型分歧重数一，等等）。封装 `theta_integrals_agree_and_local_matching_of_literature` 供给 #ref[定理 4.17] 与 #ref[定理 4.15] 并得到结论。它的假设 `OpenLiteratureStatements` 在证明项中未被使用。
]

#caution("4.21")[
  有两对不同的声明被命名为 `ThetaIntegralsAgree` 与 `LocalMatching`。上文这一对位于 `WeilTensorModels`。第二对位于 `Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean`（命名空间 `GlobalTheory.SquareSt`），涉及 D7 数据上的扭平方。它由第一对经 `twisted_square_theta_integrals_eq` 导出。
]

== 稳定范围内的 U(n) × U(d) theta 提升

伽罗瓦侧各章需要一个从定酉群 $U(n)$ 到更大的定酉群 $U(d)$（CM 域 $E$ 上）的提升。关键在于：该提升被证明非零且自守，而未使用任何 L-值。

#defn("4.22", "IsLift 与 TLiftK")[
  设 $E$ 是带极大实子域 $F$ 的 CM 域。设 $U' subset {$ $U(d)(bb(A)_E)$ 上的函数$}$ 与 $U subset {$ $U(n)(bb(A)_E)$ 上的函数$}$ 为自守不可约子表示。若
  + $U'$ 是自守表示（字段 `aut`）；
  + 无穷权被 `IsLiftWt` 平移（字段 `wt`）：对 $k < n$，$2 lambda'_k = 2 lambda_k - d - m_W + n + m_X$；对 $k >= n$，$2 lambda'_k = n + m_X$；
  + 在每个分裂位 $w$ 处存在从 $"Mat"_(n times d)$ 的 Weil 模型 Schwartz 空间到 $tilde(tau)_w$ 的非零缠结算子（`LocPair`）（字段 `loc`）；

  则记 `IsLift`(U, U′)。命题 `TLiftK` 是：对每个带满足 `W.GoodK` 的基数据 $B$ 的 CM 域 $E$、每个秩 $n >= 1$ 且 `X.J = 1` 的定厄米空间 $X$，存在 $d_0$，使得对所有 $d >= d_0$、每个秩 $d$ 且 $W.J = delta dot.op 1$ 的定斜厄米空间 $W$、一切无穷型为 $m_X$、$m_W$ 且满足 `ResEtaPow`(χ_X, n) 与 `ResEtaPow`(χ_W, d)（对单位上限制的条件）的 Hecke 特征 $chi_X$、$chi_W$，以及每个其权 $lambda$ 对一切 $w$、$k$ 满足 $d + m_W (w) <= 2 lambda_k (w)$（该条件依赖于 $d$）的自守不可约 $U subset cal(A)(U(n))$，存在自守不可约 $U'$ 使 `IsLift`(U, U′)。
]

#lean("UpperTheory.TP.TLiftK", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean")
#lean("UpperTheory.TP.tLift_holds_k", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TPGHolds.lean")

#caution("4.23")[
  这不是 theta 对应。它只对定群成立、只在稳定范围成立、且只是提升的存在性命题。它不给出 Howe 对偶（成分的唯一性），也不给出持续性。
]

`tLift_holds_k` 的证明是复合 `tLift_of_tools_k`。它把一族工具命题与四块主要部件结合。部件是 `NonVan_k`（非零性）、`LiftAut_k`（自守性）、`ProjEx`（到某个像非零的不可约成分上的投影）与 `ReadLift_k`（经一个 Schur 型引理 `AbsIso` 读出权与局部映射）。还有一个阿基米德步骤 `RealPair_k`：它给出一个非零多项式 Fock 向量 $f_0$、一个同型的形式 $phi in U$，以及一个提升权 $lambda'$ 使 $f_0$ 具有该型。这是最低 K-型的簿记，用手完成。

#thm("4.24", "提升的非零性")[
  设数据如 `NonVan_k`：CM 域上 $U(n) times U(d)_RR$ 的一个 Weil 数对，$1 <= n$、$2n <= d$，一个带高度函数 $a$ 的 Haar 测度使 $integral a(g, 1)^t dif g < oo$ 对 $t >= t_0$ 成立，且 $t_0 < d\/2$。设 $U$ 是 $U(n)$ 的自守不可约表示，$f_0 eq.not 0$ 是一个多项式 Fock 向量，$phi in U$ 是与 $f_0$ 同型的非零元。则存在有限位测试向量 $phi_f$，使 $f_0 ⊗ phi_f$ 对 $phi$ 的提升不恒为零：
  $ theta(f_0 ⊗ phi_f, phi) eq.not 0. $
]

#lean("UpperTheory.TP.NonVan_k", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/GalTPDefs.lean")
#lean("UpperTheory.TP.nonVan_k", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TPGNonVan.lean")

#proof(uses: ref[定理 4.17])[
  证明（约 130 行，`nonVan_k`）有两步。两步中都不出现 L-值。

  第 1 步，单向 Rallis（`Rallis_k`）。令 $"coef"(g) = ⟨omega(g) Phi, Phi⟩$ 为 theta 系数，$"mc"$ 为 $phi$ 的矩阵系数。命题是：$integral "coef"(g) "mc"(g) dif g$ 收敛，且若提升为零则该积分为 0。证明用倍增法：Eisenstein 截面与 $phi$ 的配对在 $Re s$ 大时等于常数乘该积分。若提升为零，则配对在半平面上为零。由延拓（#ref[定理 4.17]），它在 $s_0 = (d - n)\/2$ 处为零，而在该点它等于该积分。所以只用到了延拓与在 $s_0$ 处的全纯性。

  第 2 步，主项压过尾部。选取有限位集 $S$ 与在 $S$ 处支撑于 1 的任意给定邻域内的隆起函数（`BumpAny_k`）。在 $S$ 之外取球面真空向量。分裂 $U(n)(bb(A)) = g_oo times g_S times g_"off"$（`Decomp_k`）。在紧的无穷部分上，Schur 正交性（`SchurStep_k`）给出
  $ integral_(g_oo) "coef"(x) overline("mc"(x c)) dif x = kappa "coef"(1) overline("mc"(c)), quad quad kappa eq.not 0, $
  因为 $f_0$ 与 $phi$ 落在同一个不可约表示中（`SameType`）。在 $S$ 处，系数支撑在隆起子群上，并在那里等于 $s dot.op "coef"(x')$，$abs(s) = a(c)^(d\/2)$（`Datum_k`）。在 $S$ 之外，$a(c)^(d\/2)$ 在非整点 $c$ 上的积分小于整点的体积（`Tail_k`）；这用到了 $t_0 < d\/2$。抽象引理 `AbsNe` 接着说：若主项在集合 $K$ 上有常值尺寸，而其余部分被 $w$ 控制、且 $integral_(K^c) w < mu(K)$，则总积分非零。应用它即与第 1 步的消失性矛盾。
]

`Rallis_k` 是稳定范围 $2n <= d$ 的一个独立的单向倍增命题。它不是 #ref[定理 4.13]——后者需要 $"rk" A < "rk" B <= 2 "rk" A$，即相反的体制。

#rem("4.25", none)[
  与最终命题之间没有循环。唯一进入“$d$ 大”的地方是 $t_0 < d\/2$ 与 $2n <= d$。#inferred[黎曼猜想命题的任何 L 函数都不出现，且未使用 $0 < Re s < 1$ 中的任何点。我们核查了 `nonVan_k` 的证明，但未为此核查整个库。]#inferred[该区域确实出现的 Hecke L-值（在 `StepBeta`、`StepAlpha` 中）位于整数点或 $Re s >= 1$。]对 $d > 2n$，点 $s_0 = (d - n)\/2$ 落在收敛区域内，因此那里不需要延拓。
]

#thm("4.26", "提升的自守性")[
  在 `LiftAut_k` 的假设下，存在线性映射 $Theta : "PolData" arrow.r {cal(A)(U(n)) arrow.r cal(A)(U(d)) "的共轭线性映射"}$，使得对每个 $Phi$ 与 $U(n)$ 上的每个自守形式 $phi$：
  + $Theta(Phi)(phi) = h arrow.bar lr(integral theta_Phi (g, h) phi(g) dif g)$，这正是 theta 提升；
  + $Theta(Phi)(phi)$ 是 $U(d)$ 上的自守形式；
  + $Theta$ 是等变的：$Theta(omega(g, h) Phi)(R_g phi) = R_h Theta(Phi)(phi)$。
]

#lean("UpperTheory.TP.LiftAut_k", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/GalTPDefs.lean")
#lean("UpperTheory.TP.liftAut_k", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TPGLiftAut.lean")

#proof[
  自守性是直接的，且不使用 Eisenstein 级数。
  + 连续性（`continuous_thetaLift_of_definite`）使用定商的紧性。
  + 在 $U(d)(F)$ 下的左不变性（`lift_left_k`）来自 theta 分布的不变性（`thetaBasic_k`），后者依赖于 Poisson 求和。
  + 光滑性：$U(d)(bb(A)_f)$ 中的稳定子由 Schwartz 函数的水平界（`level_sch_k`）是开的。
  + 无穷处的有限维轨道：多项式 Fock 空间在 Lie 代数下稳定（`exists_finiteDimensional_weil_archimedean_orbit`）。
  + 等变性：`polStab_k` 与 `thetaLift_weil_translate_equivariant`。
]

映射 $Theta$ 通过选取有理不变连续函数空间的补空间（`Submodule.exists_isCompl`）装配成线性映射。这个选择只影响线性结构；(1) 中的恒等式是对自守 $phi$ 断言的。

#heading(numbering: none, outlined: false)[局部稳定范围结果与 TwoUp]

在分裂位处，提升由一个关于 $"GL"_n times "GL"_d$ 的纯局部命题控制。

#thm("4.27", "局部提升是一个归纳，LiftIso")[
  设 $k$ 是非阿基米德局部域，$n < t$，$nu$、$b$ 是 $k^times$ 的光滑酉特征。设 $sigma$ 是 $"GL"_n (k)$ 的不可约可酉化光滑表示，$pi$ 是 $"GL"_(n + t) (k)$ 的不可约光滑表示，带 `IsLift`(ν, b, σ, π)（一个非零的 Weil 模型缠结算子）。则
  $ "contra"(pi) tilde.op "contra"("src"_(nu b)(sigma)) times (b^(-1) ∘ "det") quad quad "(抛物诱导)", $
  其中 $"src"^c (sigma)(g) = c("det" g) sigma(g^(-T))$。
]

#lean("UpperTheory.Gal.TP.Loc.LiftIso", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SatakeLifts/SrcApply.lean")
#lean("UpperTheory.Gal.TP.Loc.liftIso_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SatakeLifts/LiftSatUHolds.lean")

#thm("4.28", "提升的 Satake 参数，LiftSatU")[
  设 $n$、$d$ 满足 $2n < d$，$chi_X$、$chi_W$ 为 Hecke 特征，$U$ 是 $U(n)$ 的自守不可约表示，$U'$ 是 $U(d)$ 的自守不可约表示，带 `IsLift`(U, U′)。设 $w$ 是分裂位，$chi_X$、$chi_W$ 在 $w$ 处不分歧。若 $U_w$ 的 Satake 多重集为 $B$，则 $U'_w$ 的 Satake 多重集为
  $ B dot.op lr( (chi_X (w))/(chi_W (w)) + "seg"_w (chi_X (w), d - n) ), $
  其中 $"seg"$ 是由 $d - n$ 个连续特征组成的段。
]

#lean("UpperTheory.Gal.TP.Loc.LiftSatU", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SatakeLifts/CompUnit.lean")
#lean("UpperTheory.Gal.TP.Loc.liftSatU_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SatakeLifts/LiftSatUHolds.lean")

#proof(uses: ref[定理 4.27])[
  `liftIso_holds` 是 `liftIso_of` 应用于一个双提升定理（`pairOfLift`），带四个输入：光滑性、Schwartz–Bruhat 空间的保持、一个模型字典、以及一个分离命题。这是一个 Mínguez 型的稳定范围定理；未使用 Howe 对偶与 Kudla 持续性。随后，`liftSat_holds`、`pairSat_holds` 与 `liftSatU_holds` 通过把 Satake 参数沿诱导、逆轭、行列式扭曲以及分裂位处局部域的同构 $E_w tilde.op F_v$ 输运而得到。
]

#prop("4.29", "TwoUp")[
  设 $E$ 是在其极大实子域 $F$ 的所有位上都不分歧的 CM 域，$[F : QQ]$ 为偶数，$n >= 1$ 为偶数（`TwoUpAll`；没有进一步的非分歧条件）。对 $U(n)$ 上每个带权 $lambda$ 的自守不可约 $U$ 与每个分裂位 $w_0$，存在整数 $t$ 与 Hecke 特征 $kappa, psi_1, dot.op, psi_t$ 及 $psi'_1, dot.op, psi'_t$，使得：$n + t$ 为奇数；$kappa$ 是代数且正的，无穷型为 $m$（`IsAlgPos`(κ, m)）；存在 $U$ 到 $U(n + t)$ 的两个提升 $U_1$、$U_2$，特征分别为 $kappa, psi$ 与 $kappa, psi'$；族 ${psi_i}$ 与 ${psi'_j}$ 不相交（对一切 $i, j$，$psi_i eq.not psi'_j$）；且 $kappa$ 与一切 $psi_i$ 在 $w_0$ 处不分歧。
]

#lean("UpperTheory.Gal.TP.Sub.TwoUp", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SplitLineSubtraction/RowDefOfOdd.lean")
#lean("UpperTheory.TP.TwoUpOK", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/AllCoreOf.lean")
#lean("UpperTheory.TP.twoUpOK_of_steps", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/TwoUpOKOfSteps.lean")

#proof(uses: ref[定义 4.22 与定理 4.28])[
  定理 `twoUpOK_of_steps` 走四步。第一，`BaseNG` 给出对 `TLiftK` 足够好的基数据。第二，`TLiftK` 给出 $d_0$；取 $t = 2(d_0 + n) + 1$，于是 $n + t$ 为奇数且 $2n < n + t$。第三，`ChrPairs` 给出两族 $psi$-集不相交的特征对，全部在选定的分裂位不分歧。第四，`UpOf` 把 `IsLift` 转化为 `IsUp`：提升后的权是 $"wtJumps"(lambda') = "wtJumps"(lambda) + m union {-p_i}$，而分裂不分歧位处的 Satake 数据来自 #ref[定理 4.28]。
]

`TwoUp` 的用法如下。若 $r_1 = rho ⊗ kappa + (psi_i)$ 与 $r_2 = rho ⊗ kappa + (psi'_j)$ 带不相交的特征集，则 $rho$ 通过减法被分离出来（`Subtract`、`rowDef_of_odd`）。这就是从奇秩情形得到偶秩伽罗瓦表示的方法。#inferred[减法的代数只从命题陈述读出。]

== 关于 Stepanov 方法的一点评论

#rem("4.30", "解读，而非 Lean 命题")[
  本注是阅读者的解读与作者自己的描述。它不是定理，Lean 文本中也不含这样的命题。在我们读过的文件中，没有发现 “Stepanov” 一词的使用，也没有 Wronskian 式的行列式。

  在函数域上的 Stepanov 方法中，人们构造一个辅助多项式，使它在被计数的点处以高阶 $m$ 消失。重数 $m$ 把整体误差除以 $m$，代价是随 $m$ 增长的亏损。在整数上，不存在带指定重数的多项式。作者的描述说：酉群之间的迭代 theta 提供了这个替代品。这些群除最后一步外都是不定的（#ref[定义 4.1]：$sigma_W(j) = (k + j - 1, m - j)$）。链的长度是 $sqrt(X)$ 的量级，其中 $X$ 是 von Mangoldt 和的长度。

  代码在以下方面与这一读法吻合。素数和 $"ASK"$ 是对 $m$ 个提升的和（字段 `Ident`）。#inferred[$m$ 个权 $w_(u^0, j)$ 大致同尺寸，所以对 $j$ 的和看起来像一个素数和的 $m$ 次重复。]代码只给出厚类上的 $b <= w <= b + eta + 1$、其余处的 $w <= 2 b'$（`NodeSizes`），而主项包含 $sum_j log w_j$。每个提升把整除因子大约乘上 $b$，这给出 $log T approx m x^epsilon$。误差有不依赖 $m$ 的部分与随 $m$ 增长的部分（#ref[命题 4.7]）。除以 $m$ 起到重数的作用，而平衡 $m approx sqrt(x)$ 起到 Stepanov 论证中通常重数选择的作用。
]

#heading(numbering: none, outlined: false)[本章传递什么]

- 塔数据及其秩（#ref[定义 4.2]）与尺寸窗口（#ref[定义 4.4] 与 #ref[定义 4.6]）。
- 指数平衡 #ref[命题 4.7]，及其在 #ref[推论 4.8] 中的使用。
- 逐提升余体积界（#ref[命题 4.11]），在 #ref[定义 4.10] 的条件下，供体积章使用。
- theta 积分：#ref[定理 4.13]、#ref[定理 4.15]、#ref[定理 4.17] 与 #ref[定理 4.20]，全部由库证明。
- 定提升：#ref[定理 4.24]、#ref[定理 4.26]、局部 Satake 公式 #ref[定理 4.28]，以及供伽罗瓦章使用的 #ref[命题 4.29]。
