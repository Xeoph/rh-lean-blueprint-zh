// ch5.typ —— 第 5 章 格体积、乘积公式与素数计数
#import "lib.typ": *
#pagebreak(weak: true)

= 格体积、乘积公式与素数计数

本章把几何转化为素数和上的一个界。几何栖身于志村簇上的 Hodge 丛之中。素数和是解析各章的量 $"ASK"$：在宿主 CM 域中惯性的素数 $p$ 上的 $log p$ 加权和。证明需要这一步，因为解析一侧只要求一个上界 $"ASK" <= "MAIN" + "error"$。该界是关于格的命题，而非关于素数的命题。

路线分四部分。第一，算术 Hilbert–Samuel 从两侧数出 Hodge 丛的小截面，并从上方给出每个 theta 提升格的对数余体积的界（#ref[定理 5.13]）。第二，乘积公式把该余体积写成一个阿基米德项加上有限位处 $log N(w)$ 乘局部指标的和（#ref[定理 5.15]）。第三，在每个惯性素数处的局部 theta 分析把局部指标从下方用显式的组合增益控制住（#ref[定理 5.19]）。第四，阿基米德常数由 Chowla–Selberg 与 $gamma$ 及 $L'\/L (1, chi_(-d))$ 等同（#ref[定理 5.23]），然后合并一切（#ref[定理 5.27]）。

两个事实塑造了全章。我们没有在 theta 塔中发现 Stepanov 型的消失阶论证；下文的辅助截面 $theta$ 有赋值界但没有重数。此外，没有任何 Hecke 特征值或表示数进入这座桥。余体积与素数之间的联系，是大 CM 域上厄米格的乘积公式。

下文所有编号命题都译自 Lean 源码。凡未读证明主体之处，我们都予以说明。

== 厄米格、对数余体积与斜率

#defn("5.1", "格的对数余体积")[
  设 $K$ 是数域，$X = (X_v)_(v bar.v "oo")$是由无穷位标号的 $d "times" d$ 复矩阵族，$L subset K^d$ 是一个 $cal(O)_K$-子模。置
  $ "lcv"(X, L) = 2\/[K : "QQ"] dot.op log "ht"(X, L), $
  其中 $"ht"$ 是格 $L$ 对厄米数据 $X$ 的高度（`Formalism.HN.ht`，相对于 $K^d$ 的标准基）。
]

#lean("Formalism.DivisionValues.lcv", "Formalism/QuotientMetricDivisors/Statement.lean")

这就是 `lcv_le`、`BoundsMu` 与 `L3` 使用的 lcv。同一文件还定义了位权 $l_w(w) = log N(w)\/[K : "QQ"]$ 与 Gram 行列式。一个相关的变体 $"lcv"(b, X, e, M) = "lcvInf" + "lcvFin"$（一个 Gram 行列式项加上局部指标的和）位于 `Formalism/SizeWindowBrackets/LcvBaseChange.lean`、命名空间 `Formalism.LFunctionChainParameters.LLcv`。它与上文 lcv 的关系在本章中未被使用，我们也未核对。

#defn("5.2", "斜率")[
  对秩为 $D$ 的格 $M$，斜率是 $mu(M) = - "lcv"(M)\/D$。这是引理 `MuLcv`，由 `log_covolume_slope_mu` 证明。
]

#lean("Formalism.DivisionValues.MuLcv", "Formalism/SizeWindowBrackets/SBrDiv.lean")

于是 $"lcv"\/D$ 的上界就是斜率的下界。下文使用的欧氏斜率不等式是对实内积空间中的格陈述的。

#env("输入定理", "5.3", "斜率不等式（Bost 型）")[
  设 $L subset E$、$M subset F$ 是有限维实内积空间中的离散 $"ZZ"$-格，$L eq.not 0$。若 $phi : L arrow.r M$ 是 $"ZZ"$-线性的、单射的，且 $norm(phi x) <= C norm(x)$ 对一切 $x$ 成立，则 $mu(L) <= mu_max (M) + log C$。
]

#lean("SlopeInequality", "Formalism/LatticeSlopes/Statement.lean")

源码中的名字就是朴素的 `SlopeInequality`，不是“Bost”。它被证明（`slopeInequality_of`，由 `SlopeLeMuMax` 得来），不是假设。$cal(O)_K$ 上的版本经由带因子 $2\/[K : "QQ"]$ 的 lcv 处理。[用到 #ref[定义 5.1]]

== 辅助 theta 截面及其两个界

余体积界比较环向紧化（toroidal compactification）的一个分支 $Z$ 上、权 $u'$ 与 $u$ 的两个尖点形式格。权为 $8(u - u')$ 的固定截面 $theta$ 是桥梁。乘以 $theta^k$ 把权 $8k u'$ 的小形式映入权 $8k u$ 的形式。

#defn("5.4", "辅助截面数据")[
  设 $"c".F$ 是模问题（moduli problem）的系数域，$e$ 是其有限位上 finitely supported 的实除子，$t$ 是其复嵌入上的共轭不变函数。
  - $"cost"(e, t) = sum_l e(l) log N(l) + lr(sum_sigma t(sigma))\/["c".F : "QQ"]$。
  - `Carries`(Z, u, u′, θ)：$theta$ 是权 $8(u - u')$ 的截面，$theta$ 在 $Z$ 上不恒为零，且对每个 $k$ 与每个权 $8k u'$ 的尖点形式 $f$，$theta^k f$ 是权 $8k u$ 的尖点形式。
  - `FinBd`(Z, G, a, θ, e)：对每个有限位 $l$、每个在某处有格元具有有限赋值的容许赋值 $v$，有 $a dot.op "depth"_v (G) <= v(theta) + a e(l)$。
  - `InfBd`(Z, G, G₀, a, θ, t)：在每个好的复嵌入 $sigma$ 与 $Z$ 上的每个标架 $y$ 处，$norm(theta)_sigma^2 (y) <= exp(2 a t(sigma)) dot.op "Berg"_sigma (y)^a$，其中 $"Berg"$ 是权 $G$ 尖点形式的 Bergman 核。
  - `Mult`(Z, u, u′, cc)：`NoBase` 成立，且存在 $theta$、$e$、$t$ 满足 $a = 8$ 时的 `FinBd`、$a = 8$ 时的 `InfBd`，以及 $"cost"(e, t) <= "cc"$。
]

这里 `NoBase` 说权 $G$ 的格没有基点（base locus）：任何具有有限赋值的形式，在同一处都有某个格元具有有限赋值。

#lean("GlobalTheory.CovHt.Mult", "Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean")

同一文件定义了 `Carries`、`FinBd`、`InfBd`、`NoBase` 与 `cost`。

赋值条款并不是在许多点上的 Stepanov 重数。#inferred[它是 $theta$ 在形如 $8\/2500 dot.op phi \/ e_0 - 8 e(lambda)$ 的整点处的 p-进下界。]数 $phi$ 来自点的约化类型，经由 PEL 整模型上的一个二次型；常数 $1\/2500$ 是一个自由的小常数（常数报告）。阿基米德条款是在 Lean 中证明的，不是引用的。

#prop("5.5", "theta 的 Bergman 核界")[
  辅助截面由 level-$5^4$ theta 常数构造。引理 `theta_function_le_bergman_kernel_alt` 给出估计 $abs(f^2)^3 <= e^beta "Berg"$（在模空间的细部与厚部），其中 $beta$ 在尺寸簿记中由 $T^beta <= C_E$ 控制。#inferred[由此可推出 $a = 8$ 时 `InfBd` 的界 $"homN"(theta)^2 <= exp(2 dot.op 8 t) "Berg"^8$；这最后一环我们没有读。]
]

#lean("theta_function_le_bergman_kernel_alt", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsSectionBoundedByBergmanKernel.lean")

#proof(uses: ref[定义 5.4])[
  我们读了命题陈述与证明的头部。估计被分成边界附近的细部与厚部。#inferred[输出喂给 $a = 8$ 的 `InfBd`。]
]

== 从两侧数小截面

记 `smallL`(Z, G, τ, t) 为权 $tau G$ 的尖点形式 $f$ 之集：在每个有限位处赋值深度至少 $tau dot.op "depth"(G)$，且在每个好嵌入处 $norm(f)_sigma^2 <= e^(2 tau t) "Berg"_sigma^tau$。计数 `volL` 是由 `smallL` 构造的体积泛函（`countVol`）。斜率 `compVolSlope` 是 $"vol"(t)\/delta - t$ 对 $t$ 的下确界。

#env("输入定理", "5.6", "算术 Hilbert–Samuel")[
  设 $X$ 是 $"Spec" k$ 上相对维数 $D$ 的整算术簇，$L$、$N$ 为厄米线丛，$L$ 为 nef 且算术自相交为 $a$。则最终对 $m$，$L^m ⊗ N$ 的小截面之集有限，且
  $ log {#raw("smallSec")}(L^m ⊗ N) - a/((D + 1)!) m^(D + 1) = o(m^(D + 1)). $
]

#lean("GlobalTheory.Published.ArithHilbertSamuel", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/SmallSecTensTriv.lean")

这是一个忠实的渐近形式。它在库中被证明：从 ample 情形、Hironaka 主化与算术相交演算（`arithHilbertSamuel_of_principalisation`）。环境丛是 `PublishedHodgeBundleTheorems`，它是封闭的：其 28 个字段由 Lean 定理填满。另见 #ref[输入定理 7.7] 与 #ref[输入定理 7.8]。

#caution("5.7")[
  Lean 名 `MoriwakiBigStatement` 是个误名。它陈述的是：对半正、共轭不变、nef 的 $A$，$Pi(A^(D + 1)) <= "arVol"("small sections")$。那是算术 Siu 或 Hilbert–Samuel 下界，不是大性判据。
]

#lean("MoriwakiBigStatement", "ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/MoriwakiSt.lean")

#prop("5.8", "上侧计数")[
  假设 `SelfIntersectionBound` 与 `SmallSectionsInject`。设 $Z$ 是满足 $0 < "dg"(u, Z)$、无基点、并带一个范数 $<= e^t$ 的短生成元族的权 $u$ 格的分支。则
  $ "volL"(Z, u, t) <= "dg"(u, Z) dot.op lr("ht"(u, Z) + t). $
]

#lean("SelfIntersectionVolumeEstimates.VolUpG.volume_line_bundle_le", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/VolumeLineBundleLe.lean")

#proof(uses: ref[输入定理 5.6 与定义 5.4])[
  `SmallSectionsInject` 说 $L^(8 i)$ 的小截面单射入平移后的 nef 模型 $L(t)^(8 i)$ 的小截面。`SelfIntersectionBound` 给出平移模型的自相交 $a <= [K : "QQ"](D + 1) "imageDeg" ("imageHeight" + t)$。然后 #ref[输入定理 5.6] 以 $a m^(D + 1)\/(D + 1)!$ 数出平移模型的小截面，除以首项系数即得命题。在 Lean 中，计数经由 `countingVolume_le_selfIntersection_nefHermitianBundle` 并带假设 `hP.q9` 完成。
]

#lean("SelfIntersectionVolumeEstimates.SmallSectionsInject", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/VolumeEstimateHypotheses.lean")

单射假设由 `PositivityTheory.Xj7N.small_sections_injective` 供给；我们没有读那个证明。

#defn("5.9", "下侧假设")[
  对带 gap $g$ 的权 $u$，置 $"bndB"(u, g) = 4 abs(Psi) (p + q)^2 (1 + sup abs(u)\/g)$，且
  $ "errX"(s, u, g) = lr(log "bndB"(u, g) + s) ell_1 (u) + q sum_tau lr(max_i u_(tau i) - min_i u_(tau i)), quad quad ell_1 (u) = sum_(tau, i) abs(u_(tau i)). $

  `MeanAll`(s, C) 说：对每个带 gap $g$ 的权 $u$，存在斜率 $"sl"_Z <= "compVolSlope"(Z, u)$，满足 $-C "errX"(s, u, g) <= 1/(\#iota) sum_Z "sl"_Z$。
]

#lean("GlobalTheory.CovHt.MeanAll", "Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean")

它从何而来。命题 `DeepStR`（文件 `Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ModelSmall.lean`）打包了这个下界。它由 `deepStR_of_use` 从 `HSUse`、`MoriwakiBigStatement`、`ResK`、`ArithIntersectionSystem` 与好塔体积定理构造。“体积 ≥ 自相交”形式的算术 Hilbert–Samuel 说：nef 丛有许多小截面。这从下方控制了分支斜率的平均。[用到 #ref[输入定理 5.6]]

#prop("5.10", "高度下界")[
  固定分支 $Z$ 与满足 `Mult`(Z, u, u′, cc) 的权 $u$、$u'$。假设 $rho < 1$、$(1 - rho) "dg" <= delta'$、$log Lambda <= c_s$、$0 <= "ht" + c_s$、$s <= "compVolSlope"$。则
  $ (1 - rho) max(0, s + c_s) <= lr("ht"(u, Z) + c_s + "cc" + "htCost" dot.op ell_1 (u')). $
]

#lean("slope_le_height", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/HeightAddLogNonneg.lean")

#proof(uses: ref[命题 5.8 与定义 5.4、5.9])[
  乘以 $theta$ 给出 $"compVol"(Z, u', t) <= "volL"(Z, u, t + "cc" + "htCost" ell_1 (u') + epsilon)$（`compVol_le_volL_deep`）。下侧计数说：一旦 $t >= c_s$，左边至少是 $delta' (s + t)$。#ref[命题 5.8] 用 $"dg" ("ht" + t + dots.h.c)$ 控制右边。比较、令 $epsilon arrow.r 0$、并用 $(1 - rho) "dg" <= delta'$，即得所展示的界。项 $"htCost" = sum_p p "htEx"(p) log p$，其中 $"htEx"(p) = (p^(-1))/1 + 40 v_p ("disc" E)\/[E : QQ]$，是比较两个赋值系统的代价（`HTCmp`）。
]

== 余体积界

固定 theta 塔中提升指标 $i < m$。数据是：$"lenT" = ceil("PP"^2 "Dflag"^2 k\/m)$，其中 $"Dflag" = "dim" "Flag"$；$"binT" = binom("lenT" - 1, "Dflag")$（二项式系数）。$E$ 为误差的单位 `unitE`（Lean 中 $b <= "unitE" <= x^A b$，$b = exp(x^epsilon)$），且 $"l3u" = B_0 dot.op "llx"$ 是余体积界的误差部分；$"mainT"(i) = sum_tau w_tau c_1 (tau)$ 是 Hodge 扭曲的次数。每个簿记条件（`GramAt`、`RecAt`、`CutAt`、`BadAt`、`LamAt`、`SizeAt`、`CoreAt`、`LowAt`）都是关于点族的最终陈述。

#prop("5.11", "Hilbert–Samuel 次数界")[
  条件 `HSAt` 对覆盖 $Y$ 与权 $u_M$ 断言：存在 $A > 0$、$R >= 0$，$A log max(A, 1) + R <= C dot.op "unitE"$，使得对每个分支 $Z$，
  $ "binT" dot.op "dg" dot.op "lenT" dot.op "ht" - 3 ("Dflag" + 1) abs("ht") - A log(2 + abs("ht")) - R <= deg_C (u_M)(Z). $
]

#lean("GlobalTheory.CovTop.HSAt", "Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean")

证明装配于 `hilbertSamuel_of_component_estimates_alt`。想法是：权 $u_M$ 的截面由短形式的 $T$-重乘积生成，故次数像 $T dot.op "ht"$ 那样增长。这就是为什么 #ref[命题 5.10] 的高度要乘 $T$，以及为什么每个斜率误差 $X$ 必须满足 $T X <= C E$。[用到 #ref[命题 5.10]]

#lem("5.12", "实数核心")[
  设 $iota$ 是有限非空指标集（诸分支），且对每个 $c$ 以下成立：$0 <= h_c + c_s$；$(1 - rho) max(0, "sl"_c + c_s) <= h_c + c_s + "cc"$；$-X <= 1/(\#iota) sum_c "sl"_c$；以及 #ref[命题 5.11] 的次数界。假设 $T X <= C_a L_0 U + e_1$、$T "cc" <= C_b L_0 U + e_2$，以及一个把 $c_s (6 D + 10 + T(z + 2 rho)) + A log max(A, 1) + dots.h.c$ 控制在 $b\/4$ 的尺寸不等式。若 $(sum_c deg_c)\/(sum_c d_c) - P <= mu_U$，则 $mu_U >= -2 lr((C_a + C_b) L_0 U + b\/4)$。
]

#lean("Formalism.ExtensionFiltration.CombinedAverageDegreeBound", "Formalism/MeanHeightDescent/CombinedAverageDegreeBound.lean")

它被证明为 `mean_height_sum_bound`（文件 `Formalism/MeanHeightDescent/DivisionInequalityWithCovolume.lean`），经由 `mean_height_sum_bound_holds`。下游使用的输出是 $mu(u_M) >= -2(3 C_1 + C_2 + 4) E$。为余体积界打包这一点的实数封装是：

#lean("GlobalTheory.CovTop.FromComp.core", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformLowerBoundOfSums.lean")

[用到 #ref[命题 5.10、5.11 与输入定理 5.3]]

#thm("5.13", "余体积界，逐提升")[
  对封闭类 `FamHyp` 中的每个族，存在 $C_0 >= 0$，使得最终在满足点条件（`RowsTAlt`）的所有点 $p$ 处，对每个 $C >= C_0$ 与每个提升指标 $i < m$，
  $ ("lcv"(X_(W_i) ; M_i))/(D) <= "mainT"(p, i) + C dot.op "unitE"(p). $
  等价地 $mu(M_i) >= -"mainT"(p, i) - C E$。常数 $C_0$ 来自 $C_1 + C_2 + 1$，其中 $C_1$、$C_2$ 是 `CoreAt` 与 `LowAt`（#ref[命题 4.11]）的常数。在 Lean 中这就是谓词 `L3` 在 $N = p dot.op N(C)$ 处，即 $forall j, "lcv"(X_(W_j) ; M_j)\/D <= N dot.op "l3"_j$，其中 $N dot.op "l3"_j = "l3mj" + C "l3u"$ 而 $"l3u" = B_0 dot.op "llx"$。
]

#lean("GlobalTheory.CovTop.CovolumeBoundOfX", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LiftLambdaBound.lean")
#lean("lcv_le", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean")
#lean("L3", "Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean")

#proof(uses: ref[命题 5.11、引理 5.12 与定义 5.1])[
  逐提升不等式是 `lcv_le`。其假设为：$0 < x$、$0 <= C_1$、$C_2$、尺寸条件 $12 exp(-x^(e_z\/7))(x^A + x^B + C_1 + C_2 + 1) <= 1$，以及最终条件 `GramAt`、`RecAt`、`CutAt`、`BadAt`、`LamAt`、`SizeAt`、`CoreAt`、`LowAt`。`RecAt` 说 $"lcv"(M_i)\/D <= -"slope"_2("good" "sublattice")$。`LowAt` 说 $-"mainT" - C_2 E <= mu_"core"$。好子格由有限酉群的一个幂等元切出（`CutAt`）；切的代价在斜率上至多 $12 delta Q$，$delta = exp(-x^(e_z\/7))$（`slope_good_ge`）。`LowAt` 来自 `lowAt_of_cover`，后者串联：实核心（#ref[引理 5.12]）、一个平坦扭曲（`FlatAt`）、穿过 $n$ 个满足 $abs(phi_h f)^2 <= e^(2 b) abs(f)^2$ 的映射的下降（`MapsAt`、`RkAt`、下降），以及环的界（`RingAt`，每步损失 $2 b$）。打包成 `CovolumeBoundOfX` 的是 `covolX_of_lift_bounds_and_coreLe`，装配于 `topCovolG_alt_alt`。
]

#rem("5.14", none)[
  锚定条件 `AnchorAt` 表明 `mainT` 与 $sum_tau (p - q) "anchor"(tau) dot.op "logOm"$ 相差不超过 $100 "unitE"$，故 `mainT` 携带与最终主项相同的周期常数。
]

== 乘积公式

诸提升 $M_j$ 沿一个格 $"RR" subset K^D$ 粘合，后者由每个位 $w$ 处的局部格 $"matLat"(iota(mu_w), "abelian"_2 (mu_w))$ 构造。参考元组 $mu_w$ 是 $w$ 处 Frobenius 扭曲的点。$M_j$ 在 $w$ 处对其参考格的局部指标是 $"idx"_w (M_j, "matLat"(theta_j (mu_w), T_(l, j) (mu_w)))$。置 $A_(j w) = "idx"_w + "idx"_bar(w) + j_w$，即对 $w$、其共轭与一个跳跃项之和。

#thm("5.15", "提升塔的乘积公式")[
  在 `BoundsMu` 的设定下（CM 域 $K$、有限多处变更的元组 $mu$、厄米数据 $X_(W_j)$、格 $M_j$ 与局部等于 $"matLat"(iota(mu_y), "abelian"_2 (mu_y))$ 的 $R$、扭曲位的有限集 $T_w subset S_y$、以及局部指标界），有
  $ mu(R^"vee") <= "meanLog" kappa + sum_j ("lcv"(X_(W_j) ; M_j))/(D) + 2 sum_j sum_(y in T_w) frak(l)_w (y) F_y^j + L_G + sum_j (E_1^j + E_2^j) + E_3, $
  且对每个 $j$：$"lcv"(X_(W_j) ; M_j)\/D = -mu(M_j)$。
]

#lean("slope_bounds", "Formalism/DivisorInequality/DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds.lean")
#lean("BoundsMu", "Formalism/DivisorInequality/StatementObj.lean")

命题 `BoundsMu` 是一个约四十条假设的长蕴涵。主要的几条：局部标量恒等式 $"det" "ratio"(X_Q, X_E, iota)_v = kappa^D product_j "det" "ratio"(X_T^j, X_W^j, theta_j)_v$，它们说 $iota$ 与 $theta_j$ 在每个同型分支上是标量，使 Gram 行列式跨塔相乘；指标在有限集 $S_y$ 之外局部为零；以及在扭曲位处的界 $"idx"_y + "idx"_bar(y) <= (sum_j (2 F_y^j + "err"_y^j) + 2\/ell_y^2) D$。

#proof[
  这是一个真正的证明（71 行），不是封装。它调用 `untwisted_choice`、`divisor_bounds_chain_weak`、`dual_lattice_measure` 与 `ExtensionFiltration.log_covolume_slope_mu`。想法是 `IndefRows.stepB` 的格恒等式：
  $ "lcv"(R) <= D "meanLog" kappa + sum_j "lcv"(X_(W_j) ; M_j) + sum_w frak(l)_w (w) lr(v_w (G_m) + sum_j A_w^j). $
  前两项是阿基米德的。最后的和是乘积公式：每个有限位贡献其局部指标乘一个权。
]

#lem("5.16", "p 上方的位累加为 log p")[
  `UnitRule` 要求：对一个有限的位集 $W$、映射 $"below" : W arrow.r "NN"$、权 $l_w$ 与素数集 $P_s$：对 $p in P_s$，$sum_(w in W, "below"(w) = p) l_w = log p$；对 $P_s$ 上方的 $w$，逐位的增益与 $tau$ 等于逐素数的；对 $P_s$ 之外的 $w$，它们为零。在其下，置 $"GaW" = 2 sum_w l_w lr(sum_j "gain"_j (w) - tau(w))$ 与 $"deficit"_p = sum_(j, t) v_(M_(j, t)) (p) - lr(sum_j "gain"_j (p) - tau(p))$，引理 `SplitEq` 给出
  $ "ASK" - "GaW" = sum_(p in P_s) 2 log p dot.op "deficit"_p + sum_(j, t) "dT"_(j, t). $
]

#lean("UnitRule", "Formalism/SizeWindowBrackets/SecondKindBucket.lean")
#lean("SplitEq", "Formalism/SizeWindowBrackets/SecondKindBucket.lean")

#proof(uses: ref[定理 5.15])[
  把对位 $w$ 的和按其下方素数分组，并使用 `UnitRule` 的第一条款。不等式版本 `SplitLe` 把 $"ASK" - "GaW"$ 控制为 $sum_(p in S) 2 log p dot.op "servedLoss"_p + sum_(p in.not S) 2 log p dot.op "wholeAsk"_p + sum "dT"$。被服务的素数 $p in S$ 满足尺寸条件（`SizeData2`），使 deficit 很小；其余素数增益为零，于是整个 ask 是损失，由桶引理控制。
]

#rem("5.17", none)[
  符号约定值得警告。恒等式 $"lcv"\/D = -mu$ 是被证明的。从 $M_u$ 到 $N_u$ 的过程中哪个格是子格，编码在下文的 `SlopesN` 中；我们没有独立追踪它。
]

== 惯性素数处的局部增益律

乘积公式需要对惯性素数处局部指标的下界。它来自周期整除性。设 $N_u = L."NuLat"(u)$ 为提升的格，设 $w$ 是大 CM 域 $"LL"$ 在有理素数 $p$ 上方的位，$p$ 不同于水平素数 $T$，也不同于两个型素数 $g_0$、$g_1$。

#defn("5.18", "增益")[
  置 $"partner"(D, p, t, e) = ("decide"("IsSg" p ∧ "Odd" e), t + e dot.op "Frob"_p)$。对权向量 $a : "HH" arrow.r "ZZ"$ 与填充函数，置
  $ "askP"(p, j, s) = sum_("e odd") max lr(0, a(s)/(p^e) - "fill"_j ("partner"(p, s, e))). $

  变体 `askG` 使用容量 `fillG`。计算出的增益 `gainP`(p, j) 在（$p$ 是 residue-class-zero 且 `hP`(p) = 0）或 $p > X''$ 时为 0，否则为
  $ sum_(t_0 in "VV") max lr(g_U (t_0) - "Pr"(t_0), max(g_0 (t_0), 0)) + sum_(t_0 in "reps" ∖ "VV") max(g_0 (t_0), 0), $
  其中 $"g"_0 (t_0) = sum_s sum_("e odd") max lr(0, alpha_s\/p^e - "cap"_U (s, e)) - "dl"$，$"cap"_U (s, e) = "fillG"("partner"(p, s, e)) + c_G$，$alpha_s = a_s - 2 c_G$，而 $"g"_U = gamma_p sum_s alpha_s - sum_s sum_("e odd") min(alpha_s\/p^e, "cap"_U) - "dl"$。这里 $"VV"$ 是被服务的 Frobenius 轨道之集，`reps` 是轨道代表元之集。
]

#lean("gainP", "Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean")
#lean("askG", "Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean")

常数在 `FamP.fixed` 中固定：$"dl"_1 = 5$、$"dl"_2 = 4$、$"Pr"_1 = 1$、$"Cr" = 1$。#inferred[于是 gainP 是 ask 减去簿记损失。]`askP` 与 `askG` 都对奇数 $e$ 求和。`FirstPrimeNeSecondPrime.lean` 中声明的全局 ask 对一切满足 $i dot.op "Frob"_p in.not Phi$ 的 $i <= N$ 求和，这正是惯性素数处奇指数之集。

#thm("5.19", "局部增益律")[
  设 $w$ 是剩余特征 $p eq.not T$、$p in.not {g_0, g_1}$ 的位，并设 $"sg"(u, w) = sum_j lr("gainD"_j (w) + F_j (w) - E_(u, j) (w))$。假设配对整除性 `PairInt`、`ErrDefs`、绑定 `Ties9`、被服务格的定义、$w$ 处的局部包含 $N_u subset M_"ram"$，以及假设 `Conclusion1`。则对每个 $phi in N_u$ 与参考格 $tilde(M)(mu_w) ∩ V_0 (mu_w)$ 中的每个 $F$，存在 $y in "LL"$ 等于周期 $"perCol"(u, mu_w, j_N phi, F)$，使得
  $ y = 0 quad quad "或" quad quad "ur"(w, "sg"(u, w)) <= v_w (y). $

  此外，声明的增益被服务增益控制：$"L.gainD"_j (w) <= "gainS"(p, j)$（`gainD_le_gainS`），其中 $p$ 是 $w$ 的剩余特征。这里 $"gainS"(p, j) = "gainP"(p, j)$ 若（$p$ 是 residue-class-zero 或 `IsSg`）且 $p$ 不是例外的（`Exc`）也不在类 `IsCs` 中，否则 $"gainS"(p, j) = 0$。整体上，$N_u$ 是 $M_u$ 经理想 $I_u = product_w p_w^floor("s_g")$ 的扭曲（`shiftIdeal_sgFl`），由 #ref[定理 5.15] 这给出 `SlopesN` 中使用的斜率增益 $"Ga" + "Fo" - "Ee"$。
]

#lean("off_level_bound", "Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean")
#lean("gainD_le_gainS", "Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean")
#lean("shiftIdeal_sgFl", "Formalism/LocalToGlobal/GroupLattices/JointServices/ShiftIdealSgFl.lean")

#proof(uses: ref[定义 5.18、定理 5.15 与引理 5.16])[
  有两步。第一，`Conclusion1`（同一文件，第 97 行）说：对 Hecke 生成的格 $N^P$ 中的 $x$，列赋值至少是 `totS`。然后 `period_ge` 乘以配对整除性，`GainLeP` 把计算出的增益 lowers 到声明的增益。第二，`LatticeGrowthAtPlace` 陈述：对 $F in N^P$，$F in p^(sum_j "gainP"_j + "low") dot.op ("chain lattice")$。子格 $N^P$ 由 Hecke 词 $y_v m$ 作用于 $p^ceil(S_v) tilde(M)$ 生成，再被 $p^ceil(tau_P) tilde(M)$ 与 $V_"ram"$ 截断。其长度在另一方向被 $v_"unit" dot.op d dot.op (tau_P + "io"_P)$ 控制住，这就是整体公式使用 $"gain" - tau$ 的原因。`Conclusion1` 在 `baseChange_preserves_unitary_of` 中按情形构造：被服务轨道（`kernel_valuation_served`）、判别素数（`LossAtDiscriminant`）、平凡 Frobenius（`MediumInertPrimeLengthBound`）、否则 `OrbitsWithoutOperator`。被服务情形依赖于 `TupleLatticeValuation`，后者来自 `unitBoundAtTwistedPlaces`，对 $N^P$ 的生成元做张量归纳。
]

#caution("5.20")[
  `Formalism/SharpRestriction/GrowthBounds` 下的文件名 `WeilJacquetShalikaLaw.lean` 有误导性。它包含关于 $N^P$、Hecke 词与 `gainP` 的格赋值命题，没有任何 Whittaker 模型。`Development/WeilBound/CoreStatements/PublishedTheorems/SmoothVectorEstimates` 下同名文件确实带有 Whittaker 内容，但不用于增益。同样，`IsResidueClassZero` 只表示“在 $QQ(sqrt(-d))$ 中惯性，且 $sqrt(-q)$ 上的 Frobenius 符号为 $-1$”。
]

#prop("5.21", "指数 a/p^e 从何而来")[
  #inferred[奇数 $e$ 的因子 $p^(-e)$ 来自 $W(F_p)$ 上一个高为 2 的形式群。]在 Lean（`FormalGroupSystem.lean`）中定义了级数 $"logF" = sum_(j >= 0) p^(-j) X^(p^(2 j))$，故对数为
  $ "logF" (X) = sum_(j >= 0) p^(-j) X^(p^(2 j)), $
  #inferred[其 CM 作用是 $sigma^2$。]theta 核写作 $"Th" = exp(-P h) dot.op U$，其中 $P h = sum_e b_e (x_e, y_e)$，是双加性级数，满足 $b_e (alpha x, y) tilde.op b_e (x, sigma(alpha) y)$（$alpha$ 被 $sigma^2$ 固定）。一个 Dwork 型整除性判据（`DworkLemma`、`InClass`）表明单项式的系数带 $sum p^(-i)$ 因子：$"coeff"(h^((g_i)))$，$h = sum_s u_s x_s x_(s + 1)$。这在 `FormalGroupSystem` 中编码。定理 `stmt_proved` 是 `Conclusion2`（来自 `packet_statements_hold`）连同表示命题（`relative_presentation_of_d7`）；它本身不是上文的形式群命题。
]

#lean("FormalGroupSystem.Pf.stmt_proved", "Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean")

#proof(uses: ref[定义 5.18])[
  定理形状为 $"admitted" arrow.r "Conclusion2"$，由 `packet_statements_hold` 从 `prv_and_kernel_commutation_up_to_units_of_rests` 证明。所需的“rests”是：`theta_kernel_expansion`（使用 `restBeta`，它表明 $b_e$ 整除地是一个 Honda 律，以及 `restGc`）、`expansions_multiply`、`auxU_of_firstTheoremPlaceBound` 与 `restEnt_of`。最后一步是 `lift_bound_of_integrality`，带天花板算术的张量归纳，把整除性穿过 Hecke 链。#inferred[高为 2 正是只有奇数 $e$ 有贡献的原因。]和为 $sum_("e odd") p^(-e) = p\/(p^2 - 1) = gamma_p$（`GammaIdentity`），总赋值被 $"S"_("vv") <= m gamma_p sum_s alpha_s$ 控制（`Conclusion5`）。#inferred[读法“单项式 $x_s^(a_s)$ 至多能吸收约 $a_s\/p^e$ 个因子，位置 $s + e$ 的伙伴变量给出容量，增益即超额”是我们对定义的解读；组合引理在 `InClassOfExp` 与 `SxMuAltInt` 中，我们没有读。]
]

#rem("5.22", "兑现局部系统")[
  假设 `LocalSystemCompletion` 说：对每个词 $u$ 与位 $w$，实局部数据给出一个形式群系统，带全部 13 个容许条件 $"adm"_1, dot.op, "adm"_13$，外加低项的下界。它在库中被兑现。定理 `system_of_local_data` 把 `LocalDataSystem` 变成 `LocalSystemCompletion`；`link_of_local_closed` 由局部假设 `Loc` 给出族命题 `LinkG`；而 `loc_proved : Loc` 由判据 `criterion_restricted_of_closed` 与 `TraceSpectra.stmtE` 证明。
]

#lean("system_of_local_data", "Formalism/LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean")
#lean("loc_proved", "Formalism/LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean")

定义位于 `Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean`，第 1620 行。

== 主项：Chowla–Selberg

`mainT` 与除子不等式中的几何常数涉及 `logOm`——宿主域上 CM 阿贝尔簇的平均对数周期。

#thm("5.23", "Chowla–Selberg 周期")[
  设 $E$ 是带判别式 $d$ 的宿主数据 $H$ 的 CM 域，$chi$ 是模 $d$ 的 Kronecker 特征，$rho^2 = -d$。则存在 CM 椭圆曲线 $Z$（`Curve0`(H, ρ)）与实数 $x$，使 $Z.z eq.not 0$、$Z.C$ 有周期 $x$，且
  $ x = gamma + log ((2 pi)/sqrt(d)) - L'\/L (1, chi). $
  于是，对各嵌入取平均，
  $ "logOmVal"(D) = gamma + log ((2 pi)/"rd"_E) - L'\/L (1, chi_(-d)), $
  且 `MeanPeriod` 成立：阿贝尔簇的 log CM 周期对共轭的平均等于 `logOmVal`。
]

#lean("GlobalTheory.T.chowla_selberg_period", "Development/AutomorphicSpectrum/Proofs/GeometryProofs/ChowlaSelbergPeriodStatement.lean")
#lean("logOmVal_eq", "Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/MeanPeriodLogarithms.lean")
#lean("meanPeriod", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogPeriodChowlaSelberg.lean")

#proof(uses: ref[定理 5.13])[
  第一条命题是 `exists_curve0_hasPeriod`（文件 `ChowlaSelbergPeriod.lean`）。它依赖于 `GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg` 中约五十个文件、约 5500 行。Kronecker 极限公式被证明为 `KroneckerLimit.proof`（文件 `PKroneckerLimit.lean`）：
  $ lim_(s arrow.r 1) lr(sum abs(m tau + n)^(-2 s) ("Im" tau)^s - 1/(s - 1)) = 2 pi lr(gamma - log 2 - log(sqrt("Im" tau) abs(eta)^2)). $
  它由 `KroneckerSplit`、`PowerIntegral`、`ShiftedSumIntegral`、`CotangentSum`、`LogEta` 与 `GammaZetaLimit` 经控制收敛得到。`PhTau.full` 给出 $log "period"(L_tau) = log(4 pi "Im" tau abs(eta)^4)$，`ClassMean.full` 对 Epstein zeta 取类群平均，其中 $zeta_K = zeta dot.op L(dot.op, chi)$。从一条曲线到域 $E$ 的步骤使用 `mean_log_period` 与 $E$ 的 CM 型由 $QQ(sqrt(-d))$ 诱导这一事实（`InducedType.induced_type`），于是只需要椭圆曲线情形，且不使用 Colmez 定理。`two_log_brN` 把 $E$ 的判别式换成根判别式 $"rd"_E$。
]

#caution("5.24")[
  Lean 定理是对 `Curve0`（由宿主数据附带的阶给出 CM 的椭圆曲线）陈述的，且在类平均一步中要求素判别式 $d "equiv" 3 ("mod" 4)$。它不是任意 CM 域的完整 Chowla–Selberg 公式。
]

Hodge 一侧使用同一个常数。平坦 CM 线的 Hodge 次数是 $-(p - q)\/2 dot.op "logOm"$，误差为 $C_c q' (log "rd" + L_chi)$（`FlatVal.flat_val_alt`）。所以 `logOm` 也是 CM 点处的 Hodge 次数输入。

`MAIN` 中的另一项是 $"ph"(a) = a log a - a$。它经由 `ph` 与钩长乘积之 log 的比较，控制权 $a$ 的 Fock 向量的对数 Gram 行列式（`RowsHook`、`Numbers.logHook`）。#inferred[这就是把 Stirling 公式用于钩长乘积。]

== 从除子不等式到 ASK ≤ MAIN + 误差

#prop("5.25", "除子不等式")[
  在 `ThmConcl` 的记号下：对带权 $a_t$ 的有限位指标集 $"TT"$，
  $ mu_C + h_u - 2 F_o <= sum_(t in "TT") lr(m "ph"(a_t) - a_t "logOm" - a_t log T) + (50 C_0 + 10) lr(abs("TT") a L_a + m (B_0 + N_c) x^(c"Div" epsilon)). $
]

#lean("divisor_inequality", "Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TheoremDivIneq.lean")
#lean("ThmConcl", "Formalism/SizeWindowBrackets/SBrDiv.lean")

#proof(uses: ref[定理 5.13、5.15 与 5.23])[
  证明很短：`divisor_inequality_assembly`（44 行）把误差项 $abs(p q - k) abs(w) abs("logOm")$ 与 ph-和配对，`error_absorption`（205 行）把所有常数吸收进 $50 C_0 + 10$。全部几何都坐在 `TheoremDivIneq` 的八条假设 $h_1, dot.op, h_8$ 中：Fock 对数余体积界 $"logK"_(j, s) <= sum_tau (sum_i "ph"(nu_(j, tau, i)) - (sum_i nu_(j, tau, i)) "logOm"_tau) + dots.h.c$、平坦线的 Hodge 次数、Hilbert–Samuel 斜率界（$mu_U >= -2(C_1 L_0 u_a + b\/4)$）、平坦扭曲、下降与好的切（$mu_G - P_9 <= mu(M_j)$）。这正是 #ref[定理 5.13] 的链条再次进入。打包成平均斜率数据的是 `construct_divisibility_of_conclusion`（一个 `nlinarith` 装配）。
]

文件 `DivIneqTopAnchorU.lean`（616 行）只有命题陈述：约十条 `def ... : Prop`，没有定理。无论其名字暗示什么，它不是除子不等式的证明。

在平均数据 `Data` 的层面（字段 $mu_"CC", mu_M, mu_N, "Ga", "Fo", "Ee", h, T, "ASK"$），最终论证使用以下条件，全部定义于 `Formalism/RankGapBounds/MeanBoundSecondForm.lean`：

- `DIV`：$mu_"CC" + h - "Fo" <= sum_t lr(m("ph"(a_t) - a_t "logOm") - a_t log T) + c_"Div" n_T a L_a + c_"Div" m (B_0 + N_c) x^(c"Div" epsilon)$，其中 $"logOm" = gamma + log(pi\/v) - L'\/L$。
- `Count`：$sum_j 1/f sum_rho log(w_(j rho) v\/pi) + m "lg" - c_"Count" (L + m^2 L\/k) - 2 log Gamma\/(f k) <= log T <= c_"Count" m L$。
- `EComp`：$abs("Ee"_j - "sumA" dot.op "lg") <= c_E B_0$。
- `SlopesN`：$mu_N <= mu_(max, M) + "Ga" + "Fo" - "Ee" + c_("S1") m B_0$ 且 $mu_M + "Ga" + "Fo" - "Ee" - "Lo" <= mu_N$。
- `Losses`：$"umean"("ASK" - "Ga") <= "LoP"$，来自 `SplitLe`（#ref[引理 5.16]）。
- `SlopeIneq`：一个 Harder–Narasimhan 比较，$s - log abs(W) - (1 - delta)^(-1) (4 u_F log(1 + H\/u_F) + (eta + 4 sqrt(e)) H) <= mu_"CC"$。

等同 `Ident` 置 $"Dd.gam" = gamma$（Euler–Mascheroni 常数）、$"Dd.LpL" = Re ell(chi_C)$、$"Dd.ASK"(u^0) = sum_(t in "TT") sum_(j < m) "ASK"(D, N, a_t, t, w_(u^0, j))$。`LdIdentD` 对格一侧给出同样的东西：$"Ga" = (F_m u^0)."Ga"$。

#lem("5.26", "相消到 Count 与 EComp 误差")[
  置 $"logOm" = gamma + log(pi\/v) - L'\/L$，设 $"lg"$ 是 `Count` 中的常数。令 $"ErrCount" = c_"Count" (L + m^2 L\/k) + 2 log Gamma\/(f k)$ 为 `Count` 下界中的误差，令 $"ErrE" = c_E B_0$ 为 `EComp` 的误差（对 $j$ 求和）。则，对 $m$ 个提升与位 $t$ 求和，
  $ sum_t lr(m "ph"(a_t) - m a_t "logOm" - a_t log T) + "Ee" <= "Main" + "ErrCount" + "ErrE", $
  其中 `Main` 对每个 $j$ 的求和项是 $a_t lr(log a_t - 1 - gamma + L'\/L - 1/f sum_rho log w_(j rho))$。
]

#proof(uses: ref[命题 5.25 与定理 5.23])[
  代入 `Count` 给出的 $log T$ 下界。$log pi$ 与 $log v$ 在 $a m log pi$（来自 `logOm`）与 $log T$ 中的 $m log v - m log pi$ 之间相消。项 $"lg"$ 在 `Ee` 与 `Count` 之间相消，但只到 `EComp` 为止：`Ee` 是 `Ee_j` 对 $j$ 的和，每个与 $"sumA" dot.op "lg"$ 相差 $c_E B_0$ 以内，所以它约为 $m dot.op "sumA" dot.op "lg"$，而非单项。留下的是 $gamma$ 与 $L'\/L (1, chi_(-d))$，它们只来自 `logOm`。这是关于定义的代数。#inferred[我们手工核对过，未在 Lean 中逐行核对。]簿记位于 `ErrX` 与 `MeanBoundSecondForm`（`Formalism/RankGapBounds/MeanBoundSecondForm.lean`），以及 `each_unit_bound_statement`（`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`）中。
]

#lean("each_unit_bound_statement", "Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean")

`ch_top_main_eq`（`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean`）证明的是一个不同的、纯形式的事实：在等同 `IdentU` 下，$"Dd.Main"(u^0) = sum_(t in "TT") sum_(j < m) Re "MAIN"(ell, a_t, w_(u^0, j))$。它不做上面的相消。

$log T$ 的下界来自一个素数窗口：`LevelWindow` 说 $X Gamma^(-2\/(f k)) <= T <= X Gamma^(-2\/(f k)) (1 + 1\/(f k))$，而 `logT_bounds` 与 `proposition_to_count_general` 把它变成 `Count`。额外的输入 `BoundedBy'`（$log X$ 的下界）我们未追踪。

#thm("5.27", "素数计数界")[
  这里 $n = abs(H)$、$n_T = abs("TT")$、$a = "Dd".a$ 满足 $x b <= a$，而 $k$ 是权预算，如 #ref[第 3 节]。在平均界包（族数据 `IdentU`、`SizeData2`、`ErrWindows`、`BNBoundsU`、`LargeX`）的假设下，对每个 $u in U_0$，
  $ "gapA"(u) = sum_(t in "TT") sum_(j < m) lr("ASK"(D, N, a_t, t, w_(u, j)) - Re "MAIN"(ell, a_t, w_(u, j))) <= x^(C_"Err" epsilon) dot.op "errorBracketSizeWindows", $
  其中误差括号是 $n_T a (1 + m^2\/k) + m(2 n m b x^epsilon + dots.h.c)$，且
  $ "ASK"(D, N, a, t, w) = sum_(p <= N, "IsInert"(p)) 2 log p dot.op "askP"(p) + log d dot.op "askD", $
  $ "MAIN" = a lr(log a - 1 - gamma + ell(chi_C) - 1/abs(Phi) sum_(rho in Phi) log w_rho). $
  等价地，平均版 `MeanBoundSecondForm` 读作 $"umean"("ASK") <= "umean"("Main") + "ErrX"$。
]

#lean("ch_top", "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean")
#lean("MeanBoundSecondForm", "Formalism/RankGapBounds/MeanBoundSecondForm.lean")

#proof(uses: ref[定理 5.13、5.15、5.19 与 5.23，命题 5.25，引理 5.26])[
  链条是：`IndefSide.l3`（逐提升余体积界，#ref[定理 5.13]）与局部指标界 `ON`；然后 `IndefCore.divCore`——其证明是一小段 `linarith`——给出
  $ mu_"CC" + "htMap"(B_u) <= X + 3 d e (X + h h + 28 l a) + 28 l a + 1/n_(P_1) sum_v log p U_(D, v)^2 - sum_j l_(6, j), $
  其中 $X = sum_j l_(3, j) + 2 sum_j sum_(y in T_w) frak(l)_w (y) F_0 + L_G + sum_j (E_1^j + E_2^j) + E_3$。接着是 `divisor_inequality`（#ref[命题 5.25]），它供给 `DIV`。然后 `SlopesN`、`Count` 与 `EComp` 给出 $"Ga" <= "Main"'' - mu_M + "Ee" + "Lo" + "err"$（项 `Fo` 相消）。经 #ref[引理 5.26]，$"Main"''$ 在 `Count` 与 `EComp` 误差内变成 `Main`，而这两个误差是 `ErrX` 的一部分。`SplitEq` 与 `LdIdentD`（#ref[引理 5.16]）把 `Ga` 换成 `ASK`，相差 `Losses` 中的损失。`Ident` 随后把 `Data.Main` 与对提升求和的 `MAIN` 等同，`ch_top` 陈述结果。
]

#rem("5.28", "误差的尺寸")[
  重数 $m$ 是提升的个数，量级为 $sqrt(x delta_1)$，$delta_1 = x^(-epsilon\/8)$。每个提升以绝对单位损失 $O(b x^(O(epsilon)))$，因为 $b <= "unitE" <= x^A b$（`SizeAt`）且 $B_0 <= 2 abs(H) m b x^epsilon$（`BNBoundsU`）。除以正规化 $n_T m b n_(T_2) \/ (2 n)$ 后，幸存的两项尺寸为 $x\/m$ 与 $m x^(O(epsilon))$（#ref[命题 4.7]）。它们在 $m tilde.op sqrt(x)$ 处平衡，总误差量级为 $x^(1/2 + O(epsilon))$。这就是指数 $1\/2$ 的来源。我们没有手工重新推导精确的正规化 $a = x b$、$m^2 tilde.op x^(1 - epsilon\/8)$。
]

#rem("5.29", "未保留的特征")[
  保留集之外特征的和 `SigA` 不会被消掉。`sigA_le` 用 `PairGood.bounds` 把它控制为 $abs(Psi_A) x^(1/2 + epsilon) = 4^o x^(1/2 + epsilon)$，而 `core_gm` 把它吸收进指数损失。这属于宿主域那一章。
]

== 本章传递什么

- #ref[定理 5.13]：每个提升的 $"lcv"\/D$ 的上界，主部为 `mainT`，误差为 $C dot.op "unitE"$（$C >= C_0$），其中 $b <= "unitE" <= x^A b$。
- #ref[定理 5.15]：把该界转化为局部指标加权和之界的恒等式。
- #ref[定理 5.19]：惯性素数处这些局部指标由 `gainP` 给出的下界，后者由对奇数 $e$ 的 $max(0, a\/p^e - "cap")$ 之和构造。
- #ref[定理 5.23]：阿基米德常数与 $gamma + log(2 pi\/sqrt(d)) - L'\/L (1, chi_(-d))$ 的等同。
- #ref[定理 5.27]：不等式 $"ASK" <= "MAIN" + "error"$，传递给解析各章以迈出 $"Gm"(x) <= x^(1/2 + C epsilon)$ 的一步，进而到无零点区域（#ref[定理 2.8]）。

从其他各章使用的输入是：宿主域（#ref[定理 3.6] 与 #ref[定理 3.14]）、塔及其非零性（#ref[定义 4.2] 与 #ref[定理 4.24]），以及 #ref[第 7 节] 列出的经典工具。
