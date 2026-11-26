// ch6.typ —— 第 6 章 伽罗瓦一侧：伽罗瓦表示与 Vandiver 界
#import "lib.typ": *
#pagebreak(weak: true)

= 伽罗瓦一侧：伽罗瓦表示与 Vandiver 界

本章证明零点检测引擎从伽罗瓦理论需要的两件事。第一，阿贝尔 CM 域上 Tate–Shafarevich 群的尺寸界。引擎在其误差项中为这个界付出代价，所以与 $exp(x^epsilon)$ 相比它必须很小。我们称之为 Vandiver 界（Lean 名 `VWin`）。第二，附着于 CM 域上极化尖点形式的伽罗瓦表示的存在性（Lean 名 `Row0b`）。Vandiver 界需要第二件事，因为它是通过证明伽罗瓦形变环的所有点都是自守的来证明的。

#ref[6.1 节] 陈述该界并把它归约为一个分情形。#ref[6.2 节] 给出自守性输入。#ref[6.3 节] 证明伽罗瓦表示的存在性。#ref[6.4 节] 陈述所使用的弱局部 Langlands 片段。凡 Lean 命题弱于已发表定理之处，都有 caution 说明。

== Vandiver 型界

固定数域 $F$、素数 $ell$ 与代数闭包 $Omega$。Lean 把一个有限位集 $S$（含 $ell$ 上方的位）、分解群，以及 $G_S$ 的分圆特征 $chi$ 打包成对象 `LData F Ω ℓ`。

#defn("6.1", "Sha 长度")[
  对 $D$ = `LData` 与 $e in ZZ$，令 $QQ_ell \/ ZZ_ell (-e)$ 为 $chi^(-e)$-扭曲。置
  $ "Ш"(D, e) = "ker" lr(H^1 (G_S, QQ_ell\/ZZ_ell (-e)) arrow.r product_(v in S) H^1 (G_v, QQ_ell\/ZZ_ell (-e))), $
  $ "shaLen"(D, e) = "length"_(ZZ_ell) "Ш"(D, e) in NN union {oo}. $
]

#lean("Formalism.GaloisCohomology.shaLen", "Formalism/GaloisCohomology/Statement.lean")

Lean 谓词 `PTShaAt` 说：当 $ell$ 为奇数或 $F$ 无实位时，这个长度等于 $Ш^2 subset H^2 (G_S, ZZ_ell (e + 1))$ 的长度。

#lean("Formalism.GaloisCohomology.PTShaAt", "Formalism/GaloisCohomology/Statement.lean")

#defn("6.2", [χ-域，窗口对])[
  设 $psi$ 为本原狄利克雷特征。称域 $E$ 是 $(psi, e, q, d)$ 的 $chi$-域，若存在被 $2^(e + 2)$、$psi$ 的导子、$q$ 与 $d$ 整除的 $N$，以及嵌入 $E arrow.r.hook QQ(zeta_N)$，使得 $tau_a : zeta_N arrow.bar zeta_N^a$ 保持 $E$ 当且仅当
  $ a equiv plus.minus 1 (2^(e + 2)), quad quad psi(a) = 1, quad quad lr((a)/q) = 1, quad quad lr((a)/d) = 1. $
]

#lean("UpperTheory.Top.IsChiField", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")

称数对 $(q, d)$ 是 $(epsilon, Y)$ 的窗口对（`WinPair`），若 $q$、$d$ 为素数，$q equiv 3 (8)$、$d equiv 7 (16)$，$1/2 Y^(epsilon\/5) < log q <= Y^(epsilon\/5)$，$1/2 Y^(epsilon\/5) log^2 Y < log d <= Y^(epsilon\/5) log^2 Y$，$q bar.v d + 1$，且每个 $<= Y^(epsilon\/5)$ 的奇素数整除 $d + 1$。

#lean("UpperTheory.Top.WinPair", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")

于是 $chi$-域在 $QQ$ 上是阿贝尔的。窗口对的存在性不在此处证明；它是 #ref[定理 3.14]。

#defn("6.3", "Vandiver 谓词")[
  对数域 $E$、$t in NN$ 与 $B in RR$，$"VVle"(E, t, B)$ 说：对每个代数闭包 $Omega$ 与每族局部数据 $(D_ell)_ell$，
  (i) 对一切素数 $ell$ 与 $0 < e < t$ 有 $"shaLen"(D_ell, e) < oo$；
  (ii) 对每个由素数组成的有限集 $S$，$sum_(ell in S) log ell sum_(1 <= e < t) "shaLen"(D_ell, e) <= B$。
]

#lean("UpperTheory.Top.VVle", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")

集合 $S$ 遍历素数的所有有限集，所以 $ell = 2$ 包括在内。和数的是长度，故 $B$ 控制 $log abs(Ш)$ 而非 $abs(Ш)$。该谓词对 $t$ 与 $B$ 单调（`VVle.mono`）。

#thm("6.4", "Vandiver 窗口界")[
  设 $psi$ 为本原狄利克雷特征，$0 < epsilon < 1\/52$，且 $e : RR arrow.r NN$ 满足对 $x >= 1$ 有 $x^(2 + 8 epsilon) <= 2^(e(x)) <= 2 x^(2 + 8 epsilon)$。存在 $J >= 1$ 与 $X_0$，使得对一切 $X >= X_0$ 与一切满足 `WinPair`(ε, X^{1/J}, q, d) 的 $q$、$d$，存在 $Y$ 满足 $X^(1\/J) <= Y$、$Y^2 <= X$，使得对每个 $x in [Y, Y^2]$ 与每个 $(psi, e(x), q, d)$ 的 $chi$-域 $E$，
  $ "VVle" lr(E, floor(x^401), sqrt(exp(x^epsilon))). $
]

在 Lean 中：`VWin = ∀ψ, VWinAt ψ 401`。

#lean("UpperTheory.Top.VWin", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")
#lean("UpperTheory.Top.VWinAt", "Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean")

这个奇怪的形状（存在量词 $J$、$X_0$、$Y$）来自证明：选取 $[Y, Y^2]$ 是为了避开有限多个例外尺度。

#rem("6.5", "为什么这个尺寸就够了")[
  引擎的主项约为 $m dot.op b$，其中 $b = exp(x^epsilon)$ 且 $m approx sqrt(x)$ 个提升。Sha 项作为 $"vvTerm" D ell = log ell sum_e "shaLen"$ 进入（`Formalism/SharpRestriction/GlobalTheoremInputs.lean`）；引理 `vvRecord` 把 `VVle` 变成对 $sum' "vvTerm"$ 的界。由 `vvRecord`，$sum' "vvTerm" <= B = sqrt(exp(x^epsilon))$，而这个和以加法方式进入 `LinkN_at`（`Formalism/SharpRestriction/GlobalTheoremInputs.lean`），与其他误差项并列。那些误差项是 $e^(x^(4 epsilon\/5)) log 2$、$K e^(8 x^(epsilon\/4))$ 与 $u^C + C e^(x^(4 epsilon\/5))$，其中 $log u <= 2 x^(epsilon\/4)$。引理 `error_terms_le_sqrt_exp_rpow`（`CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean`）表明这些合起来对大 $x$ 至多是 $sqrt(exp(x^epsilon))$。窗口数据使用 $floor(x^400)$，但输入 `VWinAt` 使用 401（`CharacterBoxes/WinPairs.lean`、`CharacterBoxes/TwistForm.lean`）。多出的 1 为 `winPairs` 中的重标度 $x = k x'$ 买单，后者需要 $k^400 <= x'$。`LemmaK` 的平凡界 $exp((2 e n)^C log 2^D)$ 大得多，所以该命题有实质内容。下游使用是 #ref[定理 5.27]。
]

#heading(numbering: none, outlined: false)[定理 6.4 的证明]

Lean 中的顶层接线是

`vwin_of_row → automorphic_window_of_inputs → v_window_of_literal_automorphy_n` \
`→ vwin_of_hypotheses_H_E_alt → vwin_of_counts.`

#lean("UpperTheory.One.vwin_of_row", "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean")
#lean("UpperTheory.V.HV.vwin_of_counts", "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean")

#proof(uses: ref[定理 6.13、6.18 与命题 6.6 到 6.8、6.10、6.11])[
  所携带的输入。定理 `vwin_of_row` 表明：若 `Row0b (fun h rc => IsRecT h rc)` 成立，则 `VWin` 成立。它把一个结构 `OpenImageCondition`（其唯一字段是 `Row0b`）连同 `baseChangeN`（到 CM 域上 isobaric 和的基变换，在库中证明）一起喂入 `LiteratureAutomorphyHypothesis`。该结构有 15 个字段；14 个由具名定理填满（尖点形式衰减、Harish-Chandra 有限性、Jacquet–Shalika、Gelfand–Kazhdan、Clozel 纯性、Artin 互反律、Berger 定理等等），而其中一个字段 `gal` 就是 `Row0b`。

  然后 `published_hypotheses_from_patching_alt` 由这些与迹公式下降 `descWeak` 构造出大结构 `HypothesesH'`。没有发现任何字段被 `True` 兑现。`Row0b` 本身是 #ref[定理 6.18]，是一个定理。

  分情形。最后 `vwin_of_counts` 按 $ell$ 与奇偶性分裂。下面三部分由 #ref[命题 6.6] 与 #ref[注 6.5] 的误差引理结合。
]

#prop("6.6", "按素数与奇偶性分裂")[
  设 $E$ 是 CM 域。假设 (a) `VVat₂ E t B₂`——#ref[定义 6.3] 的界在 $ell = 2$ 单独时；(b) `VVminusLe E t B₋`——对奇数 $ell$ 只用复共轭在 Sha 上的 $(-1)$-特征空间的界；(c) `VVplusLe E t B₊`——对 $(+1)$-特征空间同样。则 $"VVle" E t (B_2 log 2 + B_- + B_+)$。
]

#lean("UpperTheory.V.vvle_of_parts", "Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean")

#proof[
  对奇数 $ell$，$"shaLen"$ 等于 $(+1)$-特征空间长度与 $(-1)$-特征空间长度之和（`shaLen_eq_add`）；对 $ell$ 求和。
]

三个输入是：(b) 用 `ThmBcFree`，(c) 用 `ThmHV`，(a) 连同坏素数用 `ThmBab`。

#prop("6.7", "奇偶性，伯努利界")[
  设 $E$ 是 $QQ$ 上阿贝尔 CM，$ell$ 为奇数且 $ell divides.not [E : QQ]$，$psi : "Gal"(E\/QQ) arrow.r cal(O)^times$ 是取值于 $QQ_ell$ 的有限扩域之整数中的特征，$e >= 1$，且 $chi_psi (-1) = (-1)^(e + 1)$。则 Sha 的 $psi$-部分的长度至多是附着于 $psi$ 与 $e + 1$ 的一个广义伯努利数的 $ell$-进赋值。在 Lean 中：`PsiBound`，右边为 `addVal O (alN (e+1) (chiOf ρ ψ))`。
]

#lean("UpperTheory.V.Odd.PsiBound", "Development/AutomorphicArithmetic/AutomorphicVarieties/OddResidueBounds/ZeroMemUnrHom.lean")

由此 `ThmBcFree`：存在 $C$ 使 $"VVminusLe" E t ("minusBound" C dots.h.c)$——一个关于 $t$、$[E : QQ]$ 与导子的多项式界。

#lean("UpperTheory.V.ThmBcFree", "Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean")

#proof[
  `PsiBound` 由 Poitou–Tate 对偶与非分歧正交性证明（`ML.iv`）。它给出 `StickBound`，进而 `ThmBcFree`。不使用自守性。#inferred[给这个界贴上 Mazur–Wiles 或 Stickelberger 型的名字是我们的归类。]
]

#prop("6.8", "一般计数")[
  对每个本原 $psi$，存在 $C$ 与素数 $r_1$、$r_2$ 使得下述成立。取每个带特征 $psi$（#ref[定义 3.1]）且 $r_1, r_2 < min(q_1, d)$ 的宿主 $h$、每个满足 `h.Big t`（$2t + 1 < q_1$、$d$ 与 $h$ 在 $q_1$、$d$ 之下的有限多个辅助素数）的 $t$、一切 $0 < e < t$，以及每个由奇素数 $ell in.not B_psi$（$ell - 1 divides.not 2e$）（`CaseI`）组成的有限集 $L$。则 Sha 长度有限，且
  $ sum_(ell in L) log ell sum_(psi') V_n (ell, e, psi') <= (N t)^C, $
  其中 $V_n$ 是 $psi'$-扭曲的 Sha 长度，$N$ 是宿主的水平。这就是 `CountI`。
]

#lean("UpperTheory.V.HV.CountI", "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean")

#proof[
  输入是 `CorG`：对辅助素数 $p eq.not p'$，和至多是
  $ 4 c_5 phi("ind") abs("disc" K)^5 N^18 e^7 (log p + log p'), $
  其中 $K$ 是辅助虚二次域。它由 `PropGK` 推出：对 $e$、$N$、$H$、$p$，存在非零整数 $N N$ 使
  $ log abs(N N) <= c_5 phi("ind" H) (N (e + 1))^A log p, $
  且对每个 $ell eq.not p$，轨道和满足 $sum_psi V_n <= 2 v_ell (N N)$。
]

#lean("UpperTheory.V.U3.PropGK", "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean")

由于 $sum ell log ell dot.op v_ell (N N) <= log abs(N N)$，对全体素数的和保持多项式。`CountI` 按核把特征分组并吸收常数。$v_ell (N N)$ 的界来自 #ref[命题 6.9]。[用到 #ref[命题 6.9、定理 6.13 与定义 3.1]]

#prop("6.9", "抽象计数")[
  设 $cal(O)$ 是 $QQ_ell$ 的有限扩域的整数环，$F$ 是-profinite 群 $Gamma$ 的三维酉形变的局部条件标架（带条件 `Ok`、`LocVan`、`Count`、`VanE`、`Cl1`、`Xpp`），$u$ 是万有形变，$"wpart"(cal(O), u, 0)$ 在 $cal(O)$ 上有限。假设 `LemmaM`、`LemmaM'`，且每个 I 型点都是 `Good` 的，每个特征零的 `Good` 点都是刚性的、其 $phi$ 处的迹不同于 Eisenstein 迹。则存在两两不同构的特征零 I 型点 $r_1, dot.op, r_n$ 与 $V in NN$，使 $"shaLen"(a) <= V$ 对一切非零 $a in cal(O)$ 成立，且
  $ V <= 2 e(cal(O)) sum_(i = 1)^n v_ell lr(tr r_i (phi) - tr r_0 (phi)). $
]

#lean("UpperTheory.V.UnitaryThreeInertia.abstract_count", "Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeDeformations/AbstractCount.lean")

#proof[
  `LemmaM` 是分次交换代数中的定理：对带点 $x : A arrow.r cal(O)$ 的分次 $cal(O)$-代数 $A$ 与满足五个正则性条件的表示，余切长度至多 $2 sum_(xi in T) v(xi(a))$，其中 $T$ 是覆盖该理想的 $QQ$-点的任意有限集。
]

#lean("UpperTheory.V.Alg.LemmaM", "Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean")

`LemmaM'` 用余切长度控制导子模的长度。证明构造万有环的一个适配权表示，把 `Sha` 等同于一个导子模，并对 $a = tr u(phi) - tr r_0 (phi)$ 应用 `LemmaM`。诸点 $r_i$ 由 #ref[定理 6.13] 是自守的；其迹差是非零的、尺寸受控的代数整数，故其赋值被 $log$-范数对 $log ell$ 控制。#inferred[最后一句正是 `PropGK` 收尾的方式；我们读了它的陈述与用法，而非整个证明。]

#prop("6.10", "特殊素数")[
  对一般情形之外（即 $ell - 1 bar.v 2e$）的奇数 $ell in.not B_psi$：计数 `CountZ`（平凡特征）、`CountII` 与 `CountIII`（秩 4 辛）成立。`SumOut`（`HeightAndVanishing/LayerLe.lean`、`HeightAndVanishing/SumOut.lean`）仅由 `CountI`、`CountZ`、`CountII`、`CountIII` 导出。它给出界 $M^(C_1 + 3K + 4)$，其中 $M = N t$、$K = max(C_Z, C_2, C_3)$（证明把 $t(M^(C_1) + 2 M dot.op M^(3K))$ 控制为 $M^(C_1 + 3K + 4)$）。计数 `CountV`（秩 3 酉，$ell in B_psi$、$e = 1$ 的情形）不在此处使用：它进入 `SumIn`。
]

#lean("UpperTheory.V.HV.CountZ", "Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean")

#proof[
  `PropZ` 说：当 $5 <= ell$、$e$ 为偶且 $ell - 1 bar.v 2e$ 时，平凡特征的 $V = 0$；这是一个带 Minkowski 界的初等计算。`CountII` 与 `CountIII` 来自 `sp4Main_alt`——#ref[命题 6.9] 的秩 4 辛类似。`CountV` 是 `countV_of_finiteness_duality_euler_host`，它使用 `abstract_count`；它被 `SumIn`（而非 `SumOut`）消耗。
]

#prop("6.11", "素数 2 与坏素数")[
  若 `LemmaK CK` 对某个 $C_K$ 成立，且 `FixedIn`、`TwoIn` 成立，则存在常数包 $K$ 使 `ThmBab K Ct` 对一切 $C_t >= 1$ 成立。这里 $J = 2^(R + 2) (2 C_K C_t\/epsilon)^R$，$R$ 是一个总的受控增长秩。窗口部分对 $ell = 2$ 与一个只依赖于 $psi$ 的有限素数集给出尺寸为 $exp(x^(4 epsilon\/5))$ 的界。
]

#lean("UpperTheory.V.Win.thmBab_of", "Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ThmBabOf.lean")

#proof[
  `FixedIn` 与 `TwoIn` 来自 Ferrero–Washington 界 `FW.ferreroWashington`（#ref[输入定理 7.12]；在库中证明）与使用 Poitou–Tate 的 `TowerBound`。
]

#lean("UpperTheory.V.FW.ferreroWashington", "Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean")

#inferred[机制：沿一个 $ell$-幂塔的 Sha 长度至多跳跃 $R$ 次，而跨越对数尺度的鸽笼论证选出 $Y in [X^(1\/J), X^(1\/2)]$ 使 $[Y, Y^2]$ 内无跳跃。这解释了 #ref[定理 6.4] 的形状。我读了陈述与证明的开头，而非鸽笼论证本身。] #used[#ref[输入定理 7.12]]

#caution("6.12")[
  `LemmaK` 只给出双指数界 $log abs(H^2) <= exp((2 e n)^C log 2^D)$；窗口论证使它可用。#ref[定理 6.4] 对一切窗口对做全称量化。它之所以不落空，只是因为 #ref[定理 3.14] 供给这样的素数对。
]

== 形变点的自守性

一般计数需要秩 3 酉形变环的每个特征零点都是自守的。方法是 Hida 族与 Taylor–Wiles–Kisin 拼合（CM 域上的 U(3)），并配一个行列式环，使剩余可约（Eisenstein）点也被覆盖。

#thm("6.13", "拼合核心")[
  设 $K = QQ(i)$，设 $(ell, iota, c, N, e, psi, o_1)$ 为宿主数据（`HostData`），$F$ 是带标记元素 $g_1$ 的宿主标架，$u$ 是其万有秩 3 酉形变。则 $"wpart"(cal(O), u, 0)$ 在 $cal(O)$ 上有限，且万有常环的每个 I 型特征零点 $r$ 都是自守的：`AutOnAlt K ι (-1) r`。
]

#lean("UpperTheory.V.Aut.ThmS6Core_s", "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/ThmS6CoreS.lean")

#proof[
  经由 `ends0_alt`、`ends_u_alt`、`ends_of_alt`，来自三种原料。

  种子。`seed2_alt`：对宿主的特征数据与每个界 $B$，存在 $m >= B$ 与 $G_QQ$ 的一个秩 2 表示 $sigma$：行列式为 $eta theta$、剩余表示是两个特征之和，且其到 $L$ 的限制（经一个 CM 型 Hecke 特征扭曲后）不可约、常、极化且自守。
]

#lean("UpperTheory.V.Z.Win.Birth.seed2_alt", "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/BirthTop.lean")

它来自经典的 Eisenstein 同余 `propE`：对大权 $k$，一个 Eisenstein 级数减去其（小的）常数项乘一个单位常数项的形式，是一个模 $ell$ 同余于该 Eisenstein 级数的尖点形式。

#lean("UpperTheory.V.Sd.propE", "Development/AutomorphicArithmetic/AutomorphicVarieties/IdeleGenerators/HolomorphicIrreducibility/SumDivHecke.lean")

二次继而是循环基变换把它带到 $L$。伴随提升给出 `UnitaryThreeAutomorphyDense`：对一切 $B$，存在 $m >= B$ 与一个不可约开像的秩 3 种子，Hodge–Tate 权为 $(m, 0, -m)$。

#lean("UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense", "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/SymUse.lean")

稠密性。算术点在 $V(J)$ 中 Zariski 稠密，因为权 $m$ 无界。

拼合。#ref[命题 6.14] 把自守性从种子传播到连通分支上的每个 I 型点。Hecke 理想 $J$ 由 `hida_unitary_of_printed_hida` 构造；输出 `ModUAlt` 由 `modularity_unitary_of_automorphy_hida_unitary` 装配。

#lean("UpperTheory.V.W.ModUAlt", "Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/PointTheoremBaseObject.lean")

种子表明 $V(J) eq.not emptyset$，故 $J$ 是真理想。[用到 #ref[命题 6.14、定理 4.26、6.18 与定义 4.22]]

#prop("6.14", "沿厚素数的拼合")[
  设 $B$ 是一个秩 $n$ 剩余数据的万有常行列式环，$J$ 是带 `HasAut B J` 的理想：对每个 Taylor–Wiles 数据 $T$ 存在拼合模 `TWAut`。则 `P1core` 与 `P3core` 成立。`P1core`：对 $V(J)$ 中一个好的自守点，其核下方的每个素数都包含 $J$。`P3core`：沿一条由厚素数（可约、非分裂）连接的好点链 $x_0, dot.op, x_h$，若一个稳定素数 $q_1 supset.eq J$ 位于 $ker f_0$ 下方，则 $ker f_h$ 下方的每个稳定或厚素数都包含 $J$。
]

#lean("UpperTheory.V.Pa.pFromAut_of", "Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/ChebotarevFamilies/PFromAutOf.lean")

#proof[
  `chain_of`：选取检测剩余表示的 Chebotarev 元（`Pa.choice`）；对它们存在 Taylor–Wiles 素数（`arPl`）；对偶 Selmer 界 `b1Ar` 与障碍界 `b2Ar` 给每个点一个至多 $n d + n q$ 个生成元与关系的表示；然后是核心。核心用到：拼合模在幂级数环上有限自由、超滤拼合引理 `s5`、以及维数计数 `galOut`。#inferred[数学上：拼合模的支撑是行列式环的不可约分支之并；一旦期望维数的分支含有一个点，它就含于其中；在厚素数处相交的分支共享支撑。这就是 Skinner–Urban 与 Thorne 的连通性论证。]我们读了 `s5`、`galOut` 与 `chainAbs` 的陈述，未读其证明。
]

#caution("6.15")[
  结构 `OpenImageCondition` 与引理 `*_of_open O` 的哑参数只是 `Row0b` 的载体；证明忽略它们。#ref[定理 6.13] 只对 $K = QQ(i)$ 与一个受限制的 `HostData` 陈述。它是适配宿主域的特殊情形，不是一般的自守提升定理。
]

== 来自自守形式的伽罗瓦表示

#defn("6.16", "Row0b")[
  设 `Rc` 是局部配方（recipe）的一个概念（从 $"GL"_n (E_w)$ 的不可约表示到 Weil–Deligne 表示的一族映射 `rc`）。`Row0b Rc` 说：设 $E$ 是 CM 域，$ell$ 是素数，$iota : QQ_ell tilde.op CC$，$a >= 1$，$pi$ 是 $"GL"_a (bb(A)_E)$ 的尖点自守子空间，它对极大实子域的 Hecke 特征 $chi$ 是正则代数且极化的（符号条件 $chi_v (-1) = (-1)^a$ 且 $pi ⊗ chi^(-1) tilde.op$ 共轭对偶）。则存在 $r : G_E arrow.r "GL"_a (QQ_ell)$、整数 $w t$ 与带性质 `PropsB` 的 Hodge–Tate 多重集 $"HT"_tau$：
  (i) $r$ 连续且半单；
  (ii)（away）对满足 $w arrow.not ell$ 的有限 $w$、每个满足 `Rc` 的 `rc` 与 $w$ 处的每个局部成分 $sigma$：`AwayB`(WD(r|G_w), rc(σ))；
  (iii)（weights）$"HT"_tau = {(a - 1)\/2 - z}$，其中 $z$ 是无穷特征在 $iota tau$ 处的权；
  (iv)（weights_conj）$"HT"_(tau ∘ c) = w t - "HT"_tau$（$c$ 为复共轭）；
  (v)（above）对每个局部数据 ($P$, `AI`)（`LocPrime`、`LocAinf`，`LocTied` 非空）与每个带 `Pst.Induces` 的桥 $B_w$，在所论的位 $w$ 处：若 $pi_w$ 是球面的，则 $r bar.v G_w$ 晶体且 de Rham，跳跃为 $"HT"_tau$。此外，若 $"rc"(sigma)$ 是 $"mono"_0$ 且或 tame 兼 squarefree（带 `IsQpBig`）或挠，则 $r bar.v G_w$ 是 de Rham 且潜在半稳定，跳跃相同，且在 $ell$ 处 `AwayB` 在 $r bar.v G_w$ 的 Weil–Deligne 表示与 $"rc"(sigma)$ 之间成立。
]

`AwayB(x, y)` 意为：维数相等；若 $y$ 是挠的且为 $"mono"_0$ 则 $x = y$；且若对剩余特征 $p$ 有 $a = 1$ 或 $16 a^2 < p$，而 $y$ 是 tame、squarefree、$"mono"_0$，则 $x$ 是 $"mono"_0$ 的，且在 0 次 Weil 元上与 $y$ 有相同的特征多项式。

#lean("UpperTheory.GalStar.Row0b", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean")
#lean("UpperTheory.GalStar.PropsB", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean")
#lean("UpperTheory.GalStar.AwayB", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean")

#caution("6.17")[
  `Row0b` 弱于 Harris–Lan–Taylor–Thorne、Scholze 与 Shin 型的已发表定理（库中的 `PolarizedGaloisRepPublished`）。它不断言 $r$ 是共轭自对偶的。它不断言 Frobenius 权的纯性。$ell$ 之外的相容只是 `AwayB`，而非 $"WD"(r) = "rc"(sigma)$。在 $ell$ 之外，Frobenius 特征值不受约束，除了 tame squarefree 情形中 0 次 Weil 元上、以及挠情形中的完全相等。上文的条款如所述地以局部数据与桥为条件。它是对弱配方 `IsRecT`（#ref[定义 6.25]）陈述的，不是对真正的局部 Langlands 对应。消费者 `polG_of_printsH_of_rT` 只读取连续性、半单性、权、away 的挠分支与 above 的 nice 条款。其他消费者（`AUpDown`、`AAcross`）未全部核查是否使用了更强的形式。
]

#thm("6.18", "Row0b 成立")[
  `Row0b (fun h rc => IsRecT h rc)` 是一个定理：`galoisLocalGlobalStrong_recParameter`。
]

#lean("UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean")
#lean("UpperTheory.Gal.Int.galoisLocalGlobalStrong_of_geometry_lift", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean")

#proof(uses: ref[构造 6.19、定理 4.26、6.20、定义 4.22 与命题 6.22])[
  它是 `galoisRepresentations_of_thetaLift` 应用于 theta 提升命题 `tLiftK`（#ref[定义 4.22]），后者由 #ref[定理 4.26] 与 #ref[定理 4.24] 证明，即 `galoisLocalGlobalStrong_of_geometry_lift geoOne_holds tLiftK`。接线（33 行）是

  `Row0b ← Row0 ← rest ← CoreAll ← toCoreK(TLiftK, ClosedPhi, DescOffT, LimFinOdd),`

  其中 `LimFinOdd ← (SeedFinOdd, CongFinOdd)` 且 `SeedFinOdd ← GeoOne`。没有任何 Frobenius 特征值取自迹公式；表示由几何与极限构造。诸阶段见 #ref[构造 6.19]。
]

#heading(numbering: none, outlined: false)[构造 6.19（Row0b 的证明）.]

+ `GeoOne`：几何表示。取奇数 $a$、CM 域 $E$（带 `FieldOK`：$sqrt(-d) in E$、偶数次实子域、$E\/E^+$ 不分歧、$ell$ 上方的位全分裂且至少三个），以及定酉群 $U(a)$ 上带 $w_0 bar.v ell$ 处型条件、有限集之外球面、$v' bar.v ell$ 处 lacunary 权的形式 $U$。则存在 $ell$-进表示 $rho$，取自一个光滑射影 Harris–Taylor 簇的上同调、由 $U$ 的 Hecke 特征系统切出：一个连续半单的 `VBase`；对每个满足 $w arrow.not ell$ 且带 `UsPl`（被使用的分裂位）与 $U$ 在 $w$ 处的 Satake 参数的 $w$，一个带 $w$ 处 `ESAt` 的；对每个满足 $w bar.v ell$、带 `OneK x w v'`、不同于 $w_0$ 与 $v'$、且在 $w$ 处有 Satake 参数的 $w$，一个晶体且跳跃正确的，以及一个被 Hecke 多项式杀死 $phi$ 的。

  #lean("UpperTheory.Gal.Int.Geo.geoOne_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean")

  该簇是一个 `HTower`：带有限平展 Hecke 对应群的光滑射影概形。

  #lean("GlobalTheory.GalV.HTower", "Development/AbelianVarietyTheory/Definitions/Divisors/IdTower.lean")

  关系 `ESAt` 只是零化：惯性平凡作用，且 $rho("Frob"^(-1))$ 被 $product_b (X - b)$ 杀死。它不是特征多项式的等式。

+ `TowES`：Frobenius 关系（#ref[定理 6.20]）。
+ `SeedFinOdd`：精确特征多项式。`CharOfAnn`：若 $product (X - s)$ 杀死 $M$、多重集 $s$ 是 generic 的（只有子多重集 $s$ 有自己的尺寸与乘积）、且 $"det" M = product s$，则 $"charpoly" M = product (X - s)$。`seedFinOdd_of` 用 lacunary Hodge–Tate 权（`SenWLac`）提取 $rho$ 的一个 $a$ 维部分，用 Hecke 特征固定行列式，并使用 generic 性。

  #lean("UpperTheory.Gal.Int.Div.seedFinOdd_of", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/SeedFinOddOf.lean")

+ `CongFinOdd`：权插值。奇秩形式的每个特征系统 $theta$ 是特殊形式特征系统的 `PolyApprox`-极限：对每个 $epsilon > 0$，存在有限多个 $eta$ 与系数 $c_eta$，使得对 Hecke 变量的每个整系数多项式 $P$ 有 $abs(P(theta) - sum c_eta P(eta)) <= epsilon$。

  #lean("UpperTheory.Gal.Int.Cong.congFinOdd_of_ex", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/CongruenceOddLevel/CongFinOddOfLvLac.lean")

  不构造任何特征簇。

+ `LimFinOdd`：迹极限。`exists_trace_limit` 给出 $G_E$ 上一个作为迹之极限的函数；`PsChar.exists_ssRep`（Taylor 的伪特征论证）表明它是唯一半单表示的迹；连续性随后；Chebotarev 密度输运 Frobenius 数据。

  #lean("UpperTheory.Gal.Lim.limFinOdd_of", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TraceLimits/LimFinOddOf.lean")

+ `ClosedPhi`：在 $ell$ 处的闭性。若 $r$ 是集合 $C$ 中表示的联合迹极限、全都晶体且带相同跳跃 $J$，则 $phi$ 在 $"WD"(r)$ 上的迹是 $C$ 的那些迹的极限。

  #lean("UpperTheory.Gal.ClosedPhiFromClosedTrace.ClosedPhi", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ClosedPhiFunctoriality/JointApproxOfMem.lean")

+ `TwoUp`：偶秩（#ref[命题 6.22]）。
+ `DescOffT`：从 $"GL"_a$ 到 $U(a)$。对 CM 域上尖点、正则代数、极化的 $pi$ 与任意有限位集 $Z$，存在一个与 $Z$ 不相交的非分裂位的有限集 $T$，以及定 $U(a)$ 上的形式 $U$：在一切分裂位匹配 $pi$，在 $T$ 之外的非分裂位不分歧。

  #lean("GlobalTheory.Cong.DescOffT", "Development/AbelianVarietyTheory/Definitions/GaloisGeometry/MatchOfMatchOffTEmpty.lean")

  这是一个迹公式下降（Speh 基变换、Jacquet–Shalika 刚性、重数一），不是伽罗瓦下降。

+ `QuadLift`、`JoinUp`：去掉域条件（#ref[命题 6.23]）。
+ `rest`：所有位。一个环面、非连通支撑的论证给出 Iwahori 固定位处的相容性；`Props.big` 弱化为 `PropsB`。

[用到 #ref[定理 4.26、6.20，命题 6.22、6.23 与定义 4.22]]

#heading(numbering: none, outlined: false)[Eichler–Shimura 关系]

#thm("6.20", "Eichler–Shimura 同余关系")[
  设 $ell$、$p$ 为素数，$f, n in NN$，$cal(O)$ 是离散赋值环，$p$ 在其极大理想中，剩余域被 $a arrow.bar a^(p^f)$ 固定，$K = "Frac" cal(O)$，$p eq.not 0 in K$。设 $H$ 是 $K$ 上的一个好塔，$theta$ 是取值于域 $L supset QQ_ell$ 的 Hecke 特征系统，$C$ 是 $H$ 被 $cal(O)$ 上光滑模型的覆盖，带 $C dot.op "Cong" p f n theta.alt$。设 $V$ 是代数闭的 $Omega supset K$ 在 $cal(O)$ 上的一个赋值环，$ell$ 在其中是单位，且 $sigma in "Aut"(Omega\/K)$ 保持 $V$。再假设上同调的 $theta$-分支在全部 $"Aut"(Omega\/K)$ 下稳定。则对 $theta$-分支中的每个 $x$：
  (i) 若 $sigma$ 在 $V$ 的剩余域上平凡，则 $sigma x = x$；
  (ii) 若 $sigma$ 在剩余域上作用为 $v arrow.bar v^(p^f)$，则令 $q = p^f$，
  $ sum_(j = 0)^n (-1)^j q^(binom(j, 2)) theta.alt_j (sigma^(-1))^(n - j) x = 0. $
]

#lean("UpperTheory.Gal.Mod.TowES", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/BasicOpenSections/PlaceData.lean")

对 $n = 2$ 这就是 $F^2 - T_p F + p = 0$。系数是 $"co"(q, j) = (-1)^j q^(binom(j, 2))$。

#proof[
  特殊纤维中的几何（`CongKS`）。对带 $D.m = 1$（在所选位处符号差 $(1, n - 1)$）的 Harris–Taylor 数据 $D$，对应 $T_j$ 是平展水平模型上泛阿贝尔簇的 Kuga–Sato 幂的 $w$-同源（度 $q^j$）。`PtId`：对每个带代数闭分式域的赋值环 $V$、每个闭点是特殊纤维某分支的泛点的点、每个 Frobenius $phi$ 与 $T_j$ 的每族双射截面 $z_j$，恒等式 `AltId` 成立：带权 $q^(binom(j, 2))$ 的点 $F^(n - j)(v_(j, i))$ 的加权多重集在偶 $j$ 与奇 $j$ 上相等。
]

#lean("UpperTheory.Gal.crystallineComparison.Mod.congKS_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/AnnihilatorModels/IdealSplitHolds.lean")

(1) 泛点是普通的（`ordGen`）：分支泛点上的每个几何点在 $w$-挠中有 $N(w)^(n - 1)$ 个点。

#lean("UpperTheory.Gal.Ord.ordGen", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/RadicalStalks/OrdGen.lean")

这是一个 Katz 式的 Kodaira–Spencer 论证：非普通点会给出 $k[epsilon]$ 上的、从特征 $p$ 域拉回的形变，其 Frobenius 像是水平的且被 Kodaira–Spencer 杀死。不使用 Serre–Tate 理论，也不使用普通轨迹的开性。

(2) 普通点处的恒等式（`OrdCount`）：存在 $FF_q$-空间 $H$（维数 $n$）与一条线 $C$；$T_j$ 由 $j$ 维子空间 $D subset H$ 标号，其约化当 $C subset D$ 时是 $F(A(D mod C))$、否则是 $A(D mod C)$。$H\/C$ 的 $m$ 维子空间 $U$ 来自 $q^m$ 个补与一个原像；权相消是因为 $binom(m + 1, 2) = binom(m, 2) + m$（`telescope_core`）。

(3) 所有点（`NormOfPt`）：若模型在 $cal(O)$ 上光滑，特殊纤维既约且坐标环在其于 $p$ 处的局部化中整闭（`smoothClosed_of`）。`CongrRad`：模一个根理想的每个极小素都相等的多项式模该理想相等。于是泛点上的恒等式给出范数形式的整体恒等式。

#lean("UpperTheory.Gal.crystallineComparison.NormOfPt", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/AnnihilatorModels/GenericMulOfProd.lean")

输运到上同调。严格 henselian 基上的正常基变换、有限平移对应在上同调上的作用、以及沿一个投影拉回后 `hop` = 沿另一个投影的迹（`HopOp`）给出 `TowES`。不使用点计数。#inferred[从范数恒等式 `NormOn` 到 `TowES` 的步骤我们没有读；各部件（`ESTot`、`MapUSharp.lean`、`PTowES.lean`）看起来是真正的工作。]

模型。`harrisTaylorIntegralModel_nonempty` 对与 $p$ 互素的水平 $N >= 3$ 给出相对维数 $a(n - 1)$ 的拟射影光滑模型，来自 theta 函数 Siegel 模、一个 Zarhin 技巧族、一个 Harris–Taylor 结构的有限概形，与一个有限群商。

#lean("GlobalTheory.T.harrisTaylorIntegralModel_nonempty", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/HarrisTaylorIntegralModelNonemptyStatement.lean")

[用到 #ref[构造 6.19]]

#caution("6.21")[
  该关系只在符号差 $(1, n - 1)$ 的位 $w$ 处成立，且数据是对每个 $w$ 选取的。这正是 #ref[GeoOne] 中的表示依赖于 $w$、从而需要极限步骤的原因。
]

#prop("6.22", "由奇秩得偶秩")[
  设 $E$ 是 CM，$E\/E^+$ 不分歧，$[E^+ : QQ]$ 为偶数，$n >= 1$ 为偶数。对 $U(n)$ 上每个自守 $U$ 与分裂位 $w_0$，存在 $t$、Hecke 特征 $kappa$ 与到 $U(n + t)$ 的两个提升 $U_1$、$U_2$（$n + t$ 为奇数），用满足 $psi_(1, i) eq.not psi_(2, j)$ 且在 $w_0$ 不分歧的特征集 $psi_(1, i)$、$psi_(2, j)$ 构造。这就是 `TwoUp E n`。
]

#lean("UpperTheory.Gal.TP.Sub.TwoUp", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SplitLineSubtraction/RowDefOfOdd.lean")

#proof(uses: ref[定义 4.22 与定理 4.24、4.26])[
  使用 theta 提升 `TLiftK`，取 $t = 2(d_0 + n) + 1$（#ref[定义 4.22]，由 #ref[定理 4.26] 与 #ref[定理 4.24] 构造）；分裂不分歧位处提升的 Satake 数据是 $"Sat"(U) kappa^(-1)$ 加上诸 $psi_i (w)$。相减：两个提升有表示 $rho ⊗ kappa ⊕ psi_(1, i)$ 与 $rho ⊗ kappa ⊕ psi_(2, j)$，不相交性分离出 $rho$（`rowDef_of_odd`）。
]

#prop("6.23", "二次 CM 扩张")[
  `QuadLift`：对全复数域 $K subset M$、$[M : K] = 2$ 与 $"GL"_a \/ K$ 上尖点的 $pi$：若 $M$ 的某个位在 $K$ 上分歧且 $pi$ 在其下方有 Satake 参数，则存在 $"GL"_a \/ M$ 上尖点的 $P$ 带 `IsLift`(π, P)。
]

#lean("GlobalTheory.GalCut.QuadLift", "Development/AbelianVarietyTheory/Definitions/GaloisGeometry/IsWeight.lean")

`exists_quadratic_CM_ext_split_at`：对 CM 域 $Y$ 与坏位有限集 $T$，存在无穷多个 $QQ = Y(sqrt(-p_1 p_2))$ 使 $T$ 的位分裂、且恰在 $T$ 之外的一个好位处在 $QQ^+$ 上分歧。

#lean("UpperTheory.Gal.Int.Core.exists_quadratic_CM_ext_split_at", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/CrystallineDescent/ExistsQuadraticCMExtSplitAt.lean")

#proof[
  选 $c$ 被 2、3 与 $T$ 中位的范数整除，选素数 $p_1, p_2 > c$ 满足 $p_1 p_2 equiv -1 (8c)$；于是 $-p_1 p_2 equiv 1$ 对每个整除 $c$ 的素数。`QuadLift` 的假设是 Arthur–Clozel 判据：$pi$ 在 $M\/K$ 分歧处球面迫使 $pi$ 不等于其二次特征扭曲，故基变换保持尖点。`joinUp_of'` 使用这些 $QQ$：基变换的表示被粘合（Chebotarev 与 Brauer–Nesbitt，`PatchOne`、`StepDown`）成 $G_E$ 的一个表示，其对 $G_QQ$ 的限制对余有限多个 $QQ$ 匹配。
]

#lean("UpperTheory.Gal.Int.Core.joinUp_of'", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/CrystallineDescent/BadFinite.lean")

#inferred[`ramSph`（分歧基变换）的证明经由 `UpperTheory.Gal.Join.*`，我们没有读；粘合描述是我们对 `PatchOne` 的解读。]

== 轻量局部 Langlands 对应

#defn("6.24", "好表示")[
  对局部域 $k$ 与 $"GL"_n (k)$ 的不可约光滑表示 $y$，`GoodCusp` 意为：$n = 1$，或 $k$ 连续同构于 $QQ_g$ 且 $y = y_0 ⊗ chi$，其中 $y_0$ 是不可约表示，带一个被极大 pro-$p$ 子群 $K_1$ 固定的非零向量（该定义不要求 $y_0$ 本身是尖点的；`GoodCusp` 只被应用于尖点表示）。称表示是 `Good` 的，若其支撑中的每个尖点成分都是 `GoodCusp` 的。
]

#lean("UpperTheory.Zero.LLC.Good", "Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean")

#defn("6.25", "弱局部 Langlands 律")[
  设 $E$ 是数域，$w$ 是有限位，$h$ 是 $Omega$ 在 $w$ 上方的位。映射 $"rc" : "Irr" "GL"^ast (E_w) arrow.r "WD"(h)$ 与 $a : W_h arrow.r E_w^times$（局部 Artin 映射）满足 `LawsT`，若：
  - $"dim" "rc"(x) = n$ 于 $"GL"_n$；$"rc"(chi) = chi ∘ a$ 于 $"GL"_1$；
  - （langlands）对多段（multisegment）$l$ 的 Langlands 商，$"rc"(x) = "segSum"("rc", l)$；
  - （cusp）$x$ 尖点蕴含 $"rc"(x)$ 不可约（仅一个方向）；
  - $"rc"(x ⊗ abs("det")^s) = "rc"(x) ⊗ abs(dot.op)^s$；$norm("det" "rc"(x)(sigma)) = norm(omega(a_sigma))$（$omega$ 为中心特征）；
  - 仅对 `Good` 的 $x$：被特征扭曲、精确的中心特征、与逆轭的相容、以及当 $x$ 有 $K_1$-固定向量时 $"rc"(x)$ 的 tame 性；
  - （inj）$"rc"(x) = "rc"(y)$ 且 $y$ 为 `Good` 蕴含 $x = y$；
  - （type）对 $QQ_g$ 上深度零、膨胀 $"GL"_n (FF_g)$ 尖点 $tau$（带 $FF_(g^n)^times$ 的正则特征 $theta$）的 $sigma$：$"rc"(sigma)$ 是 $"mono"_0$，惯性特征多项式为 $product_(j < n) (X - theta(z^(g^j)))$。
]

`IsRecT h rc` 意为 $exists a$，$a$ 是局部 Artin 映射且 `LawsT a rc`。

#lean("UpperTheory.Zero.LLC.LawsT", "Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean")
#lean("UpperTheory.Zero.LLC.IsRecT", "Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean")

#thm("6.26", "轻量局部 Langlands")[
  `RecTExists`：对每个数域 $E$、代数闭包 $Omega$、赋值子环 $A subset Omega$、有限位 $w$ 与 $w$ 上方的位 $h$，存在 `rc` 带 `IsRecT h rc`。
]

#lean("UpperTheory.Zero.LLC.recTExists", "Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean")
#lean("UpperTheory.Zero.LLC.RecTExists", "Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean")

#proof(uses: ref[定义 6.24 与 6.25])[
  它是无条件的。(1) `artEx`：局部 Artin 映射，来自整体类域论（库中已证）。(2) `cuspEx`：在 `GoodCusp` 上用 `goodMap`；在每个其他尖点表示上用固定维数、单位范数行列式的不可约 Weil–Deligne 表示，经扭曲以固定绝对中心特征（`junkEx`）。(3) 对 $QQ_g$ 上深度零尖点的 `parEx`：`typeEx` 找到膨胀的 $"GL"_n (FF_g)$ 尖点 $tau$（在差一个特征的意义下唯一）；`nameLaws` 是 Green 的正则特征参数化；`extEx` 选取带剩余域 $FF_(g^n)$ 的辅助域；`indEx` 构造由非分歧 $n$ 次扩域诱导的 $n$ 维 Weil 表示，因 $theta$ 正则而不可约。(4) `exists_isLExt` 经 Zelevinsky–Langlands 多段分类（库中已证）扩展到一切不可约表示。(5) 其余各律逐条核对（`extDim`、`extTw`、`extDual`、`extInj`、`extDepth`、`typeIff`）。
]

#caution("6.27")[
  `RecTExists` 不是 $"GL"_n$ 的局部 Langlands 对应。它没有双射性、没有满射性、没有唯一性，也没有对的 $epsilon$-因子或 L-因子。条款 `cusp` 与 `depth` 是单向的，若干条律只对 `Good` 表示成立。对每个不是 `GoodCusp` 的尖点表示（wild，或在不同于 $QQ_g$ 的域上），`rc` 的取值是占位符 `junkEx`——一个恰有正确维数的任意不可约表示。下游的 epsilon 族是常数 1（`extraV`），所以任何 epsilon 槽位都是哑的。完整命题（`LocalLanglandsGL`）存在于库中但未被使用。下游只使用球面与深度零表示（`good_of_fixed`）。
]

== 本章传递什么

- #ref[定理 6.4]：Vandiver 窗口界，$t = x^401$、尺寸 $sqrt(exp(x^epsilon)) = exp(x^epsilon \/ 2)$，供引擎（#ref[定理 5.27]）使用。
- #ref[定理 6.18]：$"GL"_a \/ E$ 上正则代数极化尖点形式的伽罗瓦表示，弱形式 `PropsB`，使用 theta 提升 `TLiftK`（#ref[定义 4.22]）。
- #ref[定理 6.13]：秩 3 酉常环全部 I 型特征零点的自守性（$K = QQ(i)$）。
- #ref[定理 6.20]：替代点计数的同余关系。
- #ref[定理 6.26]：弱局部 Langlands 片段，仅对球面与深度零成分够用。

外部输入：Ferrero–Washington（#ref[输入定理 7.12]）、$p$-进 Hodge 理论（#ref[输入定理 7.3]，连同列于基础章“其他输入”下的 Berger 定理 `DeRhamPotSemistable`）与平展上同调（#ref[输入定理 7.5]）。[用到 #ref[定理 3.14、4.26 与定义 4.22]]
