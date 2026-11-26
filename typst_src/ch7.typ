// ch7.typ —— 第 7 章 输入定理
#import "lib.typ": *
#pagebreak(weak: true)

= 输入定理

本库中的黎曼猜想证明并不只从 Mathlib 出发。它先在同一库中证明了一批大型经典定理，后续各章把它们当作工具使用。本章列出这些定理。每一条都给出 Lean 文件所证明的精确形式、库中证明它的简要说明，以及——在 Lean 命题比教科书定理狭窄之处——一条注意。

以下两条对下面每一项都成立。第一，每个命题都是一个 Lean 定义 `def X : Prop`，且存在一个恰好为该类型的 Lean 定理。名字 `Published` 与 `_of_literature` 并不表示“假设”。第二，经全树扫描（对整棵树的文本扫描），树中没有 `sorry`、没有公理声明、也没有 `native_decide`。所以这些输入定理都是已证明的结果，但许多只在特殊情形下被证明。读 Lean 命题、而非名字，才是了解下游有哪些可用的稳妥方式。

本库有 175,187 个 Lean 文件与 17,374,215 行（#ref[表 2]）。

== Hironaka：消解与主化

#env("输入定理", "7.1", "特征 0 中的函子性消解与主化")[
  在固定的一个宇宙中处理概形。

  （消解。）设 $k$ 是特征 0 的域，$X$ 是 $k$ 上既约、拟紧且局部有限型的概形。存在一条规则，对每个这样的 $(k, X)$ 指派一个有限爆破序列
  $ X_n arrow.r X_(n-1) arrow.r dots.c arrow.r X_0 tilde.op X, $
  其中 $X_(i+1) arrow.r X_i$ 是在理想层 $Z_i$ 中的爆破。“爆破”意指：$Z_i$ 的拉回是有效 Cartier 除子，且每个使 $Z_i$ 的拉回为有效 Cartier 的映射 $T arrow.r X_i$ 都唯一地经由 $X_(i+1)$ 分解。该序列满足：
  (R1) $X_n$ 在 $k$ 上光滑，且 $X_n arrow.r X$ 固有；
  (R2) $X_n arrow.r X$ 在光滑轨迹 $X^"sm"$ 上是同构，且 $X^"sm"$ 的原像稠密；
  (R3) 每个中心 $Z_i$ 的支撑位于 $X$ 的非光滑轨迹之上；
  (R4) 非光滑轨迹的既约原像是严格正规交叉除子：所有茎正则，且局部地理想由 $product_(i in J) f_i$ 生成，其中 $(f_i)$ 是正则参数系的一部分。

  该规则是函子性的：对任意相对维数的光滑态射 $phi : X' arrow.r X$，$X'$ 的序列是 $X$ 的序列的拉回（去掉拉回中心为空的那几步）。沿特征 0 的域扩张 $K\/k$ 作基变换亦然。

  （主化。）设 $X$ 在特征 0 的 $k$ 上光滑、拟紧、局部有限型。设 $I$ 是在每个不可约分支上非零的理想层。设 $E$ 是一个处于简单正规交叉位置的有限光滑除子表。该规则产生一个爆破序列 $(X_i, Z_i)$ 连同理想 $I_i$ 与边界表 $E_i$，使得：$I_0 = I$，$E_0 = E$；每个中心 $Z_i$ 在 $k$ 上光滑且与 $E_i$ 处于简单正规交叉位置；$I_i subset.eq Z_i$；$Z_i dot.op I_(i+1) = I_i$（拉回）；$E_(i+1)$ 是 $E_i$ 的严格变换加上新的例外除子；$I_n = cal(O)$；$I$ 到 $X_n$ 的拉回是诸例外除子之积；每个 $X_i$ 光滑、每个 $E_i$ 简单正规交叉。它对光滑态射与域扩张同样函子性。
]

#lean("FunctorialResolution.functorialResolutionCharZero", "Development/ResolutionOfSingularities/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean")
#lean("FunctorialResolution.functorialPrincipalizationCharZero", "Development/ResolutionOfSingularities/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean")

命题是 `FunctorialResolutionCharZero` 与 `FunctorialPrincipalizationCharZero`，位于 `Development/ResolutionOfSingularities/Statements.lean`。两个定理都没有假设。

库如何证明它。文件夹 `Development/ResolutionOfSingularities` 有 499 个文件、140,709 行。爆破是在其中从零构建的（`Foundations` 中约 4,800 行），因为 Mathlib 没有爆破。论证是基于不变量的现代论证。对象是“带边界的标记理想”：一个理想 $I$、一个重数 $m$ 与一个光滑除子表 $E$。对 Krull 维数归纳。为把 $I$ 的阶降到 $m$ 以下，取一个极大接触超曲面 $H$，它局部是落在导数理想 $D^(m-1) I$ 中的坐标超平面。把 $I$ 换成一个“调谐”理想 $product_(j < m) (D^j I)^(c_j)$，并在 $H$ 上降一维解决问题。基础情形是局部单项式理想：通过对边界除子的交作爆破来主化，且每步一个自然数的字典序三元组下降。特征 0 在两处被使用：每个整数都是单位（Euler 论证，`mem_pow_succ_of_deriv_mem_pow`），以及 $k$ 的每个域扩张都形式光滑，这给出所有点处的对偶导子。归纳步骤是定理 `isCorrect_canonicalAlgorithmRules`，它没有遗留假设。最大的部分是 `IdealPrincipalization`（219 个文件、69,051 行）。消解由主化推出：把一个仿射片嵌入仿射空间，主化嵌入簇的理想，丢弃分离出的成分，再按函子性粘合。函子性来自忠实平坦下降与超曲面选择无关性（`MaxContactHypersurfacesEtaleEquivalent`）。

#caution("7.2")[
  光滑中心只记录在主化命题中。消解命题（R1 到 R4）没有说中心 $Z_i$ 光滑、也没有说它们与例外除子正规相交。所以在此方面它弱于 Kollár 定理 3.36。另一方面它更强：不假设 $X$ 分离。下游各章使用派生形式 `ResolutionCharZero` 与 `Published.Principalisation`（后者用于光滑射影整的 $Y$），它们由这两个定理得到。与 Kollár 文本的对应是阅读者依结构作出的判断。
]

Arakelov 各章实际消耗的推论是 `ResKStatement`：对特征 0 上既约的 $X subset PP^M$ 与相对维数 $D$ 的稠密开光滑 $U subset X$，存在光滑射影的 $X'$ 带到 $X$ 的映射、在 $U$ 上的同构、以及一个边界，其局部坐标 $z_1, dot.op, z_D$ 中边界为 ${z_1 dots.c z_k = 0}$。

#lean("PositivityTheory.ResPlug.FromRes.resK", "Development/WeilBound/CoreStatements/ResolutionCharZero/PlugResK.lean")

它由消解、再对边界主化、再为正规交叉除子取局部坐标而构造。

== p-进 Hodge 比较定理

设 $l$ 是素数，$K$ 是 $QQ_l$ 的有限扩张（任意分歧，包括 $l = 2$）。Lean 文本中 $l$ 是剩余素数，许多论文称之为 $p$。模型是带映射到 $"Spec" cal(O)_K$ 的概形 $X$。记 $V^n = H_"ét"^n (X, QQ_l)$，取自库自己的平展上同调，带 $"Gal"(bar(K)\/K)$ 的作用。“光滑模型”（`Model.Sm`）意指：在 $cal(O)_K$ 上射影、对某个一致化子严格半稳定、且在 $cal(O)_K$ 上光滑。所以光滑模型是 $cal(O)_K$ 上的光滑射影概形。

#env("输入定理", "7.3", "好约化比较定理")[
  (a) Hodge–Tate（`HTBij`）。对每个 $l$、$K$，在 $V^n$ 与 $H^(n - a)(X, Omega^a) ⊗ CC_l$ 的对偶之间存在自然的、伽罗瓦等变的（差 $chi^a$）配对。对每个相对维数 $d$ 的光滑模型 $X$，它在每个次数 $n$ 单射、满射，且
  $ dim_(QQ_l) V^n = sum_(a = 0)^n dim_K H^(n - a)(X_K, Omega^a). $
  同一事实的矩阵形式是 `HTSpecGood`：对每个标架存在实现该配对的 $CC_l$-矩阵 $Phi$，它在模型的拉回下自然。

  (b) `CstSmooth` 是三条命题的合取，对每个 $l$、$K$ 与光滑模型 $X$：
  (i)（`SmoothModelCrystalline`）对每个 $n$ 与 $V^n$ 的每个 $QQ_l$-基 $b$，伽罗瓦作用的矩阵是 $B_"cris"$-容许的。即：存在 $B_"dR"$ 的子环 $B_"cris"$ 上的矩阵 $P$、$Q$，$P Q = 1$ 且对一切 $sigma in G_K$ 有 $rho(sigma) sigma(P) = P$。
  (ii)（`DeRhamComparisonSmooth`）存在自然的伽罗瓦等变配对 $V^n times (H_"dR"^n)^∨ arrow.r B_"dR"$，与滤过相容且严格，使得 $V$ 的一个 $QQ_l$-基保持 $B_"dR"$-线性无关。
  (iii)（`CrysPhi`）对每个剩余域数据，存在一个类似的到 $B_"cris"$ 的配对，取值在特殊纤维的晶体上同调 $D$ 中（与 $W(k)[1\/l]$ 张量）。它自然、伽罗瓦等变、单射，并与 Frobenius 相容。
]

#lean("UpperTheory.Gal.Seam.cstSmooth", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/CrystallineTowers/Closed.lean")
#lean("UpperTheory.Gal.Seam.HT.htSpecGood", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/CrystallineTowers/ClosedHT.lean")

命题是 `CstSmooth`（`Development/WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/CstSmooth.lean`）、`HTBij`（`.../HodgeSurjectivity/HtBijOfParts.lean`）与 `HTSpecGood`（`.../HodgeTateResidues/HodgeTateSpectral/HTSpecGood.lean`）。第二个定理在 `CrystallineTowers/ClosedHT.lean`。两个封闭定理都没有假设。

#caution("7.4")[
  四点限制要紧。
  + 仅好约化。每个命题都需要 $cal(O)_K$ 上的光滑射影模型。Faltings 的一般情形（$K$ 上光滑固有但无好模型）未被覆盖。
  + 单射形式。条目 (ii) 与 (iii) 没有满射性或维数相等字段。它们给出单射的严格配对，而非教科书同构 $B_"dR" ⊗ V tilde.op B_"dR" ⊗ H_"dR"$。条目 (i) 是教科书的容许性陈述。
  + 半稳定比较 $C_"st"$ 未被证明。命题 `SemistableModelSemistable` 与 `CstNarrow` 存在。定理 `narrow_of` 由两个假设（`BstRegularPeriodRing` 与 `SeamAll`）推出 `CstNarrow`，而这两个假设在树中任何地方都未被证明。该文件夹之外的任何声明都不使用它们。它是死代码（见最后一小节）。
  + 系数是 $QQ_l$。没有整理论（没有 Fontaine–Laffaille，没有 Breuil–Kisin）。

  在适用范围内定理是普遍的：任意 $K$、任意 $l$、任意维数、任意权。没有诸如 $l > dim X$ 的限制。
]

库如何证明它。路线既非棱柱式、也非经由几乎纯性。它是一条第一陈类路线。在平展线丛数据构成的 Čech 覆盖上逐图构造三个到 $A_"cris"$ 一侧代数的映射：一个平展映射（Kummer 类）、一个来自对数晶体一侧的 Bockstein 型映射、以及一个到 $B_"dR"$ 的周期映射 $kappa$。它们给出带杯积公式的预配对。在最高次，与 $c_1$ 的 $d$ 次幂的杯积是单位（`powK_ne_zero`）。平展 Poincaré 对偶（#ref[输入定理 7.5]）随后给出单射性。Fontaine 的 $B_"cris"$ 正则性（`bCris_isRegular`）把独立的伽罗瓦稳定张成变成容许性。骨架是 `cstSmooth_of_etSide`。Hodge–Tate 满射性（`HodgeSurjectivity` 中 53 个文件）表明平展类是 Kummer 类或 $d log$ 类，且图的 Hodge 上同调由 $d log$ 与杯积生成。它以维数计数 `HodgeTateDimensionEquality` 收尾。周期环 $A_"inf"$、$A_"cris"$、$B_"dR"$、$B_"cris"$、倾斜、Fontaine–Wintenberger 与 Ax–Sen–Tate 在 `GroundTheory/PAdicHodge` 中从零构建（226 个文件、64,317 行）。真正的比较是 `PadicHodgeComparison`（538 个文件、50,512 行）。[用到 #ref[输入定理 7.5]]

后续各章消耗的是三个推论，针对在 $l$ 处有好约化的志村簇。它们是 `CrysStep`（$l$-进部分在 $l$ 上方的位处晶体）、`JumpStep`（Hodge–Tate 跳跃包含 Hodge 次数）与 `PhiStep`（$phi$-模上的 Frobenius 被 Hecke 多项式杀死）。它们供给 #ref[定理 6.18] 的“$l$ 上方”条款。

#lean("UpperTheory.Gal.Seam.crysStep_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/CrystallineTowers/Closed.lean")

== Mathlib 概形上的平展上同调

#env("输入定理", "7.5", "平展上同调、Poincaré 对偶、Künneth 与 Lefschetz")[
  层是 $"Sheaf"("étale topology on Mathlib schemes", "Mod"_R)$。上同调是该 Grothendieck 阿贝尔范畴中的 `Ext`，用内射消解计算。“空间”是概形上的单纯预层。杯积、陈类、Kummer 类、Bockstein、Gysin 映射与纯性都在此基础上构造。在这个基础上库证明以下内容（`UpperTheory.Gal.KunnethLefschetz.core_holds`，一个带字段 `c2`、`c3`、`c4`、`c5`、`d1` 的结构 `Core`）。它包含：SGA4 式的公理 A1 到 E2，其中包括下降、基变换、Artin 消没、射影丛公式、Hensel 不变性与正常基变换；以及 ind-平展映射的平展基变换。它还有 $bb(A)^1$-同伦不变性，以及严格 henselian 基上 Laurent 多项式上同调的消没。由这些，对每个 $cal(O)_K$ 上的光滑模型 $X$（#ref[输入定理 7.3] 的记号），得到结构 `EtSide`：
  (i) 每个 $V^j$ 是 $QQ_l$ 上的有限维空间；
  (ii)（Poincaré 对偶）若 $X$ 有相对维数 $d$ 的连通分支，则 $i > 2d$ 时 $V^i = 0$，且对 $i + j = 2d$，最高群 $V^(2d)$ 由有限多个向量 $g_s$ 张成（在伽罗瓦作用下差非零标量置换），而泛函 $x arrow.bar ⟨x union y⟩$（与整水平类 $y$ 的杯积）张成整个 $(V^i)^∨$（`Model.Dual`）；
  (iii) $X$ 有一个由连通片构成的有限覆盖，它在每个次数上检测消没。
]

#lean("UpperTheory.Gal.KunnethLefschetz.core_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/KunnethLefschetz/CoreHolds.lean")
#lean("UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/KunnethLefschetz/EtSideGoodHolds.lean")

结构 `EtSide` 在 `.../BocksteinBaseChange/EtSide.lean`（`PadicHodgeComparison` 下）。

库如何证明它。叶子分两处。文件夹 `Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology`（79 个文件）证明公理 A1、…、E2。文件夹 `Development/EtaleCohomology`（1,398 个文件、约 100k 行）容纳大型叶子开发：平展层（688 个文件）、上同调纯性（202）、Tate 扭曲（239）、Kummer 理论（98）、除子循环（56）与平展迹（70）。纯性被打包为 `UpperTheory.Et.purAll`。`KunnethLefschetz` 文件夹（顶层 44 个文件、2,981 行；连同子文件夹 142 个文件、10,916 行）是胶水：它装配 `Core` 并由它导出对偶与有限性命题。[用到 #ref[输入定理 7.1]]

#caution("7.6")[
  这是一个公理化理论（叶子已证），不是带任意系数系统的任意概形的一般平展上同调。Weil 猜想不在已证命题之列（见最后一小节）。所定义的 $V^n$ 与教科书上同调的吻合是按构造的（挠上同调的逆极限张 $QQ_l$），且未被独立核查。
]

== Arakelov 几何：Hilbert–Samuel、Moriwaki 与斜率不等式

这三个输入给出 #ref[第 5 节] 计数论证的两侧。

#env("输入定理", "7.7", "nef 丛的算术 Hilbert–Samuel")[
  设 $k$ 是交换环，$X$ 是整概形，$p : X arrow.r "Spec" k$ 是相对维数 $D$ 的算术簇。设 $L$、$N$ 是 $X$ 上的厄米线丛，$L$ 为 nef（`IsNef D`）、自相交数 $a in RR$（`IsSelfInter a`）。则对所有大 $m$，$L^m ⊗ N$ 的小截面之集有限，且
  $ log {#"smallSec"}(L^m ⊗ N) - a/((D + 1)!) m^(D + 1) = o lr(m^(D + 1)) quad (m arrow.r oo). $
]

#lean("GlobalTheory.Published.ArithHilbertSamuel", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/SmallSecTensTriv.lean")

它被证明为 `arithHilbertSamuel_of_principalisation`，把 `Published.Principalisation` 映到 `Published.ArithHilbertSamuel`。

#lean("GlobalTheory.arithHilbertSamuel_of_principalisation", "Development/AbelianVarietyTheory/Proofs/DivisorProofs/ArithHilbertSamuelOfPrincipalisation.lean")

库如何证明它。证明有三部分：ample 情形（`ampleArithHilbertSamuel_of_principalisation`）、一个半正拉回步骤（`semiPull_of_principalisation`）、以及一个算术相交演算（`arCalc_of_principalisation`）。ample 情形是 Zhang 的算术 Hilbert–Samuel。#inferred[从 ample 到 nef 的一步用一个 ample 丛扰动 nef 丛，如 Moriwaki 那样。]理想的主化经由 `principalisation_closed` 进入，那是光滑射影 $Y$ 的 #ref[输入定理 7.1]。所以 Hironaka 是体积估计的直接祖先。Arakelov 演算依赖 Poincaré–Lelong 公式（见下）。渐近式在两个方向都被使用：斜率下界用“许多小截面”，上界用“少量小截面”。[用到 #ref[输入定理 7.1]]

#env("输入定理", "7.8", "名为 MoriwakiBigStatement 的命题")[
  在库的图（chart）语言中，设 $cal(A)$ 是维数 $D + 1$ 的多射影算术簇上的厄米线，由域 $Omega$ 上的坐标 $y$ 给出（$y$ 双有理）。假设 $cal(A)$ 相对一个理想 $P_0 subset.eq m_y$ 半正、共轭不变，且在纤维与一般纤维上 nef。设 $II$ 是任意相交系统，即任何满足公理 `IsIntersectionSystem` 的配对。则
  $ II lr(cal(A)^(D + 1)) <= "arVol" lr("small sections of" cal(A)), $
  右边是小截面格的算术体积，正规化为 $tau^(D + 1)\/(D + 1)!$。
]

#lean("ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement", "ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/MoriwakiSt.lean")

该定理是 `PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright`。

#lean("PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright", "Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/MoriwakiBigTheorem/Outright.lean")

#caution("7.9")[
  名字有误导性。该命题不是大性的判据。它是算术 Siu 型下界“对 nef 丛体积 ≥ 自相交”，即算术 Hilbert–Samuel 的下半部分。同一文件中的同伴 `MoriwakiHSStatement` 说小截面的正规化计数趋于相交数；它多一个假设 `HeightsNonneg`。环境对象是一个抽象公理化的相交系统，其存在性是另一条定理（`ArithIntersectionSystemStatement`）。
]

库如何证明它。`moriwakiBig_of_classicalTheorems` 取三个输入，三个都是库中的定理：`resK`（#ref[输入定理 7.1] 的 Hironaka 推论）、相交系统由 `poincareLelong` 的存在性、以及 `DenseCurves.main`。后者是一个“大量小点存在”的命题：对多射影 $PP$，存在常数 $C$ 与一个高度至多 $C$ 的算术曲线（代数点的闭包）的 Zariski 稠密集。其证明很短（60 行）：$QQ$ 上的 Noether 正规化与环面中单位根的稠密性。主链 `hsChain` 约有 180 步。[用到 #ref[输入定理 7.1]]

#env("输入定理", "7.10", "欧氏格的斜率不等式")[
  设 $E$、$F$ 是有限维实内积空间，$L subset.eq E$、$M subset.eq F$ 是非零离散 $ZZ$-子模（其张成中的格）。置 $deg L = -log "covol" L$、$"slope" L = deg L \/ "rk" L$、而 $mu_max M = "sup"{"slope" N : 0 eq.not N <= M}$。若 $phi : L arrow.r M$ 是单射 $ZZ$-线性映射，且对一切 $x in L$ 有 $norm(phi x) <= C norm(x)$，则
  $ "slope" L <= mu_max M + log C. $
]

#lean("Formalism.F.SlopeInequality", "Formalism/LatticeSlopes/Statement.lean")

它由 `slopeInequality_of` 从 `SlopeLeMuMax`（`slopeLeMuMax`）证明。

#lean("Formalism.F.slopeInequality_of", "Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean")

#caution("7.11")[
  没有声明叫“Bost”。这是 Bost 斜率不等式的欧氏格形式。它没有 $cal(O)_K$ 上的厄米丛。$cal(O)_K$ 版本在别处经由对数余体积 $"lcv" X = 2\/[K : QQ] log "ht" X$ 处理，带因子 $2\/[K : QQ]$。一个更一般的、在带 Harder–Narasimhan 数据（`muMin`、`muMax`）的环 $R$ 上的版本是 `Formalism.HarderNarasimhan.SlopeIneq`（`Formalism/HarderNarasimhan/Statement.lean`）。估计引擎使用另一条同样名为 `SlopeIneq` 的加权平均命题（`Formalism/RankGapBounds/MeanBoundSecondForm.lean`）：$s - log abs(W) - (1 - delta)^(-1) (4 u_F log(1 + H\/u_F) + (eta + 4 sqrt(e)) H) <= mu_"CC"$。那条是围绕着上述不等式的簿记。
]

库如何证明它。#inferred[论证是古典的。]像 $phi(L)$ 是 $M$ 的同秩子格。界 $norm(phi x) <= C norm(x)$ 用 $C^("rk" L) "covol" L$ 控制其余体积（Lean 引理 `norm_sum_smul_le_of_int` 与 Gram 行列式）。于是 $"slope" L <= "slope" phi(L) + log C <= mu_max M + log C$。

== 解析数论输入

#env("输入定理", "7.12", "分圆塔中类群 l-秩的界，名为 FerreroWashington")[
  设 $l$ 是素数，$K$ 是 $QQ$ 上的阿贝尔数域，含 $l$ 次本原单位根（$l = 2$ 时为 4 次）。则存在 $r in NN$，使得对每个 $n$ 与每个由 $l^n$ 次单位根对 $K$ 作的分圆扩张所得的 $K'$，
  $ \# lr("Cl"(cal(O)_(K')) \/ l dot.op "Cl"(cal(O)_(K')) ) <= l^r. $
]

#lean("UpperTheory.V.FW.ferreroWashington", "Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean")

命题是 `UpperTheory.V.Published.FerreroWashington`（`.../AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean`）。

#caution("7.13")[
  Lean 命题界定类群中 $l$ 次幂的指数，即 $l$-秩，沿塔一致。它没有陈述 Iwasawa 模的 $mu = 0$，也没有说 $\# "Cl"$ 的增长。#inferred[沿分圆 $ZZ_l$-塔秩的有界性正是下游窗口论证所需的较弱形状。]它用于在拼合章（#ref[第 6 节]）中经由 `thmBab_of_lemmaK` 得到 `ThmBab`。
]

库如何证明它。文件夹 `FerreroWashingtonIndex` 有 62 个文件、4,672 行。证明项很短。#inferred[它把 $K'$ 嵌入一个受控次数 $D l^n_0$ 的更大分圆域（`embed`），把分圆层中 $l$ 次幂的指数用一个常数 $B$ 界定（`cyc`），再从大域下降到 $K'$（`desc`）。]最终常数是 $D l^n_0 B$，而 $r$ 取为使其 $l^r$ 高于它。

#env("输入定理", "7.14", "Siegel 定理")[
  对每个 $epsilon > 0$ 存在 $c > 0$，使得对每个 $q >= 1$ 与每个满足 $chi^2 = 1$、$chi eq.not 1$ 的模 $q$ 狄利克雷特征 $chi$：
  （`SiegelLower`）$abs(L(1, chi)) >= c q^(-epsilon)$；
  （`ExcBound`）只要 $L(beta, chi) = 0$、$beta in RR$，就有 $beta <= 1 - c q^(-epsilon)$。
  常数 $c = c(epsilon)$ 是非实效的。
]

#lean("Formalism.ZeroFreeDirichlet.siegelLower", "Formalism/LandauZeroFreeBounds/FinalSiegel.lean")
#lean("Formalism.ZeroFreeDirichlet.excBound", "Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean")

命题在 `Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean`（`SiegelLower`）与 `.../LogDerivRegionChiOf.lean`（`ExcBound`）。`excBound` 的证明是 `.../SiegelWalfiszAPOfSiegelLower.lean` 中的 `excBound_of_siegelLower`。

库如何证明它。`siegelLower` 是 `siegel_theorem_of` 应用于七个输入：乘积特征的存在性（`exists_product_character`）、实非平凡特征的存在性、关键界 `bqKey`、$L(1, chi)$ 的上界、$zeta$ 在实轴一部分上的负性、$L$ 在实轴上的实性、以及同一特征的 $L(1, chi) = L(1, chi')$。#inferred[这些是经典论证的原料，用 $zeta L(s, chi_1) L(s, chi_2) L(s, chi_1 chi_2)$。]带 $q <= (log x)^A$ 的级数中的 Siegel–Walfisz 定理（`siegelWalfisz`）由它推出。

#env("输入定理", "7.15", "带一个例外零点的无零点区域与 Deuring–Heilbronn 排斥")[
  记 `IsExc`(c₁, χ, β) 为：$chi^2 = 1$、$1 - c_1\/log M < beta < 1$、且对诱导 $chi$ 的本原特征有 $L(chi_"prim", beta) = 0$。（de la Vallée Poussin 与 Landau–Page。）存在 $c_0 > 0$，使得对每个 $0 < c_1 <= c_0$ 存在 $c > 0$，对每个 $M >= 3$ 具有以下性质。
  (a) 至多存在一个数对 $(chi, beta)$（$chi$ 为模 $M$ 的特征）满足 `IsExc`(c₁, χ, β)。
  (b) 对这样的数对：$chi eq.not 1$、$beta >= 7\/8$、$L(chi, beta) = 0$ 且为零点（单零点）、且 $1 - beta >= c\/(M^2 log M)$。
  (c) $L(s, chi)$ 的每个满足 $Re rho < 1$ 的零点 $rho$ 要么是那个例外零点（$Im rho = 0$ 且 `IsExc`(c₁, χ, Re ρ)），要么满足
  $ Re rho <= 1 - c\/log(M (abs(Im rho) + 2)). $

  （Deuring–Heilbronn。）存在 $c > 0$，使得对所有 $q$、所有满足 $chi_1 eq.not 1$、$chi_1^2 = 1$ 且有实零点 $beta in [1\/2, 1)$ 的 $chi_1$、所有特征 $chi$ 与满足 $1\/2 <= Re rho < 1$ 且（$(chi, rho) eq.not (chi_1, beta)$ 或 $beta$ 为重零点）的零点 $rho$、以及所有 $L >= log(q(abs(Im rho) + 2))$：
  $ (c log(c\/((1 - beta) L)))\/L <= 1 - Re rho. $
]

#lean("GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion", "Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegionStatement.lean")
#lean("GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion", "Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RepulsionStatement.lean")

#caution("7.16")[
  这里的例外零点界 $1 - beta >= c\/(M^2 log M)$ 是 Landau–Page 强度。它远弱于 Siegel 的（#ref[输入定理 7.14]），后者另行陈述。所有常数都是非实效的。这些命题中任何地方都不使用黎曼型假设（在解析文件夹中 grep GRH 与 RiemannHypothesis 只会找到最终定理文件）。
]

库如何证明它。两者都经由 `GlobalTheory.ExceptionalPair.main` 与 `GlobalTheory.Lin.Repulsion.repulsion` 证明。#inferred[路线是标准的 Landau 论证：一个关于圆盘中全纯函数零点的局部引理（`LandauLocal3`）、$L$ 的增长界、以及一个 Turan 型幂和引理。]单模的无对数零密度估计 $sum_chi N(sigma, T, chi) <= C(q T)^(A(1 - sigma))$ 在 `LogFreeZeroDensityDirichletOneModulus`（412 行）中证明。连同上述两条命题，它给出带相对误差项的算术级数素数定理（`primesRel_holds`）与指数未指定的 Linnik 定理（`SmallOne`）。初等计数 `ZeroDensityBox` 是另一个估计，用缓和子与对偶不等式从零证明，指数为 $Q^(1\/4)$；见 #ref[定理 3.18]。文件夹 `Formalism/GL3MeanSquares`（440 个文件、约 78k 行）容纳其中大部分。[用到 #ref[定理 3.18]]

== Hodge 丛包

#env("输入定理", "7.17", "PublishedHodgeBundleTheorems")[
  这是 `Prop` 中的一个 Lean 结构，有 28 个字段，每个都是 `GlobalTheory.Published` 命名空间的经典定理。
]

#lean("GlobalTheory.CovTop.PublishedHodgeBundleTheorems", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/ToKnownTheoremsOf.lean")

它作为假设穿过了体积章的数百条定理，但最终不被假设。定理 `published_results_arithmetic` 从结构 `OpenLiteratureStatements` 构造它：每个字段用一个定理 `*_of_literature` 填充。

#lean("UpperTheory.LiteratureTheorems.published_results_arithmetic", "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean")

字段列于 #ref[表 1]。另外三个事实（`p18`、`q2`、`q12`：厄米类的有限性、典范扩张的秩一、正常相交的长度）由具名定理从该结构导出。

#caution("7.18")[
  大多数字段是通常命题，有些在较窄的设定中。环向紧化（`p1`）在数域上陈述。整模型来自 Siegel 整模型（`SiegelToroidalIntegral`）与 12 行的胶水 `toroidalCharts_of_siegel_of_forFan`。强逼近（`p13`）是带分裂幂等支撑条件的厄米设定。三个字段 Green series（`p14`）、棱柱 Dieudonné（`q4`）与 $L^2$ 延拓（`q8`）最不易识别，在下一小节描述。
]

结构如何被兑现。`published_results_arithmetic` 形如 `p1 := toroidal_compactification_of_literature O`，每个字段依此类推。唯一参数是 `O : OpenLiteratureStatements`，它只有三个字段：Caraiani 的局部—整体相容性、局部 Langlands 存在性命题 `RecTExists`、以及一个极化数对的伽罗瓦表示。三者都在伽罗瓦一侧，且都不被 Hodge 丛链使用。在顶层，`O` 本身由 `MainConclusion.lean` 构造为 $⟨h, "recTExists", h⟩$，其中 $h$ 由 theta 提升构造（#ref[定理 4.26]）证明。所以 Hodge 丛一侧没有开放输入。典型链条：`q6` 来自 `kawamataViehweg_of_nadelVanishingPair`；`q16` 来自 `principalisation_closed`；`q9`、`p2`、`p3` 来自 `arithHilbertSamuel_of_principalisation`。[用到 #ref[输入定理 7.1]、#ref[输入定理 7.7] 与 #ref[定理 4.26]]

== 其他输入，简述

每一项都是一个在库中有证明的 Lean `Prop`。路径相对于 `src` 根。

- Kawamata–Viehweg。在特征 0 的 $k = bar(k)$ 上，对光滑射影整的 $X$（典范丛 $K$，$N$ nef 且大）：$q > 0$ 时 $H^q (X, K ⊗ N) = 0$。仅线丛，无 $QQ$-除子。经由 Nadel 消没证明（约 197 个文件、9.9k 行）。
  #lean("GlobalTheory.Published.KawamataViehweg", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/KawamataViehweg.lean")

- Poincaré–Lelong。在带有限全纯图册的紧空间与带简单正规交叉除子 $sum_k m_k W_k$ 的截面 $s$ 上：$integral_v Phi dif d^c log abs(s) = sum_k m_k integral_(W_k) Phi - integral_v c_1(L) Phi$。由图陈述与单位分解证明；算术形式 `PoincareLelongInv` 来自七个叶子定理。
  #lean("poincareLelong", "ReciprocityTheory/AnalyticForms/PotentialTheory/PLLocalStatement.lean")

- Zarhin 技巧。带相对 ample $L$ 的阿贝尔概形 $cal(A)$（在赋值环上、位于代数闭域内）是主极化者的收缩。仅赋值环基。
  #lean("GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement", "Development/AutomorphicSpectrum/PublishedTheorems/AlgebraâĆĆ/ZarhinStatement.lean")

- Grothendieck–Messing。对幂零分幂加厚 $R arrow.r R_0$：晶体等于带容许滤过的 de Rham，对象与态射像滤过那样提升。对阿贝尔概形，不是一般 $p$-可除群。
  #lean("GlobalTheory.Published.GrothendieckDeformation", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/GrothendieckDeformation.lean")

- Deligne–Ribet。对全实 $F$ 与一个模 $l^n$、在与 $l$ 互素的理想上 $l$-整的 $QQ$-值射线类函数 $epsilon$：$r - N c^k r' in ZZ_l$，其中 $r$、$r'$ 是 $L(epsilon)$、$L(epsilon^c)$ 在 $1 - k$ 处的值。仅 $QQ$-值 $epsilon$ 与 $l$-幂模。证明约 390 行（射线类群与 Chebotarev）。
  #lean("GlobalTheory.Published.DeligneRibet", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/SiegelKlingenDeligneRibet.lean")

- $U(p, q)$ 的离散序列。Harish-Chandra 按符号与严格递减的整参数的分类，带唯一最低 K-型。构建了两次（`CompanionTheory/RealGroups` 中约 6k 行，`ReciprocityTheory/ReductiveGroups/DiscreteSeries` 中约 150k 行）。
  #lean("CompanionTheory.RgExh.dsExhaust", "CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/DsExhaust.lean")

- $"GL"_n$ 的局部逆定理。在特征 0 的非阿基米德局部域上，与 $"GL"_m$ 的一切不可约表示有相同 $epsilon$-因子的 $"GL"_(m+1)$ 尖点不可约表示同构。
  #lean("DiscreteGroups.sglob.LConv.localConverseGL", "Development/DiscreteGroups/GlobalIrreducibility/LConvFinal.lean")

- Ohsawa–Takegoshi 型延拓。带常数 $34\/delta$ 的 Demailly 形式，来自带给定图册与曲率假设的紧空间上的一个有限零点集，不是在 Stein 流形上。支撑文件夹 `L2DbarEstimates`：约 220 个文件、33k 行。
  #lean("GlobalTheory.Published.L2ExtensionLogCanonical", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/L2ExtensionLogCanonical.lean")

- $"GL"_N (FF_g)$ 的 Green 特征。对素数 $g$（不是素数幂），从 $f(0) eq.not 0$ 的首一 squarefree $N$ 次多项式到类函数的一个单射，每个都是维数为 $product_(i <= N) (g^i - 1)\/abs(T_f)$ 的 generic 单模的特征。
  #lean("GlobalTheory.Published.GreenSeriesSt", "Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/GreenSeriesSt.lean")

- 棱柱 Dieudonné（最弱的命题）。在 $cal(O)_C$ 上，一个从 $p$-可除群到秩为高、带 Frobenius、沿 $theta$ 的约化、自然 Hodge 序列 $0 arrow.r omega_G arrow.r D(G) arrow.r "Lie"(G^"vee") arrow.r 0$ 的自由 $A_"inf"$-模函子，在 $QQ_p\/ZZ_p$ 与 $mu_(p^oo)$ 上取标准值，外加一个唯一性条款。只有这种函子的存在性，没有完全忠实性或本质满射性。它是 Hodge–Tate 正合性（Fargues）所需的，由一个 Zink 窗口论证证明。
  #lean("GlobalTheory.Published.PrismaticDieudonneHodge", "Development/AbelianVarietyTheory/PublishedTheorems/DivisorsâĆĆ/InjectiveOfSmulMemRange.lean")

- Berger 定理（de Rham 蕴含潜在半稳定）。`DeRhamPotSemistable`：对每个有限 $K\/QQ_ell$ 与 $G_K$ 的每个连续有限维 de Rham 表示，它是潜在半稳定的。库由 `pAdicMonodromyTheorem_matrixForm` 导出它。它是 `LiteratureAutomorphyHypothesis` 的一个字段，并被 `vwin_of_row` 使用。#inferred[我们未读这个证明。]
  #lean("GlobalTheory.Published.DeRhamPotSemistable", "Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicFormsâĆĆ/DeRhamPotSemistable.lean")

- Chowla–Selberg 与 Kronecker 极限公式。在 `GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg` 中完全证明（约 58 个文件、5.5k 行）。CM 周期是 $gamma + log(2 pi\/sqrt(d)) - L'\/L(1, chi_(-d))$；见 #ref[定理 5.23]。
  #lean("GlobalTheory.T.chowla_selberg_period", "Development/AutomorphicSpectrum/Proofs/GeometryProofs/ChowlaSelbergPeriodStatement.lean")

== 未证明且未使用

库中出现两个命题但未被兑现，且主链中没有任何地方使用它们。

- Weil 猜想（`EWeil.Goal`，在 `WeilConjectures/FermatCount.lean` 中）。它说：对有限域上维数 $d$ 的光滑射影 $X$，$H^n$ 有限维，且每个 Frobenius 特征值 $alpha$ 满足 $abs(alpha)^2 = q^n$。弱变体（`WeakAt`：$log_q abs(alpha)^2 in [n - 3, n + 3]$，即 $abs(alpha)^2 in [q^(n - 3), q^(n + 3)]$）、Künneth、Gysin 与超曲面计数被定义，有些片段被证明（Leray、Artin 消没、Gysin、纯性）。`Goal` 以一个假设 `Base` 为条件。对全树的 grep 没有找到类型为 `EWeil.Goal` 的定理，也没有找到其文件夹之外的任何使用。
- 半稳定比较 $C_"st"$（`CstNarrow`、`SemistableModelSemistable`、`DeRhamComparisonSemistable`）。定理 `narrow_of` 由若干假设推出 `CstNarrow`；其中两个，`BstRegularPeriodRing` 与 `SeamAll`，在树中任何地方都未被证明。文件 `CrystallineTowers/CrystallinePeriodsOfSmooth.lean` 导入了 `SemistableModelSemistable.lean` 却不使用它。`narrow_of` 从未被应用。任何人说本库证明了 $C_"st"$ 都是错的。

同样未使用的：`TateHonda`（两个证明文件导入它，但没有声明引用它）。#inferred[我们未逐一核查其他 `Published` 命题，故不对它们作出断言。]

两个看起来未使用、其实被使用的命题。`HeckeEntire_holds` 出现在 `Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalFormToricRatio.lean` 与 `Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRatRepr.lean` 中。`NefBigIff` 作为 `NefNumerics` 的一部分被使用。

#heading(numbering: none, outlined: false)[本章传递什么]

后续各章可以引用以下内容。

- #ref[输入定理 7.1]，连同 #ref[输入定理 7.7]、#ref[输入定理 7.8]、#ref[输入定理 7.10]，是体积章（#ref[第 5 节]）的几何输入。
- #ref[输入定理 7.17] 是被贯穿余体积界的经典事实包。
- #ref[输入定理 7.3] 与 #ref[输入定理 7.5] 是伽罗瓦构造（#ref[第 6 节]）的晶体与 Hodge–Tate 条款的输入。
- #ref[输入定理 7.12] 用于拼合章的窗口论证。
- #ref[输入定理 7.14]、#ref[输入定理 7.15]用于素数一侧（#ref[第 3 节]）。
