# 黎曼猜想 Lean 蓝图 · 中文译本

> 《Lean 中的黎曼猜想：Alpöge 证明的一份人类可读蓝图》中文译本
> 英文原版 2026-11-24 草稿 · 中文版 2026-11-25 校订

**[📄 下载 / 阅读中文 PDF](rh_lean_blueprint_v2_中文.pdf)**（66 页）

---

## 这是什么

2026 年 11 月 20 日，Levent Alpöge（与 Claude 合作）发布了黎曼猜想以及狄利克雷 L 函数广义黎曼猜想（GRH）的 Lean 4 形式化证明。该证明规模约 1740 万行，正确性由机器检验保证，但几乎没有面向人类读者的叙述。

本仓库是英文蓝图 *The Riemann Hypothesis in Lean: a human-readable blueprint of Alpöge's proof*（2026-11-24 草稿，76 页）的中文译本。中文版**以英文原版为底本，并依据 Lean 源码翻译整理**：逐节对译后，再把文中的定义、公式与 Lean 声明逐一核对；英文原版中与 Lean 不符、留有 `??` 占位符或交代不清的地方，按 Lean 源码补全或修正，并在校订记录中注明依据。

仓库包含：

- 中文 PDF（66 页，2026-11-25 校订版）
- 完整 Typst 源码，可重新编译
- 逐条校订记录（英文原版 + Lean 源码双重依据）

> **重要说明**：本仓库是翻译与学习资料，**不是**对黎曼猜想的原创证明，也**不构成**对 Lean 形式化项目的独立验证。证明本身以 Lean 源码和机器检验为准；本译本的整理与校订只核对公式、陈述与 Lean 声明是否一致，没有重跑构建、内核检查或 Mathlib 审计。

## 仓库内容

| 路径 | 说明 |
|---|---|
| `rh_lean_blueprint_v2_中文.pdf` | 中文译本，66 页 |
| `typst_src/` | Typst 源码：`main.typ`、`ch0_front.typ`–`ch7.typ`、`appA.typ`、`lib.typ` |
| `校订记录.md` | 逐条修改、位置与依据（对照英文原版与 Lean 声明） |
| `build.ps1` / `build.sh` | 一键重新编译 |
| `NOTICE.md` | 底本来源、权利与免责声明 |

## Lean 源码

本仓库不包含 Lean 源码。形式化证明由 Levent Alpöge 发布在 `alpo.ge`，公告 PDF 的脚注给出 14 个分片：

- 分片：[`lean.tar.gz.part01`](https://alpo.ge/lean.tar.gz.part01) … [`lean.tar.gz.part14`](https://alpo.ge/lean.tar.gz.part14)（共 14 片，合并后 239,275,554 字节）
- 公告：[`remark.pdf`](https://alpo.ge/remark.pdf)

合并与解压（Git Bash / Linux / macOS）：

```bash
for i in $(seq -w 1 14); do curl -O "https://alpo.ge/lean.tar.gz.part$i"; done
cat lean.tar.gz.part* > lean.tar.gz
tar -xzf lean.tar.gz
```

完整压缩包 SHA-256（2026-11-26 核对）：

```
9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc
```

> 源码包内未附 README 或 LICENSE 文件。源码权利归 Levent Alpöge；本仓库只引用其中的 Lean 声明用于校订，不再分发源码。转载或再分发请以官方发布为准并注明作者。

## 重新编译

依赖 [Typst](https://typst.app/) **0.15.1**。源码使用 Typst 内置的 `New Computer Modern`，中文部分使用 Windows 字体 `SimSun`、`Microsoft YaHei`、`KaiTi`。其他平台需安装相应字体，或修改 `typst_src/lib.typ` 与 `typst_src/main.typ` 中的字体列表。

Windows PowerShell：

```powershell
./build.ps1
```

Linux / macOS / Git Bash：

```bash
./build.sh
```

或手动：

```bash
cd typst_src
typst compile main.typ "../rh_lean_blueprint_v2_中文.pdf"
```

## 校订说明

中文版不是逐字直译：凡英文原版与 Lean 声明不一致、或原文只留下占位符之处，以 Lean 源码为准补全或修正。本版只改动会改变数学内容的错误，未改动论证结构。共 9 处实质修正、10 处公式/排版修正，例如：

- 定理 4.15：分段常数改回 $c=1\ (n<m)$、$c=2\ (n\ge m)$，与 Lean `HypothesesS.lean` 的 `if n < m then 1 else 2` 一致
- 定理 6.20：$\theta^j$ 改回 $\vartheta_j$，与 `PlaceData.lean` 一致
- 定义 6.25：$\mathbb F_g^\times$ 改回 $\mathbb F_{g^n}^\times$
- 第 4 章：补回漏写的 $e_z$（4 处）
- 修复四处 `??` 交叉引用、若干希腊字母与 Lean 名称笔误

逐条对照（位置、原文、改文、依据）见 **[校订记录.md](校订记录.md)**。

## 审校范围

- 以**英文原版 PDF + Lean 源码中的声明**为基准，核对 135 个编号陈述的数学内容与交叉引用。
- 未独立重跑构建、内核检查或 Mathlib 审计。原文第 1.2 节所述的认证状态，请以 Lean 项目及 Lean FRO / Mathlib Initiative 的公告为准。
- 英文原版自身有少量 `??` 占位符，以及 $8/2500$ 与同段文字“1/2500”的差异；中文按公式与 Lean 修正，并在校订记录中注明。

## 致谢

- **Levent Alpöge**：黎曼猜想与 GRH 的 Lean 4 证明（与 Claude 合作）。
- **Atulit Gaur（[@atulit_gaur](https://x.com/atulit_gaur)）**：英文蓝图 *The Riemann Hypothesis in Lean: a human-readable blueprint of Alpöge's proof*（2026-11-24 草稿）的作者，本译本的底本。
- **Lean / Mathlib 社区**：形式化基础设施。

## 许可

本译本采用 [CC BY 4.0](LICENSE) 许可：可自由转载、改编，包括商业用途，但须署名。

转载时请保留以下署名：英文蓝图作者 **Atulit Gaur（@atulit_gaur）**，以及本中文译本仓库。英文底本本身未附明确许可证，其权利归原作者；如原作者对本文译本有任何异议，请联系仓库维护者处理。

---

## English summary

A Chinese translation of *The Riemann Hypothesis in Lean: a human-readable blueprint of Alpöge's proof* (draft of 24 November 2026), together with the Typst source and a line-by-line correction log.

This is a study aid, **not** an original proof and **not** an independent verification of the Lean formalisation. Correctness rests on the Lean source and machine checking.
