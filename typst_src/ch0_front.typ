// ch0_front.typ —— 扉页与目录
#import "lib.typ": *
#align(center)[
  #text(size: 17pt, weight: 700, font: zhhei)[Lean 中的黎曼猜想：] \
  #v(0.15em)
  #text(size: 17pt, weight: 700, font: zhhei)[Alpöge 证明的一份人类可读蓝图]
  #v(0.9em)
  #text(size: 11pt)[依据 Lean 源码编写，2026 年 11 月]
  #v(0.5em)
  #text(size: 11pt)[2026 年 11 月 24 日草稿]
]

#v(0.6em)

#align(center)[#text(size: 12pt, weight: 700, font: zhhei)[摘#h(1em)要]]

#block(spacing: 0.8em)[
  2026 年 11 月 20 日，Levent Alpöge（与 Claude 合作）发布了黎曼猜想的 Lean 4 证明，以及狄利克雷 L 函数的广义黎曼猜想（GRH）。该证明经机器检验，但仅以 1700 万行代码的形式存在。本文档是该证明的一份蓝图：它按这些内容在代码中出现的样子精确地陈述主要定义与结果，概述各自的证明，并指出证实它们的 Lean 声明。大体上，证明用 Landau 方法把 RH 归约为：辅助 CM 域上一个正的、经特征扭曲的素数计数满足某个单侧界。该界的证明方式是：对酉群之间的约 $sqrt(x)$ 个 theta 提升逐一写出同一计数，用算术相交理论从两侧夹住模形式格的余体积，再用乘积公式把余体积化为 $log p$ 之和。一个 Vandiver 型的伽罗瓦上同调界——它借助来自志村簇的伽罗瓦表示与 Taylor–Wiles 拼合证明——控制住那个唯一可能破坏计数的项。正确性由 Lean 代码保证；本文只为帮助理解。
]

#v(0.6em)
#outline(depth: 2, title: [目#h(1em)录])
#v(0.5em)
