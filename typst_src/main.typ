// main.typ —— 主文件
#import "lib.typ": *

#set document(
  title: "Lean 中的黎曼猜想：Alpöge 证明的一份人类可读蓝图",
  author: "Z.ai",
  keywords: ("黎曼猜想", "Lean", "Mathlib", "Riemann Hypothesis"),
)

#set page(
  paper: "a4",
  margin: (x: 2.4cm, y: 2.5cm),
  numbering: "1",
)

#set text(
  font: ("New Computer Modern", "SimSun"),
  size: 10.5pt,
  lang: "zh",
  region: "cn",
  cjk-latin-spacing: auto,
)
#set par(justify: true, leading: 0.68em, spacing: 0.9em)

#set heading(numbering: "1.1")
#show heading: it => {
  set text(font: ("New Computer Modern", "Microsoft YaHei"), weight: 700, fill: black)
  it
}
#show heading.where(level: 1): it => { set text(size: 14pt); v(1.2em); it; v(0.55em) }
#show heading.where(level: 2): it => { set text(size: 12pt); v(0.9em); it; v(0.4em) }

#set list(indent: 1.2em, body-indent: 0.55em, spacing: 0.65em, marker: [•])
#set enum(indent: 1.2em, body-indent: 0.55em, spacing: 0.65em)
#show raw: set text(font: ("DejaVu Sans Mono", "SimSun"), size: 9.3pt)
#show link: set text(fill: linkcolor)

#include "ch0_front.typ"
#include "ch1.typ"
#include "ch2.typ"
#include "ch3.typ"
#include "ch4.typ"
#include "ch5.typ"
#include "ch6.typ"
#include "ch7.typ"
#include "appA.typ"
