// lib.typ —— 共用样式与构件
#let Re = math.op("Re")
#let Im = math.op("Im")
#let linkcolor = rgb("#1e6bb8")
#let grayc = rgb("#8a8a8a")
#let zhsong = ("New Computer Modern", "SimSun")
#let zhhei = ("New Computer Modern", "Microsoft YaHei")
#let zhkai = ("New Computer Modern", "KaiTi")
#let zmono = ("DejaVu Sans Mono", "SimSun")

// 交叉引用（蓝色）
#let ref(body) = text(fill: linkcolor, body)
// 推断标记（灰色斜体）
#let inferred(body) = text(fill: grayc, style: "italic")[（推断：#body）]
// 证明末尾的“用到……”标记
#let used(items) = text(size: 8.5pt, fill: grayc)[［用到 #items］]

// 定理环境主体：黑体标签 + 楷体正文
#let env(label, num, name, body) = block(spacing: 1.05em, breakable: true)[
  #strong[#label #num]#if name != none [（#emph(name)）]#h(0.28em)
  #text(font: zhkai)[#body]
]

#let thm(num, name, body) = env("定理", num, name, body)
#let defn(num, name, body) = env("定义", num, name, body)
#let lem(num, name, body) = env("引理", num, name, body)
#let prop(num, name, body) = env("命题", num, name, body)
#let cor(num, name, body) = env("推论", num, name, body)
#let rem(num, name, body) = env("注", num, name, body)
#let caution(num, body) = env("注意", num, none, body)

// 证明环境：末行右侧墓碑符号
#let proof(body, uses: none) = block(spacing: 1em, breakable: true)[
  #strong[证明.]#h(0.35em)#body
  #if uses != none [ #used(uses)]
  #h(0.55em, weak: false)#box($□$)
]

// Lean 指针：声明 + 文件路径
#let lean(..items) = {
  let arr = items.pos()
  block(spacing: 0.75em)[
    #set text(size: 9pt, font: zmono)
    #strong[Lean:] #raw(arr.first())
    #for p in arr.slice(1) [\
      #h(1.8em) #raw(p)
    ]
  ]
}
