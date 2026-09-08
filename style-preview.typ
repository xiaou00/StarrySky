// Template specimen only; not included in the book.
#import "template.typ": *

#show: doc => conf(
  title: [Ex Nihilo],
  subtitle: [高阶代数几何主题 · 版式样张],
  author: "xiaou0",
  date: "2026",
  cover-image: "cover.png",
  doc,
)

= 前言 / 前置

== 对象与态射

研究一个数学对象时, 我们也关心它与其他对象之间的关系. 在范畴的语言中, 这些关系由态射描述. 本页展示正文、行内公式 $f: u -> v$、定义和证明在同一版面中的层次.

#definition(title: "范畴")[一个范畴 $C$ 由对象、态射以及态射的复合组成. 每个对象 $u$ 都有恒等态射 $id_u$, 而复合满足结合律与单位律.
$ (h compose g) compose f = h compose (g compose f) $
] <def-category>

#theorem(title: "恒等态射的唯一性")[对任意对象 $u$, 满足单位律的恒等态射唯一.] <thm-identity>

#proof[设 $e$ 与 $e'$ 都是对象 $u$ 的恒等态射. 由左右单位律可得
$ e = e compose e' = e' $
]

#example(title: "集合")[在范畴 $Set$ 中, 对象是集合, 态射是映射, 复合就是通常的映射复合.]

#remark[由 @def-category 可以写出复合的结合律. @thm-identity 说明, 恒等态射无需另作选择.]

=== 记号约定

用小写字母 $u, v, w$ 表示对象, 用 $Hom_C (u, v)$ 表示从 $u$ 到 $v$ 的态射集合.#footnote[本样张仅用于检查模板版式. 数学正文仍由各章文件维护.]

#quote[把对象放进它与其他对象的关系中, 往往能更清楚地看见它的结构.]

#pagebreak()
== 复合与交换图

图表与公式使用相同的留白尺度. 定理用深蓝色标记, 定义用青灰色标记; 例与注的边线更轻, 以便连续阅读.

#lemma[若 $f: u -> v$ 与 $g: v -> w$ 都是同构, 则 $g compose f$ 也是同构.]
#proofsketch[将 $f^(-1) compose g^(-1)$ 分别与 $g compose f$ 左右复合即可.]

#proposition[若 $f$ 可逆, 则其逆态射唯一.]
#proof[若 $g$ 与 $h$ 都是 $f$ 的逆态射, 则 $g = g compose (f compose h) = (g compose f) compose h = h$.]

#corollary[一个同构 $f$ 的逆态射也是同构, 且 $(f^(-1))^(-1) = f$.]

#figure(
  simplex2hollow($u$, $v$, $w$, ab: $f$, bc: $g$, ac: $g compose f$),
  caption: [复合对应的交换三角形.],
)

#figure(
  table(
    columns: (1fr, 1fr, 1fr),
    table.header([范畴], [对象], [态射]),
    [$Set$], [集合], [映射],
    [$Grp$], [群], [群同态],
    [$Top$], [拓扑空间], [连续映射],
  ),
  caption: [常见范畴的对象与态射.],
)

#part[范畴与结构]

= 从局部到整体

== 结构的组织

章节标题、部分扉页与页眉延续同一套视觉元素. 新章中的定理编号从头开始; 目录与交叉引用仍可点击跳转.

#axiom(title: "单位律")[对每个态射 $f: u -> v$, 有
$ id_v compose f = f = f compose id_u $
]

#theorem(title: "新章编号示例")[恒等态射的唯一性仍由单位律直接推出. 这里的计数从本章重新开始.] <thm-new-chapter>

#remark[可回到 @thm-identity 阅读同一论证. 本页的 @thm-new-chapter 用于确认章节编号与跳转位置.]

=== 阅读路径

- 先明确对象和态射, 再研究它们的复合.
- 从熟悉的集合、群与拓扑空间出发, 比较共同的结构.
- 遇到抽象定义时, 配合例子与交换图理解.

#quote[局部的描述给出线索, 相容的关系把它们联结起来.]

=== 问题与解答

#question[若 $f: u -> v$ 与 $g: v -> w$ 都是同构, 则 $g compose f$ 也是同构吗?]

#answer[是的, 将两个逆态射按相反的顺序复合, 就得到
$ (g compose f)^(-1) = f^(-1) compose g^(-1) $
]
