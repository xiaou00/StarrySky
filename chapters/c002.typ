#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= 意象 / Topoi

== Grothendieck的几何哲学

拓扑空间上的层依赖两样东西: 开集组成的范畴 $Open(X)$, 以及哪些开集族应当被视为覆盖. 前者决定信息可以沿哪些方向限制, 后者决定何时一族局部信息足以代表整体. Grothendieck 的关键观察是, 层论真正使用的正是这两项范畴化的数据, 而不一定需要先给出一个点集空间.

这一推广分成三步:

$
"覆盖结构" -> "景" -> "景上的层范畴"
$

覆盖结构把「局部」公理化; 带有覆盖结构的范畴称为景; 景上的集合值层组成 Grothendieck 意象. 本书后文将*Grothendieck 意象* (Grothendieck topos) 简称为*意象*.

=== 纤维积角度: 用覆盖族描述局部性

设 $C$ 是一个范畴. 对象 $u in C$ 上的一个*覆盖族* 是一族具有共同目标的态射

$
cal(V)={f_i:u_i->u}_(i in I)
$

它应当被想成普通拓扑中的开覆盖 ${U_i subset U}_(i in I)$. 为了使这种直觉在任意范畴中成立, 必须把开覆盖最基本的三个性质抽象出来.

#definition(title:[Grothendieck 预拓扑])[
  假设 $C$ 具有下面用到的纤维积. 一个*Grothendieck 前拓扑* (Grothendieck pretopology) 为每个对象 $u in C$ 指定一类覆盖族 $"Cov"(u)$, 并满足:

  -*同构覆盖*: 若 $f:v->u$ 是同构, 则单元素族 ${f:v->u}$ 覆盖 $u$.

  -*基变换稳定性*: 若 ${f_i:u_i->u}_(i in I)$ 覆盖 $u$, 且 $g:v->u$ 是任意态射, 则纤维积 $u_i times_u v$ 存在, 并且

    $
    {u_i times_u v -> v}_(i in I)
    $

    覆盖 $v$.

  -*传递性*: 若 ${f_i:u_i->u}_(i in I)$ 覆盖 $u$, 并且对每个 $i$ 都有覆盖族 ${g_(i j):v_(i j)->u_i}_(j in J_i)$, 则复合族

    $
    {f_i compose g_(i j):v_(i j)->u}_(i in I,j in J_i)
    $

    覆盖 $u$.
]

这三条公理分别是「一个局部模型可以覆盖自己」「覆盖拉回后仍是覆盖」以及「局部的局部仍然是局部」. 其中纤维积扮演普通拓扑中交集的角色. 若 $u_i->u$ 与 $u_j->u$ 属于同一个覆盖族, 那么

$
u_i times_u u_j
$

就是两块局部对象的重叠部分.

#definition(title:[覆盖族版本的景与层])[
  带有上述覆盖族结构的范畴称为一个*景* (site). 若集合值预层 $cal(F):C^opp->Set$ 对每个覆盖族 ${u_i->u}_(i in I)$ 都使下图成为等化子图,

  $
  cal(F)(u) -> product_(i in I) cal(F)(u_i)
  ⇉
  product_((i,j) in I times I) cal(F)(u_i times_u u_j)
  $

  就称 $cal(F)$ 是这个景上的层. 两条平行箭头分别把 $u_i$ 与 $u_j$ 上的截面限制到纤维积 $u_i times_u u_j$.
]

这正是前面 Čech 等化子的逐字推广. 原先的开集交被纤维积替代, 「局部截面在交集上相等」则变成「两个拉回到纤维积的截面相等」. 因此纤维积版本很适合直接进行粘合计算.

=== 筛角度: 用所有进一步限制描述覆盖

一个覆盖族只列出第一层局部对象. 但只要 $f:v->u$ 是其中一块, 那么任何经由 $f$ 到达 $u$ 的态射 $w->v->u$ 都应当仍属于这块局部信息.*筛*把一个覆盖族连同它的所有进一步限制一次性收集起来.

#definition(title:[筛])[
  设 $u in C$. $u$ 上的一个*筛* (sieve) 是可表预层 $h_u=Hom_C (-,u)$ 的一个子预层

  $
  cal(R) subset h_u
  $

  具体地, 对每个 $v in C$, 集合 $cal(R)(v) subset Hom_C (v,u)$ 由一批以 $u$ 为目标的态射组成, 并且对预复合封闭: 若 $f:v->u$ 属于 $cal(R)(v)$, 且 $g:w->v$, 则

  $
  f compose g:w->u
  $

  属于 $cal(R)(w)$.
]

若 $f:v->u$ 是态射, $cal(R)$ 是 $u$ 上的筛, 则它沿 $f$ 的拉回筛 $f^* cal(R)$ 定义为

$
(f^* cal(R)) (w):={g:w->v:f compose g in cal(R)(w)}
$

这个定义只使用态射复合, 不需要事先选取纤维积. 最大筛 $h_u$ 包含所有以 $u$ 为目标的态射, 对应「$u$ 被自身完全覆盖」.

#definition(title:[筛版本的 Grothendieck 拓扑])[
  范畴 $C$ 上的一个*Grothendieck 拓扑* $J$ 为每个对象 $u in C$ 指定一族筛 $J(u)$, 其中的元素称为 $u$ 上的*覆盖筛*, 并满足:

  - *最大筛覆盖*: $h_u in J(u)$.

  - *基变换稳定性*: 若 $cal(R) in J(u)$ 且 $f:v->u$, 则 $f^* cal(R) in J(v)$.

  - *局部性*: 设 $cal(R) in J(u)$, 而 $cal(S)$ 是 $u$ 上的任意筛. 若对每个 $f:v->u$ 且 $f in cal(R)(v)$, 拉回筛 $f^* cal(S)$ 都属于 $J(v)$, 则 $cal(S) in J(u)$.

  二元组 $(C,J)$ 称为一个*景*.
]

第三条公理可以读成: 若 $cal(R)$ 已经覆盖 $u$, 而 $cal(S)$ 在 $cal(R)$ 的每一块上都局部覆盖, 那么 $cal(S)$ 本身覆盖 $u$. 它正是覆盖族传递性的无坐标版本.

筛还给出了层条件更内在的表达. 对覆盖筛 $cal(R) subset h_u$, 包含映射诱导限制

$
Map_(PSh(C)) (h_u,cal(F))
->
Map_(PSh(C)) (cal(R),cal(F))
$

左侧由 Yoneda 引理等同于 $cal(F)(u)$. 因而 $cal(F)$ 是景 $(C,J)$ 上的层, 当且仅当对每个覆盖筛 $cal(R) in J(u)$, 上述映射都是双射. 直观地说, 一个定义在覆盖筛全部局部箭头上、并与进一步限制相容的截面族, 能且只能以一种方式延拓到整个可表预层 $h_u$.

=== 覆盖族与覆盖筛的对应

给定一族态射 $cal(V)={f_i:u_i->u}_(i in I)$, 它生成的筛 $cal(R)_cal(V)$ 由所有能够经过某个 $f_i$ 分解的态射组成. 也就是说, $g:v->u$ 属于这个筛, 当且仅当存在 $i in I$ 与态射 $h:v->u_i$ 使得

$
g=f_i compose h
$

一个 Grothendieck 前拓扑由此生成一个 Grothendieck 拓扑: 宣布筛 $cal(R)$ 覆盖 $u$, 当且仅当它包含某个覆盖族生成的筛. 在所需纤维积存在时, 反过来也可以把一族态射称为覆盖族, 当且仅当它生成的筛是覆盖筛.

#remark(title:[为什么筛更内在])[
  同一个覆盖筛可能由不同的覆盖族生成, 不同的前拓扑也可能给出完全相同的覆盖筛与层. 覆盖族适合计算, 因为纤维积直接写出二重交; 筛则忘掉生成元的选择, 只保留「哪些态射在局部上已经足够」. 因此 Grothendieck 拓扑在概念上通常用筛定义, 实际验证层条件时则常回到覆盖族.
]

=== 普通拓扑空间如何包含在其中

现在回到拓扑空间 $X$. 取范畴 $C=Open(X)$, 对象是开集, 态射是包含映射. 对 $U_i,V subset U$, 范畴中的纤维积正是开集交:

$
U_i times_U V=U_i inter V
$

声明包含族 ${U_i->U}_(i in I)$ 是覆盖族, 当且仅当

$
U=union_(i in I) U_i
$

前拓扑的三条公理此时分别变成: $U$ 覆盖自身; 若 ${U_i}$ 覆盖 $U$, 则 ${U_i inter V}$ 覆盖 $V$; 若每个 $U_i$ 又被 ${V_(i j)}_j$ 覆盖, 那么所有 $V_(i j)$ 一起覆盖 $U$. 这些恰好是普通开覆盖的基本性质.

从筛的角度看, $U$ 上的筛就是一族对取更小开集封闭的开子集. 这样的筛是覆盖筛, 当且仅当它所包含的全部开集之并等于 $U$. 因此景 $Open(X)$ 上的层条件, 精确退化为前面定义的拓扑空间上的层条件.

#remark(title:[推广的真正含义])[
  Grothendieck 拓扑不是在范畴的对象集合上再放一个点集拓扑. 它推广的是「什么叫局部覆盖」: 开子集被一般态射替代, 交集被纤维积替代, 对更小开集封闭的开集族被筛替代. 层论依赖的限制与粘合机制因此可以离开具体的点集空间而继续成立.
]

=== Grothendieck 意象

#definition(title:[Grothendieck 意象])[
  若一个范畴 $cal(E)$ 等价于某个小景 $(C,J)$ 上的集合值层范畴,

  $
  cal(E) tilde.eq Sh(C,J)
  $

  就称 $cal(E)$ 是一个*Grothendieck 意象* (Grothendieck topos), 简称*意象*.
]

#remark(title:[一个意象可以有多种景表示])[
  可能存在两个底层范畴和覆盖结构都不同的景 $(C,J)$ 与 $(D,K)$, 但它们的层范畴彼此等价:

  $
  Sh(C,J) tilde.eq Sh(D,K)
  $

  此时两个景表示同一个意象. 因此景不是意象唯一确定的组成部分, 而是描述意象的一套局部坐标; 真正内在的对象是层范畴本身及其范畴结构.
]

景 $(C,J)$ 是意象的一种表示: 它给出可用于计算的局部对象、覆盖与限制映射. 意象 $Sh(C,J)$ 则是所有满足粘合条件的层所组成的范畴. 可以把两者的关系概括为

$
"景" (C,J) -> "意象" Sh(C,J)
$

这正如同一个几何对象可以有不同的坐标图册. 景保留一套具体的局部坐标, 意象则保留由全部层共同表达的内在局部几何. 到这里先停在定义层面; 后续真正讨论下降与叠时, 再逐步使用这些结构.

从这一观点看, 景只是空间的一种表示,*意象才是摆脱具体表示之后的空间本身*. 因而现代代数几何的基本研究单位不再是点集或覆盖数据, 而是承载全部局部对象及其粘合关系的意象. 更准确地说, 还需在意象 $cal(E)$ 上配备结构层 $cal(O)$, 以二元组 $(cal(E),cal(O))$ 同时保存空间的局部逻辑与函数论.

== 1-Giraud 定理

以下固定一个小景 $(C,J)$, 并记

$
cal(E):=Sh(C,J)
$

再记 $i:cal(E)->PSh(C)$ 为包含函子, $a:PSh(C)->cal(E)$ 为层化函子. 我们先借助景的表示证明 Grothendieck 意象具有一系列类似 $Set$ 的正合性质, 最后再说明这些性质反过来足以刻画 Grothendieck 意象.

#proposition(title:[完备、余完备与左正合层化])[
  Grothendieck 意象 $cal(E)$ 有所有小极限与小余极限. 对任意小范畴 $K$ 和图式 $cal(D):K->cal(E)$, 有

  $
  i (lim_(cal(E)) cal(D))
  tilde.eq
  lim_(PSh(C)) (i compose cal(D))
  $

  $
  colim_(cal(E)) cal(D)
  tilde.eq
  a (colim_(PSh(C)) (i compose cal(D)))
  $

  此外, 层化函子 $a$ 保持有限极限, 即它是一个*左正合* (left exact) 局部化.
]

#proofsketch[
  预层范畴是函子范畴, 所以极限与余极限都能在每个 $u in C$ 上逐点计算. 层条件本身是一组极限条件: 相容局部截面组成等化子, 更内在地说, 对覆盖筛 $cal(R) subset h_u$ 要求

  $
  Map(h_u,cal(F)) -> Map(cal(R),cal(F))
  $

  为双射. 极限与极限可以交换, 因而一族层在预层范畴中的极限仍是层, 这给出第一条公式.

  预层的逐点余极限未必满足粘合, 所以还要施加一次层化. 由 $a$ 对 $i$ 的左伴随泛性质, 层化后的预层余极限正好满足 $cal(E)$ 中余极限的泛性质, 得到第二条公式.

  最后, 标准的加号构造用覆盖筛上的相容族构造 $cal(F)^+$, 再迭代得到层化. 在验证有限个截面之间的等式时, 可以把有限多个覆盖共同细化到同一个覆盖上; 而集合中的滤过余极限与有限极限交换. 因而这一构造保持终对象与纤维积, 也就保持所有有限极限.
]

#proposition(title:[切片仍是 Grothendieck 意象])[
  对任意对象 $s in cal(E)$, 切片范畴

  $
  cal(E) slash s
  $

  仍是一个 Grothendieck 意象.
]

#proofsketch[
  由 $s$ 构造一个新的小景 $(C_s,J_s)$. 它的对象是二元组 $(u,sigma)$, 其中 $u in C$ 且 $sigma in s(u)$. 从 $(v,tau)$ 到 $(u,sigma)$ 的态射是满足

  $
  tau=s(f) (sigma)
  $

  的态射 $f:v->u$, 覆盖族则由 $C$ 中的覆盖族诱导.

  一个层态射 $x->s$ 在每个 $(u,sigma)$ 上给出映射 $x(u)->s(u)$ 在 $sigma$ 上的纤维; 这些纤维随限制映射组成 $(C_s,J_s)$ 上的层. 反过来, 把所有 $sigma in s(u)$ 上的纤维作不交并, 就重新得到一个带有映射到 $s$ 的层. 两个构造互逆, 因而

  $
  cal(E) slash s
  tilde.eq
  Sh(C_s,J_s)
  $
]

#proposition(title:[Cartesian 闭性与局部 Cartesian 闭性])[
  对任意 $x,y in cal(E)$, 存在指数对象 $y^x$, 满足对每个 $t in cal(E)$ 都有自然同构

  $
  Hom_cal(E) (t,y^x)
  tilde.eq
  Hom_cal(E) (t times x,y)
  $

  更强地, 每个切片 $cal(E) slash s$ 都是 Cartesian 闭的, 所以 $cal(E)$ 是*局部 Cartesian 闭* (locally Cartesian closed) 的.

  对态射 $f:x->y$, 拉回函子 $f^*:cal(E) slash y->cal(E) slash x$ 同时拥有左伴随 $Sigma_f$ 与右伴随 $Pi_f$:

  $
  Sigma_f tack.l f^* tack.l Pi_f
  $
]

#proofsketch[
  指数对象可以先在景上写出. 对 $u in C$, 令

  $
  y^x (u)
  :=
  Hom_cal(E) (a(h_u) times x,y)
  $

  沿 $v->u$ 的限制由可表预层的反变性诱导. 一族这样的局部态射若在覆盖上相容, 便能逐个分量粘合成唯一的整体态射, 所以 $u |-> y^x (u)$ 是层. Yoneda 引理与层化的泛性质给出所需指数伴随同构.

  前一个命题说明每个 $cal(E) slash s$ 本身仍是层范畴, 对它重复同一构造便得到局部 Cartesian 闭性. 对 $f:x->y$, $Sigma_f$ 只是把 $z->x$ 与 $f$ 复合成 $z->y$; 它是 $f^*$ 的左伴随. 切片中的指数对象则给出 $f^*$ 的右伴随 $Pi_f$, 即依赖积.
]

#remark(title:[与依赖类型的联系])[
  在切片 $cal(E) slash y$ 中, 对象可以看成以 $y$ 为参数的一族对象. 此时 $Sigma_f$ 表示依赖和, $Pi_f$ 表示依赖积, 而拉回 $f^*$ 表示代入或换基. 因而局部 Cartesian 闭性正是意象能够解释依赖类型论的范畴论原因之一.
]

#proposition(title:[像分解、有效满射与有效等价关系])[
  任意态射 $f:x->y$ 都有像分解

  $
  x ->^e Im(f) ->^m y
  $

  其中 $e$ 是满射, $m$ 是单射. 每个满射都是*有效满射*: 若

  $
  pr_1,pr_2:x times_y x -> x
  $

  是它的核偶, 则

  $
  y tilde.eq Coeq(pr_1,pr_2)
  $

  更一般地, 每个内部等价关系 $r pairarrow x$ 都是有效的. 若 $q:x->Q$ 是它的商, 则

  $
  r tilde.eq x times_Q x
  $

  因而 Grothendieck 意象是 Barr-正合范畴.
]

#proofsketch[
  在预层范畴中, 像、核偶、等价关系与商都逐点在 $Set$ 中计算, 因而逐点有效. 对一个层态射, 先在预层范畴中取像或商, 再层化所得预层. 层化作为左伴随保持余等化子, 又因左正合而保持核偶与内部等价关系所需的有限极限. 因此层化后的商仍以原等价关系为核偶.

  像分解可由核偶的商构造. 若 $f$ 已经是满射, 它的像单射必为同构, 所以 $f$ 本身就是其核偶的余等化子. 这同时说明满射在任意换基后仍保持为满射, 是下降能够有效工作的基本机制.
]

#proposition(title:[余积不交且对换基稳定])[
  Grothendieck 意象中的小余积彼此不交. 对任意 $x,y in cal(E)$, 有

  $
  x times_(x coprod y) y tilde.eq 0
  $

  并且对任意态射 $t->x coprod y$, 典范态射

  $
  (t times_(x coprod y) x)
  coprod
  (t times_(x coprod y) y)
  ->
  t
  $

  是同构. 因而 $cal(E)$ 是一个广延范畴; 更一般的小余积也具有同样的不交性与换基稳定性.
]

#proofsketch[
  在预层范畴中, 余积逐点退化为集合的不交并, 所以不同分支的纤维积为空, 而一个映到不交并的集合恰好分解为各分支原像的不交并. $cal(E)$ 中的余积由预层余积再层化得到. 层化同时保持余积、初对象与纤维积, 因而上述两个集合层面的同构经过层化后仍为同构.
]

#proposition(title:[所有余极限都是普遍的])[
  对任意态射 $f:t->s$, 换基函子

  $
  f^*:cal(E) slash s -> cal(E) slash t
  $

  保持所有小余极限. 等价地, 若 ${x_i}_(i in I)$ 是 $cal(E) slash s$ 中的图式, 则

  $
  f^* (colim_(i in I) x_i)
  tilde.eq
  colim_(i in I) f^* x_i
  $

  因而称 Grothendieck 意象中的余极限是*普遍的* (universal).
]

#proofsketch[
  局部 Cartesian 闭性说明 $f^*$ 存在右伴随 $Pi_f$. 因此 $f^*$ 本身是一个左伴随, 而左伴随保持所有余极限. 这里必须在切片范畴中理解余极限, 这正好表达了「先粘合再换基」与「先换基再粘合」给出相同结果.
]

#proposition(title:[滤过余极限与有限极限交换])[
  设 $I$ 是滤过范畴, $K$ 是有限范畴, 而 ${x_(i k)}$ 是 $cal(E)$ 中以 $(i,k) in I times K$ 为指标的图式. 则自然态射给出同构

  $
  colim_(i in I) lim_(k in K) x_(i k)
  tilde.eq
  lim_(k in K) colim_(i in I) x_(i k)
  $

  也就是说, Grothendieck 意象中的滤过余极限是正合的.
]

#proofsketch[
  在 $Set$ 中, 滤过余极限与有限极限交换; 预层范畴逐点计算, 所以同一结论先在 $PSh(C)$ 中成立. 在 $cal(E)$ 中计算余极限需要层化, 但层化 $a$ 保持有限极限. 因而

  $
  lim_(k in K) a (colim_(i in I) x_(i k))
  tilde.eq
  a (lim_(k in K) colim_(i in I) x_(i k))
  tilde.eq
  a (colim_(i in I) lim_(k in K) x_(i k))
  $

  最右端正是 $cal(E)$ 中相应的滤过余极限.
]

=== 小生成族与局部可呈示性

#proposition(title:[层化可表对象生成整个意象])[
  层化可表对象

  $
  {a(h_u)}_(u in C)
  $

  构成 $cal(E)$ 的一小族生成元. 也就是说, 若 $f,g:x->y$ 满足对每个 $u in C$ 和每个态射 $h:a(h_u)->x$ 都有

  $
  f compose h=g compose h
  $

  则 $f=g$. 此外, 每个 Grothendieck 意象都是局部可呈示范畴.
]

#proofsketch[
  层化伴随与 Yoneda 引理给出

  $
  Hom_cal(E) (a(h_u),x)
  tilde.eq
  Hom_(PSh(C)) (h_u,i(x))
  tilde.eq
  x(u)
  $

  若两个层态射 $f,g:x->y$ 不相等, 它们必在某个 $u in C$ 的某个截面上取值不同. 这个截面对应一个态射 $a(h_u)->x$, 它便能区分 $f$ 与 $g$. 因为 $C$ 小, 这些生成元确实只组成一个集合.

  预层范畴 $PSh(C)$ 是局部可呈示的. 层条件可以表示为对所有覆盖筛包含 $cal(R)->h_u$ 的局部性条件; 当 $C$ 小时, 这些态射也只组成一个集合. 因而层化是一个可达左正合局部化, 其局部对象组成的 $Sh(C,J)$ 仍是局部可呈示范畴.
]

#theorem(title:[1-Giraud 定理])[
  设 $cal(E)$ 是一个局部小范畴. 在通常的集合大小约定下, 下列条件等价:

  1. $cal(E)$ 是 Grothendieck 意象.

  2. $cal(E)$ 满足以下 Giraud 公理:

     - $cal(E)$ 有有限极限.

     - $cal(E)$ 有所有小余积, 并且这些余积彼此不交且对任意换基稳定.

     - $cal(E)$ 中每个内部等价关系都是有效的, 且其商对任意换基稳定.

     - $cal(E)$ 有一小族生成元.

]

#proofsketch[
  从第一条到第二条正是本节前面各命题的内容: 在预层范畴中, 相应性质逐点归结为 $Set$; 左正合层化再把这些性质传递给层范畴. 层化可表对象 ${a(h_u)}_(u in C)$ 则给出一小族生成元.

  反过来, 假设 $cal(E)$ 满足 Giraud 公理. 先选择一小族生成元, 并将它扩充为一个对有限极限封闭的小满子范畴 $C subset cal(E)$. 在 $C$ 上声明一族态射 ${u_i->u}$ 覆盖 $u$, 当且仅当诱导态射

  $
  coprod_i u_i -> u
  $

  是满射. 余积的普遍性与有效等价关系保证这些覆盖满足换基和传递公理, 因而定义一个 Grothendieck 拓扑 $J$.

  接着考虑限制 Yoneda 函子

  $
  N:cal(E) -> PSh(C),
  quad
  N(x) (u):=Hom_cal(E) (u,x)
  $

  有效满射的下降性质说明 $N(x)$ 对 $J$ 是层. 生成元保证 $N$ 忠实; 任意对象都能由生成元的余积满射覆盖, 再把这个满射的核偶取有效商, 可知自然变换能够唯一下降为 $cal(E)$ 中的态射, 所以 $N$ 还是全的.

  最后, 任意 $J$-层都可以先由可表层的余积满射覆盖. 对这个满射的核偶作商, 再在 $cal(E)$ 中用相同的余积和有效商实现该表示, 就得到一个对象 $x in cal(E)$, 使原层同构于 $N(x)$. 因而 $N$ 诱导等价

  $
  cal(E) tilde.eq Sh(C,J)
  $

  这便从纯粹内在的 Giraud 公理重新构造出了一个景表示.
]


