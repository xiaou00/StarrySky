#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*
#import "../assets/retracts.typ": cylinder-retraction

#show: doc => conf(
  easy: true,
  doc,
)

= 收缩 / Retract <chap-retract>

本章从拓扑中的收缩讲起, 再转向范畴论中的收缩及其相关工具.

== 收缩的概念

收缩的拓扑直观是: 把整个空间连续地送回某个子空间, 并保持该子空间上的点不动. Borsuk 在 1931 年的 #emph[Sur les rétractes] 中已系统研究这类问题 @Bor31.

#definition(title: "拓扑空间的收缩")[
  设 $A subset X$ 是拓扑子空间, $i:A arrow.r.hook X$ 是包含映射. 若存在连续映射 $r:X->A$ 满足
  $ r compose i=id_A $
  则称 $A$ 是 $X$ 的*收缩子空间* (retract), 称 $r$ 为*收缩映射* (retraction).
] <def-topological-retract>

换句话说, $r$ 把 $A$ 上的恒等映射延拓到了整个 $X$. 从 $A$ 进入 $X$ 再回来, 一点信息也没丢; 但从 $X$ 出发再回来, 一般只得到 $i compose r$, 并不等于 $id_X$.

=== 圆柱侧面收缩到圆周

取圆柱的*侧面* $X=S^1 times [0,1]$, 以及它的下边界 $A=S^1 times {0}$. 沿竖直方向投影,
$ r:X->A, quad r(z,s)=(z,0) $
就得到收缩映射: 下边界上的点原本就在高度 $0$, 因而保持不动.

这个例子还可以把整个过程连续地演出来. 定义
$ H:X times [0,1]->X, quad H_t (z,s):=H((z,s),t)=(z,(1-t)s) $
这里 $t$ 是时间: $t=0$ 时保持原状, $t=1$ 时压到下边界, 中间每个点沿自己的竖直线向下移动.

#figure(
  cylinder-retraction(),
  caption: [圆柱侧面的形变收缩. 三幅图画的是 $H_t (X)$; 蓝色下边界始终固定, 圆柱不包含上下两个圆盘.],
) <fig-cylinder-retraction>

#definition(title: "形变收缩")[
  若收缩映射 $r:X->A$ 还能配上连续同伦 $H:X times [0,1]->X$, 满足
  $ H_0=id_X, quad H_1=i compose r, quad H_t (a)=a quad (a in A, t in [0,1]) $
  则称 $X$ *形变收缩*到 $A$.
]

这里要求全过程固定 $A$, 因而也称*强形变收缩* (strong deformation retraction). 参见 @Hat02[第 0 章, 第 3 页].

此时 $r compose i=id_A$, 而 $i compose r$ 同伦于 $id_X$, 所以 $A$ 与 $X$ 同伦等价. 这就是它在拓扑计算中的用处: 圆柱侧面的同伦群、同调群, 都可以转到圆周上计算.

=== 两个边界例子

#example(title: "收缩不一定是形变收缩")[
  任意非空空间 $X$ 都能收缩到其中一个选定的点 $a$: 取常值映射 $r(x)=a$ 即可. 所以圆周也有到一点的收缩.

  但圆周不能形变收缩到一点, 否则两者同伦等价, 与
  $ H_1 (S^1,ZZ)=ZZ, quad H_1 ({a},ZZ)=0 $
  矛盾. 也就是说, "存在一个收缩映射"与"能在原空间内部连续缩过去"是两个不同的要求.
]

#example(title: "圆盘不能收缩到边界")[
  闭圆盘 $D^2$ 没有到边界 $S^1$ 的收缩映射. 如果存在 $r$, 由 $r compose i=id_(S^1)$, 对第一同调取函子就会得到复合
  $ ZZ stretch(->)^(i_*) 0 stretch(->)^(r_*) ZZ $
  等于恒等映射, 但这个复合只能是零映射, 矛盾. 参见 @Hat02[推论 2.15].

  径向投影 $x |-> x/norm(x)$ 在去掉圆心的圆盘上确实是收缩; 难点恰好在圆心, 从不同方向靠近时像没有共同的极限, 所以不能连续补上.
]

=== 从拓扑走向范畴

现在可以问: 定义中为什么要预先写 $A subset X$? 其实, 只要给出两个拓扑空间和连续映射
$ A stretch(->)^i X stretch(->)^r A, quad r compose i=id_A $
就已经能找回这个子空间的图像.

首先, $i$ 自动是单射: 若 $i(a)=i(b)$, 两边作用 $r$ 就得到 $a=b$. 更进一步, 给像 $i(A) subset X$ 配上子空间拓扑, 则 $i:A->i(A)$ 的逆映射正是连续映射 $r|_(i(A))$. 所以 $i$ 把 $A$ *同胚地嵌入*了 $X$. 将 $A$ 与 $i(A)$ 识别后, $i$ 就变成包含映射, 而 $i compose r:X->i(A)$ 就是原来意义下的收缩.

例如在圆柱的例子里, 可以直接取抽象的圆周 $A=S^1$, 写成
$ i(z)=(z,0), quad r(z,s)=z, quad r compose i=id_(S^1) $
这与把 $A$ 写成下边界 $S^1 times {0}$ 描述的是同一个收缩结构. 因而, *包含关系由 $i$ 来表达, 返回后保持不变由 $r compose i=id_A$ 来表达*. 需要保留的是这对映射及其关系, 无须预先把 $A$ 指定成 $X$ 的一个字面子集.

#definition(title: "范畴中的收缩")[
  在普通范畴 $C$ 中, 若对象 $A,X$ 配有态射 $i:A->X$ 与 $r:X->A$, 满足
  $ r compose i=id_A, quad "i.e."quad (A -->^i X -->^r A) = id_A:A->A $
  就称 $A$ 是 $X$ 的一个*收缩对象* (retract). 称 $i$ 为*分裂单态射*, $r$ 为*分裂满态射*; $r$ 是 $i$ 的左逆, $i$ 是 $r$ 的右逆.
] <def-categorical-retract>

这些名称也能直接从等式看出来. 若 $i compose u=i compose v$, 左边再复合 $r$ 就得到 $u=v$, 所以 $i$ 是单态射; 同理 $r$ 是满态射. 在模范畴里, $M->M ⊕ N$ 的自然嵌入与 $M ⊕ N->M$ 的投影就是典型例子.

这个定义有两个立即可用的性质, 都只需要计算复合.

#lemma(title: "收缩关系具有传递性")[
  在同一个普通范畴中, 若 $A$ 是 $B$ 的收缩对象, $B$ 是 $C$ 的收缩对象, 则 $A$ 是 $C$ 的收缩对象.
] <lem-retract-transitive>

#proof[
  设两组收缩结构为
  $ A stretch(->)^i B stretch(->)^r A, quad r compose i=id_A $
  $ B stretch(->)^j C stretch(->)^s B, quad s compose j=id_B $
  将进入的映射与返回的映射分别复合, 得到
  $ A stretch(->)^(j compose i) C stretch(->)^(r compose s) A $
  而
  $ (r compose s) compose (j compose i)=r compose (s compose j) compose i=r compose i=id_A $
  因而这就是 $A$ 作为 $C$ 的收缩对象的结构.
]

#lemma(title: "任意函子都保持收缩")[
  对任意函子 $F:cal(C)->cal(D)$, 若 $A$ 是 $B$ 的收缩对象, 则 $F(A)$ 是 $F(B)$ 的收缩对象.
] <lem-functor-preserves-retract>

#proof[
  对收缩结构 $r compose i=id_A$ 应用 $F$, 就有
  $ F(r) compose F(i)=F(r compose i)=F(id_A)=id_(F(A)) $
  所以 $F(i),F(r)$ 给出所需的收缩结构.
]

这里只用到了函子保持复合与恒等态射, *不需要额外的正合性或保持极限、余极限的假设*. 上面的同调论证正是这个引理的一个应用.

#example(title: "张量积保持收缩")[
  对任意环同态 $R->S$, 若 $R$-模 $M$ 是 $N$ 的收缩对象, 则 $S ⊗_R M$ 是 $S ⊗_R N$ 的收缩对象. 具体地,
  $ (id_S ⊗ r) compose (id_S ⊗ i)=id_(S ⊗_R M) $
  即使 $S$ 不平坦, 这个等式仍然成立. 由于投射模是自由模的收缩, 而自由模基变换后仍自由, 这也解释了*任意基变换都保持投射模*.
]

#example(title: "两个方向的 Hom 都保持收缩")[
  设 $A stretch(->)^i B stretch(->)^r A$ 满足 $r compose i=id_A$. 对任意对象 $T$, 后复合给出集合的收缩
  $ Hom(T,A) stretch(->)^(i_*) Hom(T,B) stretch(->)^(r_*) Hom(T,A) $
  前复合也给出
  $ Hom(A,T) stretch(->)^(r^*) Hom(B,T) stretch(->)^(i^*) Hom(A,T) $
  第二行先把 $f:A->T$ 送到 $f compose r$, 再送到 $f compose r compose i=f$. 所以反变的 Hom 函子同样保持收缩, 只是两条结构映射交换了角色.
]

回到一组收缩结构 $i:A->X$, $r:X->A$, 令 $e=i compose r:X->X$, 则
$ e^2=i compose (r compose i) compose r=i compose r=e $
所以收缩自然产生*幂等态射* (idempotent morphism): 做一次与做两次效果相同. 反过来问一个幂等态射能否来自这样的 $i,r$, 就引出了后面要讨论的幂等分裂.
