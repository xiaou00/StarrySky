#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*
#import "../assets/retracts.typ": cylinder-retraction

#let Idem = cat("Idem")

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

== 幂等性

"幂等"的意思是: *做一次之后, 再做就不再改变结果*. 在环或幺半群中, 这写作 $e^2=e$; 在范畴中, 只需把乘法换成态射的复合. 本节先在普通范畴中讨论.

=== 幂等态射

#definition(title: "幂等态射")[
  设 $X$ 是范畴 $cal(C)$ 的对象. 若自态射 $e:X->X$ 满足
  $ e compose e=e $
  就称 $e$ 为*幂等态射* (idempotent endomorphism), 也把这份数据记为 $(X,e)$. 参见 @Ker26[Tag 03ZF].
] <def-idempotent-morphism>

由结合律, 所有正次幂都相同:
$ e^n=e quad (n>=1) $
例如, $id_X$ 总是幂等的; 但一个幂等态射若可逆, 就只能是 $id_X$, 因为可以在 $e^2=e$ 两边消去一个 $e$.

#example(title: "投影为什么幂等")[
  在模 $M ⊕ N$ 上, 定义
  $ e:M ⊕ N->M ⊕ N, quad e(m,n)=(m,0) $
  第一次已经把第二个分量清零, 第二次操作就没有新的影响. 这正是先投影到 $M$, 再嵌回 $M ⊕ N$ 所产生的幂等态射.

  更一般地, 对集合上的幂等映射 $e:X->X$, 有
  $ e(X)={x in X | e(x)=x} $
  因为像中的元素 $e(x)$ 满足 $e(e(x))=e(x)$, 而每个不动点 $x=e(x)$ 又属于像. 所以可以把它想成: 一次操作便把点送到一块固定不动的部分.
]

集合或模中可以直接谈这个"像". 在一般范畴里, 我们先保留 $e^2=e$ 这份数据; 它所对应的那块部分能否由范畴中的一个对象表示, 正是幂等分裂要回答的问题.

=== 把幂等性编码成范畴: $Idem$

上一节把收缩写成一张图表. 幂等态射也可以这样处理: 用一个很小的范畴, 记录一个对象、一条自态射, 以及这条自态射必须满足的关系.

#definition(title: [范畴 $Idem$])[
  定义普通范畴 $Idem$ 如下: 它只有一个对象 $*$, 态射集为
  $ Hom_(Idem) (*,*)={id_*,epsilon} $
  其中 $epsilon != id_*$, 复合由恒等律和 $epsilon compose epsilon=epsilon$ 确定. 即
  $ id_* compose id_*=id_*, quad id_* compose epsilon=epsilon compose id_*=epsilon, quad epsilon compose epsilon=epsilon $
  它称为*万有幂等范畴* (walking idempotent). 参见 @Ker26[Tag 03ZN].
] <def-walking-idempotent>

这确实是一个范畴: 任意一串态射中, 只要出现 $epsilon$, 复合就是 $epsilon$; 否则就是 $id_*$. 因而括号放在哪里都不影响结果, 结合律自动成立. 也可以说, $Idem$ 是把两元素幺半群 ${1,epsilon}$ 看成的单对象范畴.

#proposition(title: [$Idem$ 的泛性质])[
  对任意普通范畴 $cal(C)$, 给出函子 $F:Idem->cal(C)$, 恰好等于给出对象 $X in cal(C)$ 及其上的幂等态射 $e:X->X$. 对应关系是
  $ F(*)=X, quad F(epsilon)=e $
  参见 @Ker26[Tag 03ZP].
] <prop-idem-universal>

#proof[
  函子必须保持复合, 因而
  $ e compose e=F(epsilon) compose F(epsilon)=F(epsilon compose epsilon)=F(epsilon)=e $
  反过来, 给定 $e^2=e$, 令 $F(*)=X$, $F(epsilon)=e$, $F(id_*)=id_X$, 就得到唯一的函子: 唯一需要检验的非恒等复合, 正是 $e^2=e$.
]

这里允许 $F(epsilon)=id_X$: 函子可以把不同的态射送到同一条态射. 因而恒等态射也包含在这个泛性质中.

=== 幂等态射之间的态射

于是, 函子范畴 $Fun(Idem,cal(C))$ 可以看作 $cal(C)$ 中的*幂等态射范畴*. 它的对象是 $(X,e)$. 两个对象 $(X,e)$ 与 $(Y,f)$ 之间的态射, 就是一条使下式成立的态射 $u:X->Y$:
$ u compose e=f compose u $
这恰好是自然变换在 $epsilon$ 上的自然性条件: 先在 $X$ 上操作再送到 $Y$, 与先送到 $Y$ 再操作, 结果一致. 恒等态射上的自然性则自动成立.

因此 $Idem$ 负责给出幂等图表的形状, 而 $Fun(Idem,cal(C))$ 才收集了 $cal(C)$ 中所有具体的幂等态射及其相容映射.

== 幂等态射的分裂

前面从收缩得到幂等态射 $e=i compose r$. 现在反过来: 已知 $X$ 上的 $e$, 能否找到一个对象 $A$, 让 $e$ 表现为"先送到 $A$, 再放回 $X$"? 这就是分裂问题. 以下仍在普通范畴中讨论.

=== 分裂就是找出收缩对象

#definition(title: "幂等态射的分裂")[
  设 $e:X->X$ 是幂等态射. 它的一个*分裂* (splitting) 是对象 $A$ 连同态射
  $ X stretch(->)^r A stretch(->)^i X $
  满足
  $ i compose r=e, quad r compose i=id_A $
  若存在这样的数据, 就称 $e$ *可分裂*. 参见 @Ker26[Tag 03ZH].
] <def-split-idempotent>

第一个等式要求复合恢复原来的 $e$; 第二个等式保证 $A$ 上的信息完整保留. 所以, 分裂就是把幂等态射所描述的那块部分实现成一个收缩对象. 仅仅分解 $e=i compose r$ 还不够, 两个等式必须同时成立.

#example(title: "集合与拓扑空间中的分裂")[
  对集合上的幂等映射 $e:X->X$, 取 $A=e(X)$, 令 $i$ 为包含映射, $r(x)=e(x)$, 只是把陪域改为 $A$. 因为 $e$ 在自己的像上是恒等映射, 所以 $r compose i=id_A$, 而 $i compose r=e$.

  若 $X$ 是拓扑空间且 $e$ 连续, 给 $A$ 配上子空间拓扑, 同样的构造仍然成立. 因此集合和拓扑空间中的每个幂等态射都可分裂.
]

#example(title: "模中的分裂就是直和分解")[
  对 $R$-模 $M$ 上的幂等态射 $e$, 取 $A=im(e)$, 便得到一个分裂. 还可以取出另一部分 $B=ker(e)$, 得到同构
  $ M tilde.eq im(e) ⊕ ker(e), quad m |-> (e(m),m-e(m)) $
  逆映射是 $(a,b) |-> a+b$. 这里 $m-e(m)$ 确实属于核, 因为 $e(m-e(m))=e(m)-e^2 (m)=0$. 在这个分解下, $e$ 就是 $(a,b) |-> (a,0)$.

  所以在模论中, 幂等态射可以用来识别直和因子; 一般范畴中的分裂定义则只需要态射和复合.
]

=== 分裂的唯一性

#lemma(title: "分裂唯一到相容的唯一同构")[
  若 $(A,i,r)$ 与 $(A',i',r')$ 是同一个幂等态射 $e:X->X$ 的两个分裂, 则存在唯一的同构 $u:A->A'$ 满足
  $ i' compose u=i, quad u compose r=r' $
  它及其逆映射分别为
  $ u=r' compose i, quad u^(-1)=r compose i' $
] <lem-idempotent-splitting-unique>

#proof[
  先注意 $e compose i=i$ 与 $r' compose e=r'$. 因而上述 $u$ 满足两个相容等式. 令 $v=r compose i'$, 则
  $ v compose u=r compose (i' compose r') compose i=r compose e compose i=r compose i=id_A $
  同理 $u compose v=id_(A')$. 最后, 若 $w:A->A'$ 满足 $i' compose w=i$, 则
  $ w=r' compose i' compose w=r' compose i=u $
  故同构也唯一.
]

这里的唯一性包含了与 $i,r$ 的相容性. 因此, 一旦 $e$ 可以分裂, 它就已经确定了相应的收缩对象, 无须再任意挑选一块"像".

=== 用等化子检验分裂

集合中, $e$ 的像恰好是不动点集合. 在一般范畴中, "取出不动的部分"由 $e$ 与 $id_X$ 的等化子表达.

#proposition(title: "分裂与等化子、余等化子")[
  对幂等态射 $e:X->X$, 下列条件等价:

  + $e$ 可分裂.
  + 态射对 $(e,id_X):X pairarrow X$ 有等化子.
  + 态射对 $(e,id_X):X pairarrow X$ 有余等化子.

  若 $(A,i,r)$ 给出分裂, 则 $i:A->X$ 正是这个等化子, $r:X->A$ 正是这个余等化子. 参见 @Ker26[Tags 03ZK, 03ZL].
] <prop-idempotent-splitting-equalizer>

#proof[
  *从分裂出发.* 有 $e compose i=i$. 对任意满足 $e compose f=f$ 的态射 $f:T->X$, 它通过 $i$ 的分解必然且确实是
  $ f=i compose (r compose f) $
  唯一性来自 $r compose i=id_A$: 若 $f=i compose g$, 就有 $g=r compose f$. 这正是等化子的泛性质.

  同样, 有 $r compose e=r$. 若 $h:X->T$ 满足 $h compose e=h$, 则它通过 $r$ 的唯一分解为 $h=(h compose i) compose r$, 所以 $r$ 是余等化子.

  *从等化子出发.* 设 $i:A->X$ 是 $(e,id_X)$ 的等化子. 因为 $e compose e=e$, 泛性质给出 $r:X->A$ 使得 $i compose r=e$. 又有
  $ i compose (r compose i)=e compose i=i $
  等化子 $i$ 是单态射, 因而 $r compose i=id_A$. 余等化子的情形在对偶范畴中同理.
]

这也给出了实际寻找分裂的方法: 构造 $(e,id_X)$ 的等化子, 再用它的泛性质恢复 $r$.

#corollary(title: "任意函子保持分裂及其泛性质")[
  若 $(A,i,r)$ 分裂 $e$, 则对任意函子 $F:cal(C)->cal(D)$, $(F(A),F(i),F(r))$ 分裂 $F(e)$. 因此上述等化子与余等化子都被任意函子保持.
]

#proof[
  函子保持两个分裂等式, 这与 @lem-functor-preserves-retract 是同一个计算. 再对 $F(e)$ 应用 @prop-idempotent-splitting-equalizer 即可.
]

所以这里即使 $F$ 一般不保持极限或余极限, 也仍然保持这两个特殊的构造.

=== 幂等完备的范畴

#definition(title: "幂等完备")[
  若普通范畴 $cal(C)$ 中的每个幂等态射都可分裂, 就称 $cal(C)$ *幂等完备* (idempotent-complete).
] <def-idempotent-complete-ordinary>

由 @prop-idempotent-splitting-equalizer, *有所有等化子, 或有所有余等化子的范畴, 都幂等完备*. 参见 @Ker26[Tag 03ZM]. 特别地, 集合、拓扑空间和 $R$-模的范畴都幂等完备, 前面的例子也给出了它们的显式分裂.

#example(title: [$Idem$ 自己并不幂等完备])[
  考察其中的幂等态射 $epsilon$. 若它可分裂, 由于 $Idem$ 只有对象 $*$, 两条分裂映射 $i,r$ 都只能取 $id_*$ 或 $epsilon$.

  但 $r compose i=id_*$ 强迫 $r=i=id_*$, 从而 $i compose r=id_* != epsilon$, 矛盾. 所以 $epsilon$ 在 $Idem$ 中没有分裂.
]

这个例子说明, 幂等关系本身并不保证所需的收缩对象已经在范畴里. 最后一节给出一个重要的代数实例: 从自由模出发, 加入它们的收缩对象, 就得到了投射模.

== 投射模: 自由模的收缩

以下 $R$ 是含幺交换环, 所有模都是普通 $R$-模. 我们从一个实际问题出发: 已知模的满射, 什么样的模允许我们把映射提升到满射之前?

=== 提升性质与等价刻画

#definition(title: "投射模")[
  称 $R$-模 $P$ 为*投射模* (projective module), 若对每个满射 $q:M->N$ 和每个同态 $f:P->N$, 都存在同态 $tilde(f):P->M$ 使
  $ q compose tilde(f)=f $
  即下图总能补出虚线箭头:

  #align(center)[
    #book-diagram(
      spacing: 25pt, cell-size: 0pt, node-inset: 5pt,
      {
        fletcher.node((0, 0), $P$)
        fletcher.node((-1, 1), $M$)
        fletcher.node((1, 1), $N$)
        fletcher.edge((0, 0), (1, 1), label: $f$, label-side: left, marks: "->")
        fletcher.edge((-1, 1), (1, 1), label: $q$, label-side: right, marks: "->>")
        fletcher.edge((0, 0), (-1, 1), label: $tilde(f)$, label-side: right,
          marks: "->", dash: "dashed")
      },
    )
  ]
] <def-projective-module>

提升只要求存在, 一般不唯一. 自由模很容易做到这一点: 对每个基向量, 挑选它的像在 $M$ 中的一个原像, 再线性延拓即可.

#theorem(title: "投射模的等价刻画")[
  对 $R$-模 $P$, 下列条件等价:

  + $P$ 是投射模.
  + $Hom_R (P,-)$ 是正合函子.
  + 每个以 $P$ 结尾的短正合列 $0->K->M->P->0$ 都分裂, 即满射 $M->P$ 有右逆.
  + $P$ 是某个自由模的收缩对象. 等价地, 存在 $Q$ 和集合 $I$, 使
    $ P ⊕ Q tilde.eq R^((I)), quad R^((I)):=⊕_(alpha in I) R $
  + $P$ 同构于某个自由模 $F$ 上幂等态射 $e:F->F$ 的像.

  参见 @Stacks26[第 10.77 节].
] <thm-projective-characterizations>

#proof[
  *$(1) <=> (2)$.* $Hom_R (P,-)$ 总是左正合: 一个映射被送到零, 恰好意味着它唯一地通过相应的核分解. 因而正合性只差一件事: 对满射 $q:M->N$, 映射
  $ Hom_R (P,M)->Hom_R (P,N) $
  必须满射. 这正是提升性质.

  *$(1)=>(3)$.* 将 $id_P$ 沿 $q:M->P$ 提升, 得到 $s:P->M$ 且 $q compose s=id_P$. 识别 $K=ker(q)$ 后, 分裂对应的同构及其逆为
  $ K ⊕ P->M, quad (k,p) |-> k+s(p) $
  $ M->K ⊕ P, quad m |-> (m-s(q(m)),q(m)) $

  *$(3)=>(4)$.* 取自由模满射 $q:F->P$, 例如用 $P$ 的所有元素作一组生成元. 对 $0->ker(q)->F->P->0$ 应用 $(3)$, 就得到 $F tilde.eq ker(q) ⊕ P$.

  *$(4)=>(1)$.* 设 $P stretch(->)^i F stretch(->)^r P$ 满足 $r compose i=id_P$, 且 $F$ 自由. 对 $q:M->N$ 和 $f:P->N$, 先把 $f compose r:F->N$ 提升为 $g:F->M$. 令 $tilde(f)=g compose i$, 则
  $ q compose tilde(f)=q compose g compose i=f compose r compose i=f $

  *$(4) <=> (5)$.* 给定收缩, 令 $e=i compose r$, 就有 $e^2=e$ 且 $im(e)=i(P) tilde.eq P$. 反过来, 幂等态射给出前面已经证明的分解 $F tilde.eq im(e) ⊕ ker(e)$.
]

这个证明说明了投射模为什么与收缩有关: 自由模上可以逐个基向量作提升, 而收缩结构把这个提升传回 $P$.

#example(title: "一个不投射的模")[
  对整数 $n>=2$, $ZZ slash n ZZ$ 不是投射 $ZZ$-模. 否则满射 $ZZ->ZZ slash n ZZ$ 有右逆 $s$. 但 $s(overline(1))$ 被 $n$ 消去, 在 $ZZ$ 中只能为零, 不可能再映回 $overline(1)$.
]

=== 有限生成: 幂等矩阵与对偶基

#theorem(title: "有限生成投射模的等价刻画")[
  对 $R$-模 $P$, 下列条件等价:

  + $P$ 有限生成且投射, 简称*有限投射模*.
  + 存在整数 $n>=0$ 和模 $Q$, 使 $P ⊕ Q tilde.eq R^n$.
  + 存在幂等矩阵 $e in op("Mat")_n (R)$, 满足 $e^2=e$ 且 $P tilde.eq im(e)$.
  + 存在有限多个 $p_j in P$ 和 $phi_j in Hom_R (P,R)$, 使
    $ p=sum_(j=1)^n phi_j (p)p_j quad (p in P) $

  最后一组数据称为*有限对偶基* (finite dual basis). 参见 @Stacks26[Tag 00NX] 中的有限自由直和因子刻画.
] <thm-finite-projective-characterizations>

#proof[
  *$(1)=>(2)$.* 由有限生成性选取满射 $r:R^n->P$, 再由投射性分裂它. 反过来, $R^n$ 的收缩对象既投射, 又由标准基的像有限生成, 所以 $(2)=>(1)$.

  *$(2)<=>(3)$.* 与上一定理完全相同: 从收缩取 $e=i compose r$, 从幂等矩阵取分解 $R^n tilde.eq im(e) ⊕ ker(e)$.

  *$(2)=>(4)$.* 设 $r compose i=id_P$, 记 $R^n$ 的标准基为 $b_1,dots,b_n$, 坐标函数为 $b_1^*,dots,b_n^*$. 取
  $ p_j=r(b_j), quad phi_j=b_j^* compose i $
  将 $i(p)$ 按标准基展开, 再作用 $r$, 就得到所需公式.

  *$(4)=>(2)$.* 直接定义
  $ i:P->R^n, quad i(p)=(phi_1 (p),dots,phi_n (p)) $
  $ r:R^n->P, quad r(a_1,dots,a_n)=sum_(j=1)^n a_j p_j $
  对偶基公式正是 $r compose i=id_P$, 因而给出收缩.
]

这里的 $p_j$ 不必线性无关; 重要的是有一组线性函数能够按上述公式重建每个元素. 对应的幂等矩阵可以直接写出:
$ e_(j k)=phi_j (p_k) $
它也给出实际的提升公式: 若 $q:M->N$ 满射, $f:P->N$, 选取 $m_j in M$ 使 $q(m_j)=f(p_j)$, 就可令
$ tilde(f)(p)=sum_(j=1)^n phi_j (p)m_j $
因为 $q(tilde(f)(p))=sum_j phi_j (p)f(p_j)=f(p)$.

有限投射模还自动*有限表示*. 确实, 若 $R^n tilde.eq P ⊕ Q$, 则 $Q$ 也由标准基的投影有限生成; 选满射 $R^m->Q$, 就得到有限表示 $R^m->R^n->P->0$.

#example(title: "投射不等于自由")[
  取域 $K$, 令 $R=K times K$, $P=K times 0$. 有
  $ R=(K times 0) ⊕ (0 times K) $
  所以 $P$ 有限投射. 它对应的幂等矩阵甚至只有一阶: $e=(1,0) in R$.

  但 $P$ 不自由: 非零元 $(0,1)$ 消去整个 $P$, 而它不能消去任何非零自由 $R$-模. 几何上, $Spec R$ 有两个点, $P$ 在它们上面的秩分别为 $1$ 与 $0$.
]

=== 应用: 平坦性与任意基变换

#proposition(title: "投射模平坦, 并且对基变换稳定")[
  投射 $R$-模 $P$ 是平坦的, 即 $- ⊗_R P$ 保持正合列. 对任意环同态 $R->S$, $S ⊗_R P$ 是投射 $S$-模; 若 $P$ 有限投射, 则 $S ⊗_R P$ 也有限投射.
]

#proof[
  写 $P ⊕ Q tilde.eq R^((I))$. 对任意单射 $U->V$, 映射
  $ U ⊗_R R^((I))->V ⊗_R R^((I)) $
  就是直和上的单射 $U^((I))->V^((I))$. 将它按 $P,Q$ 分解, 可知其直和分量 $U ⊗_R P->V ⊗_R P$ 也单射. 张量积本来右正合, 因而 $P$ 平坦.

  另一方面, 张量积保持直和与同构, 所以
  $ (S ⊗_R P) ⊕ (S ⊗_R Q) tilde.eq S^((I)) $
  故 $S ⊗_R P$ 是自由 $S$-模的收缩. 有限投射时可从 $R^n$ 出发, 得到 $S^n$ 的收缩. 全程不要求 $S$ 对 $R$ 平坦.
]

若 $P=im(e)$ 由幂等矩阵表示, 基变换只需把 $e$ 的每个系数送入 $S$. 新矩阵仍满足 $e^2=e$, 它的像就是 $S ⊗_R P$.

=== 应用: 对偶把 Hom 变成张量积

#proposition(title: "有限投射模的对偶公式")[
  设 $P$ 有限投射, 记 $P^or:=Hom_R (P,R)$. 对任意 $R$-模 $M$, 自然映射
  $ P^or ⊗_R M->Hom_R (P,M), quad phi ⊗ m |-> (p |-> phi(p)m) $
  是同构.
] <prop-finite-projective-tensor-hom>

#proof[
  取有限对偶基 $(p_j,phi_j)$. 逆映射由
  $ g |-> sum_(j=1)^n phi_j ⊗ g(p_j) $
  给出. 向一个方向复合, 得到 $p |-> sum_j phi_j (p)g(p_j)=g(p)$. 另一个方向只需注意: 对每个 $phi in P^or$, 对偶基公式给出 $phi=sum_j phi(p_j)phi_j$, 因而
  $ sum_j phi_j ⊗ phi(p_j)m=phi ⊗ m $
  所以两条映射互逆.
]

这让有限投射模的 Hom 计算变成了张量积计算. 例如 $P^or$ 本身也是有限投射的: 对 $P ⊕ Q tilde.eq R^n$ 取对偶, 就得到 $P^or ⊕ Q^or tilde.eq R^n$.

=== 应用: 局部自由性与向量丛

#proposition(title: "有限表示模的局部判别")[
  对有限表示的 $R$-模 $P$, 以下两条等价:

  + $P$ 是投射模.
  + 对每个素理想 $frak(p)$, $P_(frak(p))$ 是自由 $R_(frak(p))$-模.

  此时每个点都有主开邻域 $D(f)$, 使 $P_f$ 有限自由. 参见 @Stacks26[Tag 00NX].
] <prop-finite-projective-local>

#proof[
  *先看局部环上的有限投射模.* 设 $(R,frak(m))$ 局部, 剩余域为 $K$. 将 $P slash frak(m)P$ 的一组 $K$-基提升到 $P$. 由 Nakayama 引理, 这些元素生成 $P$, 所以得到满射 $R^r->P$. 投射性给出分解 $R^r tilde.eq P ⊕ Q$. 因为 $Q$ 有限生成, 且模 $frak(m)$ 后原映射是同构, 有 $Q slash frak(m)Q=0$; 再用 Nakayama 引理得到 $Q=0$. 故 $P$ 自由. 对 $R_(frak(p))$ 应用此论证, 再用基变换保持投射性, 就证明了 $(1)=>(2)$.

  *再说明有限表示的作用.* 对有限表示模 $P$ 与任意模 $M$, 有
  $ Hom_R (P,M)_(frak(p)) tilde.eq Hom_(R_(frak(p))) (P_(frak(p)),M_(frak(p))) $
  这是因为有限表示 $R^a->R^b->P->0$ 将左边的 Hom 写成 $M^b->M^a$ 的核, 而局部化保持核与有限直和. 同一个论证也适用于主开集上的局部化.

  *现在证明 $(2)=>(1)$.* 对任意满射 $M->N$, 考察 $Hom_R (P,M)->Hom_R (P,N)$ 的余核. 在每个素理想处局部化后, 它由上式变成自由模 $P_(frak(p))$ 的提升问题, 因而余核为零. 模为零可以在所有素理想处检验, 所以原映射满射. 由 @thm-projective-characterizations, $P$ 投射.

  *最后把点上的基延伸到邻域.* 给定同构 $P_(frak(p)) tilde.eq R_(frak(p))^r$, 上述 Hom 与局部化的相容性使它及其逆映射都能在某个 $D(f)$ 上定义, 其中 $f ∉ frak(p)$. 两个复合与恒等映射之差在 $frak(p)$ 处为零, 所以各自被某个 $frak(p)$ 之外的元素消去. 再把这两个元素倒置, 两条映射便在缩小后的主开邻域上互逆. 于是该邻域上 $P$ 的局部化有限自由.
]

因此, 把有限投射模 $P$ 层化到 $Spec R$ 上, 就得到有限局部自由层 $tilde(P)$, 也就是向量丛的模论形式. 在点 $frak(p)$ 上, 它的纤维是
$ P ⊗_R kappa(frak(p)) $
其维数在上述主开邻域上等于固定的 $r$, 所以秩是局部常值函数, 不必在整个 $Spec R$ 上相同. $K times K$ 的例子正好展示了这种情况.

在 $K$-理论中, 有限投射模是有限自由模的收缩, 可以用幂等矩阵描述; 而有限投射模之间的短正合列都分裂, 因此它们给出的关系
$ [P]=[P']+[P''] quad (0->P'->P->P''->0) $
都来自直和分解 $P tilde.eq P' ⊕ P''$. 这使有限投射模成为构造 $K_0 (R)$ 的自然起点.
