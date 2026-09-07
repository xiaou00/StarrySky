#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*
#import "../assets/universal-family.typ": universal-family-pullback, quadratic-family-pullback

#show: doc => conf(
  easy: true,
  doc,
)

= 模空间 / Moduli Spaces

== 什么是模空间?

第一章中, 我们把三角形的全等类组织成一个空间, 从而可以讨论三角形的连续变化. 在代数几何中, 我们希望把代数对象也组织成一个*模空间* (moduli space), 使对象的变化能用几何来研究.

沿用上一章的相对观点, 单个对象是点上的族, 更一般的族则允许对象随参数概形变化. 模空间需要同时描述对象与族. 以下固定基域 $k$, 并简记 $Sch_k:=Sch\/Spec k$.

=== 点所对应的对象

#definition(title: "有理点与域值点")[
  设 $M$ 是 $k$-概形, $K$ 是 $k$ 的扩域. 定义
  $ M(K):=Hom_(Sch_k) (Spec K,M) $
  称为 $M$ 的 *$K$-值点集*, 也称 *$K$-有理点集*. 这里的"有理"是相对于所指定的域而言的.
]

模空间最初的愿望, 就是让这些点对应所研究的代数对象的同构类, 并使对应与扩域相容. 其中什么算作对象, 什么算作同构, 都需要先说清楚.

#example(title: "首一多项式")[
  固定整数 $d>=1$. 一个 $d$ 次首一多项式
  $ p(x)=x^d+sum_(i=0)^(d-1) b_i x^i $
  由 $d$ 个系数唯一确定. 因而仿射空间 $M=bb(A)^d_k=Spec k[a_0,dots,a_(d-1)]$ 的域值点满足
  $ M(K) tilde.eq K^d tilde.eq {p in K[x] | p " 首一且 " deg p=d} $
  此处固定变量 $x$, 不作变量替换的等同.

  也可以把 $p$ 看成带指定元素的代数 $(K[x] slash (p),overline(x))$. 因而 $M(K)$ 分类的是带元素 $alpha$ 的 $K$-代数 $B$, 其中 $1,alpha,dots,alpha^(d-1)$ 构成一组基, 同构须保持 $alpha$.
]

#example(title: "射影空间")[
  射影空间的域值点是齐次坐标
  $ bb(P)^n_k (K)=(K^(n+1) without {0}) slash K^times $
  它们也分类一维商空间 $q:K^(n+1)->L$, 其中 $q$ 满射, 同构须与 $q$ 相容. 选取 $L$ 的基后, $q$ 由一组不全为零的系数 $(a_0,dots,a_n)$ 给出; 更换基只使这些系数同时乘以一个非零标量.

  这里分类的是带商映射的一维空间. 若只记一维 $K$-向量空间本身, 它们只有一个同构类. 参见 @Stacks26[Tag 01ND].
]

#block(breakable: false)[
=== 从点到族, 从空间到函子

把 $Spec K$ 换成一般的参数概形 $T$, 就得到 $M$ 的 *$T$-值点*
$ M(T):=Hom_(Sch_k) (T,M) $
沿 $f:T'->T$ 预复合, 给出 $M(T)->M(T')$. 因而概形 $M$ 自身可以看成一个反变函子
$ h_M:(Sch_k)^opp->Set, quad T |-> M(T) $
这就是*点函子*. 前文的 Yoneda 引理说明, 这个函子完整地记录了 $M$ 及其与其他概形之间的态射. 参见 @Stacks26[Tag 01JF].
]

#example(title: "随参数变化的多项式")[
  继续首一多项式的例子, 有自然双射
  $ Hom_(Sch_k) (T,bb(A)^d_k) tilde.eq Gamma(T,cal(O)_T)^d $
  因而一个态射 $T->bb(A)^d_k$ 就是一族多项式: 它的系数 $b_i$ 是 $T$ 上的正则函数. 在 $t:Spec K->T$ 处取值, 得到 $K$ 上的多项式; 沿 $f:T'->T$ 拉回, 则得到系数为 $f^* b_i$ 的新族. 参见 @Stacks26[Tag 01LZ].

  例如, $T=bb(A)^1_k=Spec k[t]$ 上的 $x^2-t$ 给出一族二次首一多项式. 参数 $t=c$ 时得到 $x^2-c$, 基变换 $t=s^2$ 后则得到 $x^2-s^2$.
]

这提示我们也可以直接从分类问题出发. 指定所研究的族及其拉回后, 令
$ F(T):={"以 " T " 为参数的族的同构类"} $
拉回使它成为反变函子 $F:(Sch_k)^opp->Set$, 称为*精模函子*. 在上述例子中, 点对应单个对象, 一般的态射则对应随参数变化的族.

=== Yoneda 引理与万有族

在多项式的例子中, 各个参数上的族都能由同一套坐标函数描述. Yoneda 引理解释了这种统一性: 给出 $M$ 上的一族对象, 就给出了沿所有 $T->M$ 拉回它的规则. 以下记 $"Nat"$ 为自然变换的集合, 并用 $xi in F(M)$ 表示族的同构类.

#proposition(title: "一族对象与一个自然变换")[
  对上述函子 $F$ 与任意 $k$-概形 $M$, 有自然双射
  $ "Nat"(h_M,F) tilde.eq F(M), quad eta |-> eta_M (id_M) $
  其逆映射将 $xi in F(M)$ 送到自然变换 $eta^xi:h_M->F$, 其中
  $ eta_T^xi (g)=g^* xi, quad g:T->M $
  这正是 Yoneda 引理. 参见 @Stacks26[Tag 001L].
] <prop-yoneda-family>

#proof[
  给定 $eta:h_M->F$, 对 $g:T->M$ 使用自然性, 得到
  $ eta_T (g)=eta_T (h_M (g)(id_M))=F(g)(eta_M (id_M)) $
  因而 $eta$ 完全由 $eta_M (id_M)$ 决定. 反过来, 拉回与复合相容, 所以 $g |-> g^* xi$ 确实定义自然变换; 再在 $id_M$ 处取值, 就得到 $xi$. 两个构造互逆.
]

#block(breakable: false)[
现在假设这个 $eta:h_M->F$ 是*自然同构*. 那么
$ xi_"univ":=eta_M (id_M) $
称为*万有元素*, 其代表族称为*万有族*. 因为每个 $eta_T$ 都是双射, 任意 $zeta in F(T)$ 都唯一写成
$ zeta=g^* xi_"univ", quad g:T->M $
所以万有族来自恒等态射, 所有族来自它的拉回. 反过来, 若一个族具有上述唯一拉回的性质, 它对应的自然变换就是同构. 这只是同一个 Yoneda 对应的两种读法. 参见 @Stacks26[Tag 01JF].
]

#remark[
  这里唯一的是分类态射 $g$. 由于 $F(T)$ 记录同构类, 上式说明两个族同构, 并不要求它们之间的同构唯一. 此外, 任意 $xi in F(M)$ 都给出自然变换, 而万有性要求这个自然变换是同构.
]

#block(breakable: false)[
#proposition(title: "万有族的唯一性")[
  若 $(M,xi)$ 与 $(N,nu)$ 都具有上述万有性, 则存在唯一同构 $u:M->N$ 使得 $u^* nu=xi$.
]

#proof[
  两边的万有性分别给出唯一态射 $u:M->N$ 与 $v:N->M$, 满足 $u^* nu=xi$ 和 $v^* xi=nu$. 于是
  $ (v compose u)^* xi=u^*(v^* xi)=u^* nu=xi $
  恒等态射也有这个性质, 故唯一性给出 $v compose u=id_M$. 同理 $u compose v=id_N$.
]
]

#example(title: "万有多项式就是恒等态射对应的族")[
  回到 $M=bb(A)^d_k$ 与首一多项式的函子. 恒等态射保持每个坐标函数 $a_i$, 因而对应的族是
  $ p_"univ" (x)=x^d+sum_(i=0)^(d-1) a_i x^i $
  对任意 $T$ 上的系数 $b_i in Gamma(T,cal(O)_T)$, 前面的仿射空间例子给出唯一态射 $g:T->M$, 满足 $g^* a_i=b_i$. 于是
  $ g^* p_"univ" (x)=x^d+sum_(i=0)^(d-1) b_i x^i $
  这就直接验证了万有性: 所有首一多项式族都由这一个多项式拉回得到.
]

== 代数空间

把模问题写成函子以后, 我们仍希望它具有可用的局部坐标. 概形用 Zariski 开集粘合, *代数空间*则允许用平展图册描述局部几何. 这种放宽让更多自然的商具有几何意义.

=== 平展的意义

#definition(title: "平展态射")[
  概形态射 $f:U->V$ 称为*平展* (étale), 若它光滑且相对维数为 $0$. 等价地, 它局部有限表示, 平坦且非分歧. 参见 @Stacks26[Tag 02GH].
]

#block(breakable: false)[
它是代数几何中"局部同构"的对应物. 一个精确的含义是: 对 $V$ 上由平方零理想定义的闭浸入 $T_0->T$, 限制映射
$ Hom_V (T,U)->Hom_V (T_0,U) $
是双射. 也就是说, 已选定的局部解可以唯一延拓到无穷小增厚上, 不会增加新的无穷小自由度. 参见 @Stacks26[Tag 02HM].
]

#example(title: "重新看平方根")[
  设 $"char" k!=2$. 前文的方程 $x^2-t=0$ 给出 $bb(A)^1_k->bb(A)^1_k$, $t=x^2$. 去掉原点后, 得到平展二重覆盖
  $ Spec k[x,x^(-1)]->Spec k[t,t^(-1)], quad t |-> x^2 $
  因为方程对 $x$ 的导数 $2x$ 可逆. 原点处两根合并, 纤维为 $Spec(k[x] slash (x^2))$, 此处便不再平展.

  这个覆盖并非 Zariski 局部同构: 函数域扩张 $k(t) subset k(x)$ 的次数为 $2$, 缩小非空开集也不会改变它. 因而平展提供了比开集更灵活的局部参数化.
]

开浸入都是平展态射;平展态射在复合与任意基变换下保持, 并且是开映射. 因而可以把联合满射的平展态射族 ${U_i->T}$ 规定为覆盖, 得到 $Sch_k$ 上的*平展拓扑*. 这时的层条件仍是前文的局部粘合条件. 参见 @Stacks26[Tag 02GH].

#example(title: "平展能看见结点的两条分支")[
  设 $"char" k!=2$, 考虑不可约曲线
  $ C=Spec(k[x,y] slash (y^2-x^2 (1+x))) $
  原点 $o=(0,0)$ 是结点, 两条切线为 $y=plus.minus x$. 因为 $C$ 不可约, 每个包含 $o$ 的 Zariski 开邻域仍然不可约.

  取开邻域 $X=D(1+x) subset C$, 在其上添加平方根 $s^2=1+x$, 得到
  $ Y=Spec(k[x,y,s,s^(-1)] slash (y^2-x^2 (1+x),s^2-1-x)) $
  忘掉 $s$ 的映射 $p:Y->X$ 是有限平展二重覆盖: 方程 $s^2-(1+x)=0$ 是首一的, 且导数 $2s$ 处处可逆. 在 $Y$ 上, 原方程分解为
  $ (y-x s)(y+x s)=0 $
  所以 $Y$ 有两个不可约分支 $Y_+=V(y-x s)$ 与 $Y_-=V(y+x s)$, 各自同构于 $Spec k[s,s^(-1)]$. 它们恰在 $o$ 上方的两个点
  $ o_+=(0,0,1), quad o_-=(0,0,-1) $
  相交. 因而平展邻域把两条局部分支分别实现为不同的不可约分支, 这是仅缩小 Zariski 开集做不到的.
]

#remark[
  $o_+$ 与 $o_-$ 仍然是结点, 两条分支仍在这里相交. 平展邻域揭示了分支结构, 并没有消除奇点. 将结点的两条分支拆成两个光滑点属于*正规化*, 正规化映射在结点上并不平展. 关于结点与分支, 参见 @Stacks26[Tag 0C46].
]

=== 平展图册与代数空间

#definition(title: "代数空间")[
  一个 $k$ 上的*代数空间*是集合值平展层
  $ X:(Sch_k)^opp->Set $
  并且存在概形 $U$ 与层态射 $p:h_U->X$, 使得对每个概形 $T$ 及态射 $h_T->X$:

  - 层的纤维积 $h_U times_X h_T$ 由一个概形表示, 简记为 $U times_X T$.
  - 投影 $U times_X T->T$ 是满射平展态射.

  这样的 $p$ 称为*平展图册*, 也称为概形可表的满射平展态射. 代数空间之间的态射就是层之间的自然变换. 参见 @Stacks26[Tags 025Y, 076L].
]

#figure(
  diagram(
    cell-size: 0pt, node-inset: 7pt,
    {
      edge((0, 0), (1, 0), marks: "->")
      edge((0, 0), (0, 1), label: [满射平展], label-side: right, marks: "->")
      edge((1, 0), (1, 1), label: $p$, label-side: left, marks: "->")
      edge((0, 1), (1, 1), marks: "->")
      node((0, 0), $U times_X T$)
      node((1, 0), $U$)
      node((0, 1), $T$)
      node((1, 1), $X$)
    },
  ),
  caption: [平展图册的拉回方块. 对任意测试概形 $T$, 左上角仍是概形, 左边成为通常的平展覆盖.],
)

因此, "平展局部是概形"是通过测试概形与基变换来表达的. 它不要求 $U$ 是 $X$ 的开子空间; 图册中的不同点可以描述同一个局部对象.

#block(breakable: false)[
=== 商与基本结论

#theorem(title: "代数空间是平展等价关系的商")[
  若 $U->X$ 是平展图册, 则 $R:=U times_X U$ 是概形, 两个投影 $R pairarrow U$ 都是平展态射, 且
  $ X tilde.eq U slash R $
  这里取*层商*, 即预层 $T |-> U(T) slash R(T)$ 的平展层化.

  反过来, 若概形中的等价关系 $R->U times_k U$ 的两个投影都是平展态射, 则层商 $U slash R$ 是代数空间, $U->U slash R$ 是平展图册. 参见 @Stacks26[Tag 02WW].
]

这里的等价关系要求 $R->U times_k U$ 是单态射, 且对每个测试概形都给出集合的等价关系. 用第一章的语言说, 它是任意两对象之间至多有一个箭头的内部群胚. 层化则保证局部代表可以按相容关系粘合.
]

#proposition(title: "几条基本性质")[
  - 每个概形都是代数空间, 可取恒等态射为图册. Yoneda 嵌入将 $Sch_k$ 视为代数空间范畴的全子范畴. 参见 @Stacks26[Tag 025X].
  - 代数空间的纤维积存在, 并在层中计算. 特别地, 若 $U,V$ 是映向同一代数空间 $X$ 的概形, 则 $U times_X V$ 仍是概形; 这也称为 $X$ 的*对角态射概形可表*. 参见 @Stacks26[Tag 04T8].
  - 约化, 正规, 正则等平展局部性质, 都可在任意平展图册 $U->X$ 上检验. 因而许多局部问题仍归结为概形上的问题. 参见 @Stacks26[Tag 03E8].
]

#example(title: "一个不是概形的代数空间")[
  设 $"char" k!=2$, 取 $U=bb(A)^1_k$, $U^times=U without {0}$, 定义
  $ R=U coprod U^times -> U times_k U $
  第一分支映为 $(x,x)$, 第二分支映为 $(x,-x)$. 两个投影都是平展, 所以层商 $X=U slash R$ 是代数空间. 它把非零点 $x$ 与 $-x$ 识别, 在原点只保留恒等关系.

  这个 $X$ 不是概形, 证明从略. 它说明, 即使图册与关系都由很简单的概形给出, 层商也可能需要代数空间来容纳. 参见 @Stacks26[Tag 02Z0, 例 65.14.1].
]

== 精模空间

这里允许基底是任意概形 $S$, 并记 $Sch_S:=Sch slash S$.

#definition(title:[精模函子])[
  一个*精模函子* (fine moduli functor) 是一个反变函子
  $ F:(Sch_S)^opp->Set $
  通常描述一类代数对象及其随参数变化的族. 若存在一个代数空间 $M$ 表示这个函子, 即有自然同构
  $ F tilde.eq h_M, quad h_M (T)=Hom_S (T,M) $
  则称 $M$ 为这个模问题的*精模空间* (fine moduli space). 当 $M$ 是概形时, 与恒等态射 $id_M$ 对应的元素 $xi_"univ" in F(M)$ 就是*万有族*的同构类.
] <def-fine-moduli>

=== 怎样看待万有族

以下仍在 $k$ 上讨论, 并设 $M$ 是概形. Yoneda 引理把万有族写成 $F(M)$ 中的元素. 几何上, $M$ 参数化对象: 域值点 $m:Spec K->M$ 指定一个 $K$ 上的对象, 万有族把这些对象连同变化方式组织在一起.

当所研究的族由概形态射给出时, 可以把万有族写成
$ pi:U->M $
这里 $M$ 是*参数空间*, $U$ 是*族的总空间*. 在 $m$ 上取纤维
$ U_m:=Spec K times_M U $
才得到 $m$ 所代表的对象. 若模问题还包含标记, 嵌入或商映射, 这些数据也属于万有族, 并且一起拉回.

给定 $T$ 上的一族 $p:Y->T$, 万有性给出唯一的*分类态射* $g:T->M$, 以及保持所要求数据的 $T$ 上同构
$ Y tilde.eq T times_M U $
直观地说, $g$ 指定在每个参数处使用万有族的哪条纤维. 对 $t:Spec K->T$, 令 $m=g compose t$, 就有 $Y_t tilde.eq U_m$. 整个拉回还保留纤维之间的代数关系, 因而得到的是一族对象. 参见 @Stacks26[Tag 01JO].

#figure(
  universal-family-pullback(),
  caption: [沿分类态射拉回万有族. 图中只示意若干纤维, 橙色标出 $Y_(t_0) tilde.eq U_(g(t_0))$. 外框表示总空间, 整个方块是拉回方块.],
)

分类态射不必是嵌入, 不同参数可以对应同一个对象. 如果 $g$ 经过一个 $k$-值点 $m:Spec k->M$, 拉回就是常值族 $T times_k U_m->T$. 更一般地, $g$ 描述对象怎样随 $T$ 变化. 当 $T=M$ 且 $g=id_M$ 时, 每个参数仍对应它自己, 拉回便是万有族本身; 这就是 $xi_"univ"=eta_M (id_M)$ 的几何含义.

#example(title: "把系数代入万有方程")[
  设 $"char" k!=2$, 先只考虑形如 $x^2-c$ 的首一二次多项式, 即把一次项系数固定为 $0$. 它们的精模空间是 $M=bb(A)^1_k=Spec k[c]$, 万有多项式为 $x^2-c$. 把根也记录下来, 得到
  $ U=Spec(k[c,x] slash (x^2-c)), quad pi:U->M $
  连同指定的坐标 $x$. $M$ 上的一个点记录系数, $U$ 上的一个域值点则记录系数和所选的一个根. 纤维 $U_c$ 是整个根的概形, 包括重根信息.

  对 $T$ 上的正则函数 $b$, 分类态射由 $g^* c=b$ 给出. 拉回万有方程, 就得到 $x^2-b$; 相应的根的族为
  $ T times_M U tilde.eq V(x^2-b) subset bb(A)^1_T $
  例如取 $T=bb(A)^1_k=Spec k[t]$ 与 $b=t^2$, 则
  $ g^* c=t^2, quad Y=Spec(k[t,x] slash (x^2-t^2)) $
  图中的上方箭头把 $(t,x)$ 送到 $(t^2,x)$: 保留所选的根, 将参数换成对应的系数. $t=1$ 与 $t=-1$ 都映向 $c=1$, 所以这两处的纤维都由根 $x=1,-1$ 组成.
]

#figure(
  quadratic-family-pullback(),
  caption: [万有方程 $x^2-c$ 沿 $c=t^2$ 拉回为 $x^2-t^2$. 图画出 $k=RR$ 时的实点, 虚线标出 $t=plus.minus 1$ 与 $c=1$ 上的纤维. 两边参数为 $0$ 时的纤维都是 $Spec(k[x] slash (x^2))$, 图中的单个点还带有长度为 $2$ 的概形结构.],
)

#remark(title: "只列出每个点上的对象还不够")[
  取 $T=Spec(k[epsilon] slash (epsilon^2))$. 方程 $x^2$ 与 $x^2-epsilon$ 限制到 $epsilon=0$ 时都变成 $x^2$, 但作为 $T$ 上的多项式族并不相同: 两个分类态射分别满足 $g_0^* c=0$ 与 $g_1^* c=epsilon$.

  因而万有族的要求是: *所有参数概形上的族*, 连同其拉回规律, 都由分类态射描述. 仅有域值点与对象同构类之间的对应, 还不能给出这种万有性.
]

=== 一些精模空间与万有族

以下仍取 $S=Spec k$, 所有例子中的精模空间都由概形给出. 我们同时写出参数概形 $T$ 上的对象和 $M$ 上的万有族; 沿唯一的分类态射 $g:T->M$ 拉回万有族, 就得到所给的对象.

#example(title: "正则函数与可逆函数")[
  $T$ 上的 $n$ 个有序正则函数组成函子
  $ F(T)=Gamma(T,cal(O)_T)^n $
  它的精模空间是 $M=bb(A)^n_k=Spec k[a_1,dots,a_n]$, 万有族就是坐标函数组 $(a_1,dots,a_n)$. 给定 $(b_1,dots,b_n)$, 分类态射由 $g^* a_i=b_i$ 唯一确定. 参见 @Stacks26[Tag 01LZ].

  若要求一个函数处处可逆, 则 $F(T)=Gamma(T,cal(O)_T)^times$, 精模空间变为
  $ M=bb(G)_m=Spec k[a,a^(-1)] $
  万有族是其上的可逆函数 $a$. 因而这里的万有族首先是一项代数数据, 不必写成空间之间的投影.
]

#example(title: "矩阵与可逆矩阵")[
  固定标准基, 分类 $cal(O)_T$-线性映射 $cal(O)_T^n->cal(O)_T^m$. 这样的映射由 $m n$ 个正则函数给出, 所以精模空间为 $M=bb(A)^(m n)_k$, 以 $a_(i j)$ 为坐标. 万有族是*万有矩阵*
  $ A_"univ"=(a_(i j)):cal(O)_M^n->cal(O)_M^m $
  拉回就是逐项代入矩阵的系数. 若 $m=n$ 且要求映射可逆, 精模空间为开子概形
  $ GL_(n,k)=D(det A_"univ") subset bb(A)^(n^2)_k $
  万有族是 $A_"univ"$ 在此开集上的限制. 此处基是固定的, 不对矩阵作共轭或换基的等同.
]

#example(title: "射影空间与万有商线丛")[
  延续前文的一维商空间, 令 $F(T)$ 分类满射
  $ q:cal(O)_T^(n+1)->cal(L) $
  其中 $cal(L)$ 是线丛, 即秩为 $1$ 的局部自由层; 同构须与 $q$ 相容. 其精模空间是 $M=bb(P)^n_k$, 万有族是*万有商线丛*连同商映射
  $ q_"univ":cal(O)_M^(n+1)->cal(O)_M (1), quad e_i |-> a_i $
  这里齐次坐标 $a_i$ 是 $cal(O)_M (1)$ 的截面. 对任意族 $(cal(L),q)$, 唯一的分类态射 $g:T->M$ 满足
  $ (cal(L),q) tilde.eq (g^* cal(O)_M (1),g^* q_"univ") $
  具体地, 在 $q(e_i)$ 生成 $cal(L)$ 的开集上, 比值 $q(e_j)\/q(e_i)$ 给出到标准仿射图的态射, 再粘合得到 $g$. 万有族包含商映射这一数据. 参见 @Stacks26[Tag 01ND].
]

== Grassmann概形

我们下面引入一系列非常重要的精模空间的例子, 先从Grassmann概形开始.

#remark(title:[记号约定])[
  固定一个概形 $S$, 以及其上的秩 $n$ 的向量丛 $cal(E)$, 对于 $f:T->S$,  记
  $ cal(E)_T = f^* cal(E) $
  为拉回层. 设 $cal(F)$ 是拟凝聚层, 则
  $ PP_S (cal(F)) = "Proj"_S "Sym"(cal(F)) $
  为 $S$ 上的相对射影概形, 即射影化.
]

=== Grassmann模函子

#definition(title:[Grassmann模函子])[
  固定一个概形 $S$, 以及其上的秩 $n$ 的向量丛 $cal(E)$. 对每个整数 $0<r<n$, 定义*Grassmann模函子*为
  $ frak(Gr)_r cal(E) (T) = {q:cal(E)_T ->> cal(Q) | cal(Q) "有限局部自由且秩" r} slash.big tilde.eq $
  是 $(Sch_S)^opp->Set$ 的反变函子. 这里
  $ (q:cal(E)_T ->> cal(Q)) tilde.eq (q':cal(E)_T ->> cal(Q')) $
  是指存在同构 $a:cal(Q)->^~cal(Q)'$ 使得 $a q = q'$.
]

#remark(title: "它参数化什么")[
  先取一个域值点 $s:Spec K->S$. 此时 $cal(E)_s$ 是 $n$ 维 $K$-向量空间, 所分类的对象是它的 *$r$ 维商空间*, 连同商映射. 一个商由它的核完全确定:
  $ W=ker q, quad dim_K W=n-r, quad Q tilde.eq cal(E)_s slash W $
  因而也可以说, 它参数化 $cal(E)_s$ 中的 *$(n-r)$ 维线性子空间*. 保留商映射 $q$, 正是为了记录核在固定空间 $cal(E)_s$ 中的位置.

  对一般的 $T->S$, 所分类的是随参数作代数变化的商空间族, 可以写成正合列
  $ 0->cal(K)->cal(E)_T->cal(Q)->0 $
  其中 $cal(K)$ 与 $cal(Q)$ 分别局部自由且秩为 $n-r$ 与 $r$. 因为商局部自由, 这条正合列局部分裂, 所以核确实是一个子丛. 参见 @Stacks26[Tag 089R].

  按前面的射影化约定, 商映射还给出闭嵌入
  $ PP_T (cal(Q))->PP_T (cal(E)_T) $
  因而这个模问题也描述射影丛中*相对维数为 $r-1$ 的线性子空间族*. 例如 $n=3,r=2$ 时, 在向量空间的语言中是选取三维空间里的一条直线作为核; 在射影几何的语言中, 则是选取射影平面里的一条射影直线. 参见 @Stacks26[Tag 01OA].
]

#remark(title: "态射上的作用")[
  记 $F=frak(Gr)_r cal(E)$. 对任意 $S$-态射 $h:T'->T$, 利用典范同构 $h^* cal(E)_T tilde.eq cal(E)_(T')$, 定义
  $ F(h):F(T)->F(T'), quad [q] |-> [h^* q:cal(E)_(T')->>h^* cal(Q)] $
  拉回是右正合的, 因而 $h^* q$ 仍为满射; $h^* cal(Q)$ 仍有限局部自由且秩为 $r$. 商之间的同构也可以拉回, 所以这个赋值与代表的选择无关.

  对 $T''->^u T'->^h T$, 拉回的典范同构 $(h compose u)^* tilde.eq u^* h^*$ 在同构类上给出
  $ F(h compose u)=F(u) compose F(h), quad F(id_T)=id_(F(T)) $
  因此上述构造确实给出反变函子 $F:(Sch_S)^opp->Set$. 参见 @Stacks26[Tag 089R].
]

我们先来证明几个关于构造本身的核心引理.

#lemma[
  对上述定义中的 $q:cal(E)_T->>cal(Q)$, 设 $cal(K)=ker q$. 则正合列
  $ 0->cal(K)->cal(E)_T->cal(Q)->0 $
  局部分裂, 也就是说限制到某个仿射开覆盖后分裂, 并且
  $ Aut(cal(E)_T ->> cal(Q)) = {id_cal(Q)} $ 
] <lem-grassmann-splitting>

#proof[
  任取 $t in T$, 其在某个开邻域 $U$ 上取平凡化
  $ cal(Q)|_U tilde.eq cal(O)^(plus.o r)_U $
  因为 $q|_U$ 是拟凝聚层的满射. 由 $U$ 仿射, 截面函子是正合的, 于是保持满射性, 从而
  $ Gamma(U,cal(E)_T) ->> Gamma(U,cal(Q)) tilde.eq Gamma(U,cal(O)_U)^(plus.o r) $
  在右边取标准基 $e_1,...,e_r$, 取提升
  $ v_i in Gamma(U,cal(E)_T), quad q(v_i)=e_i $
  于是存在唯一的 $cal(O)_U$-线性映射
  $ s:cal(Q)|_U tilde.eq cal(O)^(plus.o r)_U -> cal(E)_T|_U, quad e_i |-> v_i $
  且 $q compose s = id_(cal(Q)|_U)$. 这给出局部分裂.

  若 $a:cal(Q)->^~ cal(Q)$ 是 $q$ 的自同构, 则 $a compose q = q$, 由 $q$ 满射可消去, 得到 $a=id_(cal(Q))$.
]

=== 概形的初步构造

下面, 我们假设 $cal(E)=cal(O)^(plus.o n)_S$ 的标准基为 $e_1,...,e_n$. 并记 $m=n-r$.

#lemma(title:[标准开子函子])[
  对每个 $r$ 元子集 $I = {i_1<...<i_r} subset {1,...,n}$, 定义子函子
  $ frak(U)_I (T) = {[q] in frak(Gr)_r cal(O)^(plus.o n)_S (T) | q: cal(O)^(plus.o I)_T -> cal(Q) "是同构"} $
  那么 $frak(U)_I tilde.eq AA^(r m)_S$.
] <lem-grassmann-charts>

#proof[
  记 $q_I$ 为 $q$ 在 $I$ 所标记的直和因子上的限制. 用 $q_I^(-1)$ 将 $cal(Q)$ 识别为 $cal(O)_T^(plus.o r)$, 并按 $I$ 及其补集重排源的标准基, 则商映射唯一标准化为矩阵 $(I_r,B)$, 其中 $B$ 是一个系数在 $Gamma(T,cal(O)_T)$ 中的 $r times m$ 矩阵.

  商映射的同构不改变 $B$, 而任意这样的 $B$ 都给出一个属于 $frak(U)_I (T)$ 的商. 因此有双射
  $ frak(U)_I (T) tilde.eq Gamma(T,cal(O)_T)^(r m) tilde.eq Hom_S (T,AA^(r m)_S) $
  拉回对应于逐项拉回 $B$ 的系数, 所以上述双射关于 $T$ 自然, 即得到所需的函子同构.
]

#lemma(title:[覆盖性质])[
  上述 $frak(U)_I$ 都是开子函子, 并在 Zariski 局部意义下覆盖整个模函子, 记为
  $ frak(Gr)_r cal(O)^(plus.o n)_S = union.big_(abs(I)=r) frak(U)_I $
  即每个 $T$-值对象都能在 $T$ 的某个开覆盖上分别落入这些子函子.
] <lem-grassmann-cover>

#proof[
  给定 $T$ 上的商 $q$, 局部选基后, $q_I$ 就是方阵. 它是同构, 等价于 $det(q_I)$ 可逆. 这就给出开子概形 $T_I$, 而且与基变换相容, 所以 $frak(U)_I$ 是开子函子.

  再看任意 $t in T$. 纤维上的 $q(t)$ 是满射, 总能从它的列中选出 $r$ 列作为 $cal(Q)(t)$ 的一组基. 取这些列的指标为 $I$, 就有 $t in T_I$. 因此 $T=union.big_(abs(I)=r) T_I$.
]

#lemma(title:[坐标变换及余循环条件])[
  将表示 $frak(U)_I$ 的概形记为 $U_I=AA^(r m)_S$. 在 $U_I$ 上, 用 $B$ 表示完整的 $r times n$ 标准商矩阵, 各列仍按原顺序排列, 因而 $B_I=I_r$. 这里 $B_J$ 表示由 $J$ 所标记的列组成的子矩阵. 与 $U_J$ 的重叠部分在 $U_I$ 中为
  $ U_(I J)=D(det B_J) $
  从 $I$ 图到 $J$ 图的坐标变换为
  $ B |-> B_J^(-1) B $
  这些变换满足余循环条件.
] <lem-grassmann-transitions>

#proof[
  进入 $J$ 图, 就是要求 $B_J$ 可逆. 要把这几列变成单位矩阵, 左乘 $B_J^(-1)$ 即可; 反向变换正好是它的逆.

  在三重交叠上, 先从 $I$ 变到 $J$, 再变到 $L$, 得到
  $ (B_J^(-1) B_L)^(-1) (B_J^(-1) B)=B_L^(-1) B $
  恰好就是从 $I$ 直接变到 $L$ 的结果.
]

现在回到一般的秩 $n$ 向量丛 $cal(E)$, 仍记 $m=n-r$.

#theorem(title:[可表性, 万有正合列与基变换])[
  存在 $S$-概形 $pi:G=Gr_r (cal(E))->S$, 称为 *Grassmann概形*, 以及关于 $T$ 的自然同构
  $ Hom_S (T,G) tilde.eq frak(Gr)_r cal(E) (T) $
  在 $G$ 上有*万有正合列*
  $ 0->cal(K)->pi^* cal(E)->cal(Q)->0 $
  其中 $cal(K)$ 与 $cal(Q)$ 局部自由, 秩分别为 $m$ 与 $r$. 每个 $T$ 上的商, 都由万有商沿唯一的分类态射 $T->G$ 拉回得到. 对任意 $S'->S$, 有典范同构
  $ Gr_r (cal(E)) times_S S' tilde.eq Gr_r (cal(E)_(S')) $
  万有正合列也随之拉回.
] <thm-grassmann-representability>

#proof[
  由 @lem-grassmann-splitting, 相容的局部商可沿唯一的商同构粘合, 所以模函子是 Zariski 层. 当 $cal(E)$ 平凡时, 由 @lem-grassmann-charts, @lem-grassmann-cover 和 @lem-grassmann-transitions 粘合各个 $U_I$, 便得到表示概形. 参见 @Stacks26[Tag 089R].

  对一般的 $cal(E)$, 在平凡化开覆盖上作此构造; 交叠处由 Yoneda 引理得到满足余循环条件的典范同构, 再粘合即可.

  由 @prop-yoneda-family, $id_G$ 对应的商就是万有商. 取核得到万有正合列, 核的局部自由性与秩由 @lem-grassmann-splitting 得到.

  基变换公式两边表示同一个 $S'$ 上的模函子, 故由 Yoneda 引理典范同构, 万有商也相互对应. 局部分裂保证拉回仍正合, 因而整条万有正合列与基变换相容.
]

#remark(title:[为什么是精模空间])[
  @thm-grassmann-representability 恰好验证了 @def-fine-moduli: 对*每个参数概形* $T->S$, $T$ 上的秩 $r$ 商族与态射 $T->G$ 自然一一对应, 而且这个对应与任意基变换相容. 这也包括带无穷小结构的参数概形.

  具体地, 万有族是商映射 $q_"univ":pi^* cal(E)->>cal(Q)$. 任给 $q_T:cal(E)_T->>cal(F)$, 其中 $cal(F)$ 局部自由且秩为 $r$, 都有唯一的分类态射 $g:T->G$ 及同构 $alpha:g^* cal(Q)->^~cal(F)$, 使得
  $ q_T=alpha compose g^* q_"univ" $
  也就是说, 所有商族都由同一个万有商拉回得到.

  这里分类的是*固定 $cal(E)$ 的商*, 商映射本身也是数据的一部分. 由 @lem-grassmann-splitting, 保持商映射的自同构只有恒等, 因而上面的相容同构 $alpha$ 也唯一.
]

=== Plücker嵌入

#definition(title:[Plücker态射])[
  对 @thm-grassmann-representability 中的万有商取第 $r$ 外幂, 得到
  $ pi^* (and.big^r cal(E)) tilde.eq and.big^r pi^* cal(E) ->> and.big^r cal(Q)=det cal(Q) $
  因为 $cal(Q)$ 的秩为 $r$, 右边是线丛. 由射影丛参数化秩 $1$ 局部自由商的模性质, 这个商唯一确定一个 $S$-态射
  $ op("Pl"):G->PP_S (and.big^r cal(E)) $
  称为 *Plücker态射*. 参见 @Stacks26[Tag 01OA].
] <def-plucker-morphism>

#remark(title:[哪个外幂是线丛])[
  $cal(Q)$ 的秩为 $r$, 局部选基 $v_1,...,v_r$ 后, 其最高外幂由一个基
  $ v_1 and dots and v_r $
  生成, 所以 $and.big^r cal(Q)=det cal(Q)$ 是线丛. 而 $and.big^r cal(E)$ 的秩为 $binom(n,r)$, 一般不是线丛. 这里需要的是它拉回后的一个*线丛商*, 正好符合射影丛的模性质.
]

#lemma(title:[Plücker态射拉回万有商线丛])[
  记 $P=PP_S (and.big^r cal(E))$. 有与商映射相容的典范同构
  $ op("Pl")^* cal(O)_P (1) tilde.eq det cal(Q) $
  以下记
  $ cal(O)_G (1):=det cal(Q) $
] <lem-plucker-line-bundle>

#proof[
  由 @def-plucker-morphism, $op("Pl")$ 是外幂商的分类态射. 而 $cal(O)_P (1)$ 连同商映射是 $P$ 上的万有商, 由 @prop-yoneda-family, 沿分类态射拉回它, 就得到 $det cal(Q)$ 连同原来的商映射.
]

#theorem(title:[Plücker嵌入])[
  Plücker态射
  $ op("Pl"):G->P=PP_S (and.big^r cal(E)) $
  是闭嵌入, 称为 *Plücker嵌入*.
] <thm-plucker-closed-immersion>

#proof[
  闭嵌入可在目标的开覆盖上检验, 因而可设 $S=Spec R$, $cal(E)=cal(O)_S^(plus.o n)$. 参见 @Stacks26[Tag 01QO]. 记 $p_J$ 为外幂基 $e_(j_1) and dots and e_(j_r)$ 对应的齐次坐标, 并令 $V_I=D_+ (p_I)$.

  由 @def-plucker-morphism, $p_I$ 拉回为 $det(q_I)$. 所以由 @lem-grassmann-cover,
  $ op("Pl")^(-1) (V_I)=U_I $
  在 $U_I$ 上取 $B_I=I_r$ 的标准矩阵 $B$, 记其自由系数为 $b_(a j)$, 其中 $1<=a<=r$, $j in.not I$. 由 @lem-grassmann-charts, $U_I->V_I$ 对应的坐标环同态为
  $ R[p_J/p_I | J != I] -> R[b_(a j)], quad p_J/p_I |-> det B_J $

  写 $I={i_1<dots<i_r}$. 将其中的 $i_a$ 换成 $j in.not I$, 沿其余单位列展开, 对应子式就是 $plus.minus b_(a j)$. 因而每个自由系数都在上述环同态的像中, 它是满射, 所以 $U_I->V_I$ 是闭嵌入. 各个 $V_I$ 覆盖 $P$, 结论成立.
]

最后写出这个闭嵌入的方程. 仍在 $S=Spec R$, $cal(E)=cal(O)_S^(plus.o n)$ 的平凡情形下讨论. 将齐次坐标扩展为交替记号 $p_(j_1 dots j_r)$: 交换两个指标变号, 有重复指标时为 $0$.

#theorem(title:[Plücker方程])[
  Plücker像由以下齐次二次方程定义:
  $ sum_(nu=1)^(r+1) (-1)^(nu-1) p_(a_1 dots a_(r-1) l_nu) p_(l_1 dots hat(l_nu) dots l_(r+1))=0 $
  其中 $A=(a_1,...,a_(r-1))$ 与 $L=(l_1,...,l_(r+1))$ 遍历取值于 ${1,...,n}$ 的指标列, 帽号表示删去该指标. 这些等式称为 *Plücker方程*.
  记它们生成的齐次理想为 $frak(a)$, 则 Plücker嵌入给出概形同构
  $ G tilde.eq op("Proj")(R[p_J : abs(J)=r] slash frak(a)) $
] <thm-plucker-equations>

#proof[
  最大子式满足上述关系, 这是行列式的 Laplace 展开. 所以若记右边的概形为 $Z$, 则由 @thm-plucker-closed-immersion, $G$ 是 $Z$ 的闭子概形.

  反过来, 固定 $I=(i_1<dots<i_r)$, 在 $Z_I=Z inter D_+ (p_I)$ 上记 $x_J=p_J\/p_I$, 并构造矩阵 $B=(b_(a j))$:
  $ b_(a j)=(-1)^(r-a) x_(i_1 dots hat(i_a) dots i_r j) $
  由交替记号的约定, $B_I=I_r$. 将方程中的 $L$ 取为 $(i_1,...,i_r,j)$, 得到
  $ x_(A j)=sum_(a=1)^r b_(a j) x_(A i_a) $
  这里 $A j$ 表示在指标列 $A$ 末尾添上 $j$. 若 $j in.not I$, 右边的指标列比左边少一个不在 $I$ 中的指标. 从 $x_I=1$ 出发归纳, 再与行列式沿最后一列的展开比较, 就有
  $ x_J=det B_J $

  因而取最大子式与上述矩阵构造互逆. 在坐标环上, 这给出
  $ Gamma(Z_I,cal(O)_(Z_I)) tilde.eq R[b_(a j) | 1<=a<=r, j in.not I] $
  由 @lem-grassmann-charts, 这正是标准开片 $U_I$, 且坐标映射与 @thm-plucker-closed-immersion 中的一致. 各个 $D_+ (p_I)$ 覆盖 $P$, 所以 $Z=G$.
]

对一般的 $cal(E)$, 在各个平凡化开集上使用这些方程即可. 它们定义的都是 Plücker像, 因而相互粘合.

#example(title:[$Gr_2 (cal(O)_S^(plus.o 4))$])[
  此时有六个齐次坐标 $p_(12),p_(13),p_(14),p_(23),p_(24),p_(34)$, Plücker方程归结为
  $ p_(12) p_(34)-p_(13) p_(24)+p_(14) p_(23)=0 $
  所以 $Gr_2 (cal(O)_S^(plus.o 4))$ 是 $PP_S^5$ 中的二次超曲面. 参见 @MS21[第 5.2 节, 例 5.7].
]

=== 几个几何性质

回到一般的秩 $n$ 向量丛 $cal(E)$, 记 $G=Gr_r (cal(E))$, $m=n-r$, 并沿用 @thm-grassmann-representability 中的万有正合列及记号 $cal(K),cal(Q)$.

#proposition(title:[光滑性, 有限表示与相对维数])[
  结构态射 $pi:G->S$ 光滑, 满射且有限表示, 并且具有纯相对维数
  $ dim(G slash S)=r(n-r)=r m $
  特别地, $pi$ 是忠实平坦的.
] <prop-grassmann-smooth>

#proposition(title:[纤维的几何性质])[
  对每个 $s in S$, 纤维
  $ G_s tilde.eq Gr_r (cal(E)_s) $
  是几何整, 光滑, 射影的 $kappa(s)$-簇, 维数为 $r m$, 并且在 $kappa(s)$ 上有理.
] <prop-grassmann-fibers>

#proposition(title:[矩阵商的含义])[
  令 $M$ 为参数化满射
  $ q:cal(E)_T->>cal(O)_T^(plus.o r) $
  的 $S$-概形. 在 $cal(E)$ 平凡化处, 它就是仿射空间中满秩 $r times n$ 矩阵构成的开集. 群 $GL_(r,S)$ 通过 $q dot g=g^(-1) compose q$ 右作用于 $M$.

  遗忘商空间的基所得到的态射
  $ M->G, quad q |-> [q] $
  是 Zariski 局部平凡的 $GL_(r,S)$-挠子. 因此有层的同构
  $ G tilde.eq (M slash GL_(r,S))_"fppf" $
  这里的商指轨道预层的 fppf 层化; fppf 覆盖是联合满射的平坦, 局部有限表示态射族. 参见 @Stacks26[Tag 021M].
] <prop-grassmann-matrix-quotient>

#proposition(title:[对偶与特殊情形])[
  对偶给出典范同构
  $ Gr_r (cal(E)) tilde.eq Gr_(n-r) (cal(E)^or) $
  具体地, 若 $q:cal(E)_T->>cal(Q)$ 的核为 $cal(K)$, 则它被送到商
  $ cal(E)_T^or ->> cal(K)^or $
  特别地,
  $ Gr_1 (cal(E)) tilde.eq PP_S (cal(E)), quad Gr_(n-1) (cal(E)) tilde.eq PP_S (cal(E)^or) $
  将同一模函子延伸到 $r=0,n$, 还有
  $ Gr_0 (cal(E)) tilde.eq S, quad Gr_n (cal(E)) tilde.eq S $
] <prop-grassmann-duality>

#proposition(title:[相对切丛与余切丛])[
  有典范同构
  $ cal(T)_(G slash S) tilde.eq underline(Hom)_(cal(O)_G) (cal(K),cal(Q)) tilde.eq cal(K)^or times.o cal(Q) $
  以及
  $ Omega_(G slash S)^1 tilde.eq cal(K) times.o cal(Q)^or $
  这里 $underline(Hom)$ 表示层 Hom. 在点的层面, 第一式说的是: 核子空间 $K$ 的一阶变形由 $Hom(K,Q)$ 描述. 参见 @Bez15[命题 3].
] <prop-grassmann-tangent>

== Hilbert概形

Hilbert概形可以视作是Grassmann理论很自然的下一步, 它参数化射影空间中闭子概形的族. 下面我们先给出它的定义, 再讨论它的存在性与几何性质.

=== Hilbert模函子

#definition(title:[Hilbert模函子])[
  固定一个有限表示的概形态射 $X->S$, 对 $T->S$ 记 $X_T=X times_S T$. 定义 *Hilbert模函子* 为
  $ frak("Hilb")_(X slash S) (T)={Z subset X_T " 闭子概形" | Z->T " 平坦, 固有且有限表示"} $
  对任意 $S$-态射 $h:T'->T$, 规定
  $ frak("Hilb")_(X slash S) (h):Z |-> Z times_T T' subset X_(T') $
  闭嵌入, 平坦性, 固有性与有限表示性都在基变换下保持, 因而得到反变函子 $frak("Hilb")_(X slash S):(Sch_S)^opp->Set$. 参见 @Stacks26[Tag 0CZX].
] <def-hilbert-functor>

#lemma(title:[Hilbert模对象没有非平凡自同构])[
  设 $i:Z->X_T$ 是闭嵌入. 若同构 $alpha:Z->^~ Z$ 满足 $i compose alpha=i$, 则
  $ alpha=id_Z $
] <lem-hilbert-automorphisms>

#proof[
  闭嵌入是单态射. 从 $i compose alpha=i compose id_Z$ 中消去 $i$, 就得到 $alpha=id_Z$.
]

#remark(title:[它参数化什么])[
  这里记录的是*嵌入在 $X_T$ 中的闭子概形族*. 两个抽象同构的概形, 若在 $X_T$ 中的位置不同, 仍是不同的对象. 等价地, 一个对象由其理想层 $cal(I)_Z subset cal(O)_(X_T)$ 确定.

  当 $X->S$ 射影时, $Z->T$ 自动固有, 所以只需另要求平坦且有限表示. 平坦性是对整个族的要求, 并不要求每条纤维都光滑或约化.
]

#definition(title:[固定Hilbert多项式])[
  进一步固定一个射影嵌入 $X->PP_S^N$, 记 $cal(O)_X (1)$ 为标准线丛的限制. 对 $Z in frak("Hilb")_(X slash S) (T)$ 与 $t in T$, 记 $Z_t$ 相对于该嵌入的 *Hilbert多项式* 为 $P_(Z_t)$, 它由充分大的整数 $d$ 处的等式
  $ P_(Z_t) (d)=dim_(kappa(t)) Gamma(Z_t,cal(O)_(Z_t) (d)) $
  确定. 这里 $cal(O)_(Z_t) (d)$ 是从所选射影嵌入限制得到的扭曲层. 参见 @Stacks26[Tag 089X].

  固定 $P in QQ[d]$, 定义子函子
  $ frak("Hilb")_(X slash S)^P (T)={Z in frak("Hilb")_(X slash S) (T) | P_(Z_t)=P " 对所有 " t in T} $
  其态射上的作用仍是基变换. Hilbert多项式在域扩张下不变, 所以拉回保持上述条件. 参见 @Stacks26[Tag 0DM5].
] <def-hilbert-polynomial-functor>

=== 平坦性与Hilbert多项式

先解释定义里为什么要放进平坦性. 它保证族在变化时, Hilbert多项式保持不变.

#proposition(title:[平坦族的Hilbert多项式局部常值])[
  设 $Z->T$ 平坦, 有限表示且射影, 并固定相对射影嵌入 $Z->PP_T^N$. 则
  $ t |-> P_(Z_t) $
  在 $T$ 上局部常值. 特别地, 若 $T$ 连通, 所有纤维具有同一个Hilbert多项式.
] <prop-hilbert-flat-polynomial>

#proofsketch[
  Hilbert多项式也可用 Euler 示性数计算:
  $ P_(Z_t) (d)=chi(Z_t,cal(O)_(Z_t) (d))=sum_i (-1)^i dim_(kappa(t)) H^i (Z_t,cal(O)_(Z_t) (d)) $
  对每个固定的 $d$, 右边由平坦族的上同调与基变换理论知局部常值. 多项式的次数至多为 $N$, 取 $N+1$ 个不同整数处的值就能确定它, 所以多项式本身也局部常值. 参见 @Stacks26[Tags 08AD, 0B9T].
]

#remark(title:[多项式不变还不够])[
  在非约化底上, Hilbert多项式恒定未必能推出平坦性. 例如
  $ T=Spec(k[epsilon] slash (epsilon^2)), quad Z=Spec k subset T=PP_T^0 $
  底空间只有一个点, 纤维的Hilbert多项式当然恒为 $1$, 但 $k$ 不是 $k[epsilon] slash (epsilon^2)$ 上的平坦模. 事实上, 单射 $(epsilon)->k[epsilon] slash (epsilon^2)$ 张量 $k$ 后变成了非单射的零映射.
]

#example(title:[两个点碰在一起])[
  考虑
  $ Z=Spec(k[t,x] slash (x(x-t))) -> Spec k[t] $
  坐标环以 $1,x$ 为 $k[t]$-基, 因而这是秩 $2$ 的有限平坦族. 当 $t=c!=0$ 时, 纤维是 $x=0,c$ 两个点; 当 $t=0$ 时, 它变成
  $ Z_0=Spec(k[x] slash (x^2)) $
  两点合到了一处, 长度仍为 $2$. 若只取约化后的点, 长度就只剩 $1$ 了. *重数和非约化结构正是平坦极限要留下的信息*. 将方程齐次化为 $x(x-t y)=0$, 就得到 $PP^1_(k[t])$ 中Hilbert多项式恒为 $2$ 的族.
] <ex-hilbert-collision>

此外, 闭子概形的理想层及其商可以作 fpqc 下降, 平坦性, 固有性与有限表示性也可如此检验. 所以Hilbert模函子是 fpqc 层; 这保证局部给出的族能够粘合. 参见 @Stacks26[Tags 082L, 0CZX].

=== 用统一正则性留下有限个数据

以下固定 *Noetherian 概形 $S$*, 先处理 $X=PP_S^N$, 并使用标准线丛 $cal(O)(1)$. 参数概形 $T->S$ 仍允许是任意的.

一个闭子概形由整层理想决定, 看上去需要记住各个次数的方程. 我们要证明: 固定Hilbert多项式以后, 只记住同一个足够大次数的方程就够了.

#definition(title:[Castelnuovo-Mumford正则性])[
  设 $k$ 是域, $cal(F)$ 是 $PP_k^N$ 上的凝聚层. 若
  $ H^i (PP_k^N,cal(F)(m-i))=0 quad (i>0) $
  则称 $cal(F)$ 是 *$m$-正则的*. 参见 @Stacks26[Tag 08A3].
] <def-cm-regularity>

#block(breakable: false)[
#proposition(title:[正则性带来的消失与生成])[
  若 $cal(F)$ 是 $m$-正则的, 则对每个 $q>=m$, 它也是 $q$-正则的, $cal(F)(q)$ 由整体截面生成, 并且
  $ H^i (PP_k^N,cal(F)(q))=0 quad (i>0) $
  乘法映射
  $ H^0 (PP_k^N,cal(F)(q)) times.o_k H^0 (PP_k^N,cal(O)(1)) -> H^0 (PP_k^N,cal(F)(q+1)) $
  也满射. 参见 @Stacks26[Tags 08A6, 08A7, 08A8].
] <prop-cm-consequences>
]

#proofsketch[
  扩域后可选一个避开伴随点的超平面, 用限制到超平面的正合列, 对 $N$ 归纳. 上同调长正合列把消失性和乘法的满射性逐次传到更高次数; 再结合 Serre 的整体生成定理, 得到 $cal(F)(m)$ 的整体生成性.
]

#theorem(title:[前置定理: 统一正则性界])[
  固定 $N$ 和 $P in QQ[d]$. 存在只依赖于 $N,P$ 的整数 $m_0$, 使得对任意域 $k$ 和任意满足 $P_Z=P$ 的闭子概形 $Z subset PP_k^N$, 理想层 $cal(I)_Z$ 都是 $m_0$-正则的.

  这是有界性定理, 此处直接引用 @Stacks26[Tag 08AG], 取其中的秩为 $1$ 即可.
] <thm-hilbert-uniform-regularity>

Serre 消失定理只说每个 $Z$ 各有一个足够大的次数. 这里更强: *同一个次数对所有这样的 $Z$ 都有效*. 这正是把整个模问题放进同一个Grassmann概形的关键.

以下固定 $m>=max(m_0,0)$. 若 $P$ 在任何域上都不能出现, 模函子为空; 下面讨论可以出现的情形. 对 $T->S$ 记
$ f_T:PP_T^N->T, quad V_m=(f_S)_* cal(O)_(PP_S^N) (m) tilde.eq cal(O)_S^(plus.o v_m), quad v_m=binom(N+m,N) $
并简记 $V_(m,T)=V_m times.o_(cal(O)_S) cal(O)_T$. 它就是 $T$ 上的 $m$ 次齐次多项式模.

#proposition(title:[平坦族给出局部自由商])[
  对 $Z in frak(Hilb)_(PP_S^N slash S)^P (T)$, 有正合列
  $ 0 -> (f_T)_* cal(I)_Z (m) -> V_(m,T) -> (f_T)_* cal(O)_Z (m) -> 0 $
  两端都有限局部自由, 秩分别为 $v_m-P(m)$ 与 $P(m)$, 且这条正合列与任意基变换相容. 这里将 $cal(I)_Z$ 与 $cal(O)_Z$ 都看作 $PP_T^N$ 上的层.
] <prop-hilbert-degree-quotient>

#proofsketch[
  $cal(O)_(PP_T^N)$ 与 $cal(O)_Z$ 都对 $T$ 平坦, 所以核 $cal(I)_Z$ 也对 $T$ 平坦. 由 @thm-hilbert-uniform-regularity 和 @prop-cm-consequences, 各条纤维上的 $cal(I)_Z (m)$ 没有高阶上同调; 由理想层的正合列, $cal(O)_Z (m)$ 也一样.

  上同调与基变换于是给出局部自由性和基变换相容性, 而 $R^1 (f_T)_* cal(I)_Z (m)=0$ 给出右端满射. 秩在纤维上计算即可. 非Noetherian参数上的结论, 可将有限表示的平坦族局部降到Noetherian情形再拉回. 参见 @Stacks26[Tags 07VK, 0B91].
]

右端满射所用的是 $H^1$ 的消失; 一般的直接像函子并不保持满射.

#proposition(title:[这个次数的方程恢复整个族])[
  对同一个 $Z$, 自然评价映射
  $ f_T^* ((f_T)_* cal(I)_Z (m)) times.o cal(O)(-m) ->> cal(I)_Z $
  满射. 因而 @prop-hilbert-degree-quotient 中的商唯一决定嵌入 $Z subset PP_T^N$.
] <prop-hilbert-reconstruction>

#proof[
  在每条纤维上, 满射性来自 @prop-cm-consequences. 由 @prop-hilbert-degree-quotient 的基变换相容性, 对评价映射的余核使用 Nakayama 引理, 就得到整个族上的满射.

  因此, 先取商映射的核, 再用这些 $m$ 次方程生成理想层, 就能恢复 $cal(I)_Z$, 也就恢复了 $Z$.
]

由 @thm-grassmann-representability, 取上述商得到自然变换
$ Phi_m:frak(Hilb)_(PP_S^N slash S)^P -> frak(Gr)_(P(m)) (V_m) $
@prop-hilbert-reconstruction 说明它对每个 $T$ 都单射. 接下来要把这个子函子具体构造为子概形.

=== 在Grassmann概形上构造候选族

令 $G=Gr_(P(m)) (V_m)$, 并写出它的万有正合列
$ 0 -> cal(K)_m -> V_(m,G) -> cal(Q)_m -> 0 $
在 $f_G:PP_G^N->G$ 上, 将万有核的截面当作方程, 得到复合映射
$ f_G^* cal(K)_m times.o cal(O)(-m) -> f_G^* V_(m,G) times.o cal(O)(-m) -> cal(O)_(PP_G^N) $

#definition(title:[万有候选闭子概形])[
  用上面映射的像作为理想层, 定义 $Z_G subset PP_G^N$, 即
  $ cal(O)_(Z_G)=coker(f_G^* cal(K)_m times.o cal(O)(-m) -> cal(O)_(PP_G^N)) $
  它把每个Grassmann点所选的 $m$ 次方程变成一个闭子概形.
] <def-hilbert-candidate>

余核与任意拉回相容, 所以这个构造对族同样有效. 但 $Z_G->G$ 一般还不平坦, 纤维的Hilbert多项式也未必是 $P$. 我们要从 $G$ 中取出恰好满足要求的部分.

#theorem(title:[前置定理: 泛平坦分层])[
  设 $Y->B$ 射影, $B$ 为Noetherian概形, $cal(F)$ 是 $Y$ 上的凝聚层, 并固定相对很丰富线丛来计算Hilbert多项式. 则存在有限个局部闭子概形 $B_Q subset B$, 以出现的纤维Hilbert多项式 $Q$ 标号, 满足:

  任意态射 $T->B$ 经过 $B_Q$, 当且仅当 $cal(F)_T$ 对 $T$ 平坦, 且每条纤维的Hilbert多项式都是 $Q$.

  这些 $B_Q$ 在点集上给出 $B$ 的分划. 存在性参见 @Nit05[定理 4.3]; 泛平坦分层的定义见 @Stacks26[Tag 052F].
] <thm-projective-flattening>

#proofsketch[
  对足够高的扭曲, 用直接像把问题转成底概形上有限模的秩条件, 再用 Fitting 理想给这些条件赋予概形结构. Noetherian性使所需条件可以有限地控制. 关键是这个结构满足任意 $T->B$ 下的上述性质, 因而也记录了非约化参数上的族.
]

#theorem(title:[Hilbert模函子的局部闭可表性])[
  对 $cal(O)_(Z_G)$ 使用 @thm-projective-flattening, 取多项式 $P$ 对应的局部闭子概形 $H=G_P$. 则
  $ Hom_S (T,H) tilde.eq frak(Hilb)_(PP_S^N slash S)^P (T) $
  自然地成立, 且 $H->G$ 是局部闭嵌入. 特别地, $H->S$ 有限型且分离.
] <thm-hilbert-locally-closed>

#proof[
  给定平坦族 $Z slash T$, @prop-hilbert-degree-quotient 给出 $T->G$. 由 @prop-hilbert-reconstruction, 候选族的拉回就是 $Z$, 所以此态射经过 $H$.

  反过来, 给定 $g:T->H$, 候选族的拉回 $Z_T slash T$ 平坦且多项式为 $P$. 原来的商诱导
  $ g^* cal(Q)_m -> (f_T)_* cal(O)_(Z_T) (m) $
  因为 $g^* cal(K)_m$ 中的方程在 $Z_T$ 上为零, 这个映射有定义; 由 @prop-hilbert-degree-quotient, 它满射. 两边都是秩 $P(m)$ 的局部自由模, 故它是同构. 所以从 $Z_T$ 取回的Grassmann数据恰好是原来的 $g$.

  两个构造互逆且与拉回相容, 因而得到所需的自然同构.
]

至此已经得到表示模函子的概形. 下一步用平坦极限说明它在 $G$ 中还是闭的.

=== 用唯一平坦极限证明射影性

#proposition(title:[DVR上的平坦延拓存在且唯一])[
  设 $R$ 是离散赋值环, 分式域为 $K$, 并给定 $Spec R->S$. 任意满足 $P_(Z_K)=P$ 的闭子概形 $Z_K subset PP_K^N$, 都唯一延拓为平坦闭子概形
  $ Z_R subset PP_R^N $
  其两条纤维的Hilbert多项式均为 $P$.
] <prop-hilbert-dvr-extension>

#proof[
  取 $Z_K$ 在 $PP_R^N$ 中的概形论闭包. 若 $pi.alt$ 是一致化参数, 在标准仿射开集 $Spec B$ 上, 设一般纤维的理想为 $J_K subset B[1\/pi.alt]$, 则闭包的理想是 $J=B inter J_K$. 因而
  $ B slash J -> B[1\/pi.alt] slash J_K $
  是单射. 右边没有 $R$-挠元, 所以左边也没有; DVR上的无挠模平坦, 故闭包对 $R$ 平坦. 它还是射影且有限表示的, 由 @prop-hilbert-flat-polynomial, 特殊纤维的多项式仍为 $P$.

  若另一个延拓也平坦, 它的坐标环同样没有 $R$-挠元, 因而理想必是 $J_K$ 的收缩 $B inter J_K$. 这就证明了唯一性. Hilbert函子的赋值判据也见 @Stacks26[Tag 0DM8].
]

#theorem(title:[Grothendieck存在定理: 射影空间情形])[
  表示概形 $H=Hilb_(PP_S^N slash S)^P$ 到 $G=Gr_(P(m)) (V_m)$ 的态射 $Phi_m$ 是闭嵌入. 特别地, $H->S$ 射影.
] <thm-hilbert-projective-space>

#proof[
  由 @thm-hilbert-locally-closed, $H slash S$ 有限型且分离. @prop-hilbert-dvr-extension 与Noetherian情形的赋值判据说明 $H slash S$ 固有, 参见 @Stacks26[Tag 0208].

  因为 $G slash S$ 分离, $H->G$ 可分解为闭的图像态射 $H->H times_S G$, 再接一个固有投影, 所以它也固有. 固有的局部闭嵌入就是闭嵌入, 参见 @Stacks26[Tag 01IQ]. 最后复合 @thm-plucker-closed-immersion, 得到
  $ H -> PP_S (and.big^(P(m)) V_m) $
  的闭嵌入.
]

这条证明的顺序是: 先由泛平坦分层得到有限型概形, 再用赋值判据证明固有, 最后得到射影性. 构造的完整版本见 @Nit05[第 5 节].

现在回到给定的闭嵌入 $X subset PP_S^N$. 还需把"候选子概形落在 $X$ 内"写成闭条件.

#proposition(title:[限制在闭子概形中是闭条件])[
  自然变换 $frak(Hilb)_(X slash S)^P -> frak(Hilb)_(PP_S^N slash S)^P$ 由闭嵌入
  $ Hilb_(X slash S)^P -> Hilb_(PP_S^N slash S)^P $
  表示. 因而 $Hilb_(X slash S)^P$ 存在, 且是射影 $S$-概形.
] <prop-hilbert-closed-ambient>

#proofsketch[
  记右边为 $H$, 其万有族为 $cal(Z) subset PP_H^N$, 结构态射为 $p:cal(Z)->H$, $pi:H->S$. 令 $cal(J)$ 为 $X subset PP_S^N$ 的理想层. 取 $a>=m$ 足够大, 使得
  $ f_S^* W_a ->> cal(J)(a), quad W_a=(f_S)_* cal(J)(a) $
  由 @prop-hilbert-degree-quotient, $cal(E)_a=p_* cal(O)_(cal(Z)) (a)$ 局部自由, 秩为 $P(a)$, 且与基变换相容. 限制方程得到
  $ theta:pi^* W_a -> cal(E)_a $
  对任意 $T->H$, 拉回族落在 $X_T$ 中, 当且仅当 $theta_T=0$: 左边的截面生成了 $X$ 的理想, 要求它们在族上全都为零即可.

  因为目标 $cal(E)_a$ 局部自由, 这个零条件由理想
  $ Im(pi^* W_a times.o cal(E)_a^or -> cal(O)_H) $
  定义, 所以得到所需的闭子概形. 这里无需 $W_a$ 局部自由, 也无需 $X slash S$ 平坦.
]

=== 万有族, 极化与函子性质

#proposition(title:[万有族与Hilbert极化])[
  记 $H=Hilb_(X slash S)^P$. 存在万有闭子概形 $cal(Z) subset X times_S H$, 其结构态射 $p:cal(Z)->H$ 平坦且射影, 并有正合列
  $ 0 -> cal(I)_(cal(Z)) -> cal(O)_(X times_S H) -> cal(O)_(cal(Z)) -> 0 $
  对任意 $T->S$, 自然双射
  $ Hom_S (T,H) tilde.eq frak(Hilb)_(X slash S)^P (T) $
  将 $g:T->H$ 送到 $cal(Z) times_H T subset X_T$. 因而 $H$ 是这个模问题的精模空间.

  对 $q>=m$, $cal(E)_q=p_* cal(O)_(cal(Z)) (q)$ 局部自由, 秩为 $P(q)$, 且与任意基变换相容. 特别地, 线丛
  $ lambda_m:=det cal(E)_m $
  是Grassmann-Plücker线丛的拉回, 因而对 $H slash S$ 相对很丰富.
] <prop-hilbert-universal-polarization>

#proof[
  万有族对应于 $id_H$, 这正是 @prop-yoneda-family. 局部自由性由 @prop-hilbert-degree-quotient 得到, 而 $lambda_m$ 的描述来自 @lem-plucker-line-bundle. 因为构造中的 $H->G$ 是闭嵌入, 拉回的线丛相对很丰富.
]

#remark[
  $cal(I)_(cal(Z))$ 一般不是向量丛. Grassmann概形上的 $cal(K)_m$ 只记录足够高次数的方程, 它与整个理想层是不同的对象. 不过上面的万有正合列沿任意 $T->H$ 拉回仍正合, 因为 $cal(O)_(cal(Z))$ 对 $H$ 平坦.
]

#proposition(title:[基变换与辅助选择])[
  对任意 $S'->S$, 有典范同构
  $ Hilb_(X slash S)^P times_S S' tilde.eq Hilb_(X_(S') slash S')^P $
  右边使用拉回的极化, 万有族也随之拉回. 改用另一个足够大的整数 $m$, 得到的表示概形仍典范同构.
] <prop-hilbert-base-change>

#proof[
  两边表示同一个 $S'$ 上的模函子, 由 Yoneda 引理即得. 更换 $m$ 时理由相同.
]

Hilbert模函子本身只依赖 $X slash S$. 选定 $cal(O)_X (1)$ 后才有固定多项式 $P$ 的分类, 选定次数 $m$ 后才有上述具体的Grassmann嵌入.

#block(breakable: false)[
#proposition(title:[完整Hilbert概形及开, 闭环境])[
  对上述射影 $X slash S$, 完整Hilbert模函子由
  $ Hilb_(X slash S)=coprod_P Hilb_(X slash S)^P $
  表示, 每一项都是开闭子概形.

  若 $Y subset X$ 为闭子概形, 则 $Hilb_(Y slash S)->Hilb_(X slash S)$ 是闭嵌入. 若 $U subset X$ 为开子概形, 则
  $ Hilb_(U slash S)->Hilb_(X slash S) $
  是开嵌入; 这里 $U$ 中的族仍须对参数概形固有.
] <prop-hilbert-open-closed>
]

#proofsketch[
  由 @prop-hilbert-flat-polynomial, 任意参数概形 $T$ 按纤维的多项式分成开闭部分, 每一部分上的族对应一个 $Hilb^P$ 的态射, 合起来即得到到上述不交并的态射. 闭嵌入的结论由 @prop-hilbert-closed-ambient 得到.

  对开子概形, 在每个 $Hilb^P$ 上取万有族与 $(X without U) times_S Hilb^P$ 相交的闭集. 它到 $Hilb^P$ 的像是闭的, 因为万有族固有. 去掉这个像, 剩下的恰好参数化完全落在 $U$ 内的族. 参见 @Stacks26[Tag 0DPE].
]

#remark(title:[结论的适用范围])[
  每个固定 $P$ 的部分都射影, 但完整 $Hilb_(X slash S)$ 可能有无穷多个非空的开闭部分, 从而不是有限型, 也就不能直接称它为射影概形.

  对拟射影环境, 可先取射影闭包, 再用 @prop-hilbert-open-closed 取开子概形. 更一般地, 对分离, 有限表示的 $X slash S$, Hilbert函子可由代数空间表示; 射影性需要额外条件. 参见 @Stacks26[Tags 0CZX, 0DM5].
]

=== 怎样想象与使用Hilbert概形

在基域 $k$ 上, 可以把 $H=Hilb_(X slash k)^P$ 想成一张记录"$X$ 内各种子概形"的参数表. 点 $[Z]$ 记录一个嵌入 $Z subset X$, 万有族在这个点上方放着整个 $Z$. 一条态射 $T->H$ 则让这些子概形随 $T$ 平坦地变化. 其中 $T$ 也可以带幂零元, 因而 $H$ 的概形结构还记录无穷小变化.

选定足够大的 $m$ 后, 这张参数表有了有限的线性代数描述:
$ [Z] |-> [V_m ->> H^0 (Z,cal(O)_Z (m))] $
核是所有在 $Z$ 上为零的 $m$ 次方程. Hilbert概形在Grassmann概形中挑出的, 正是能生成指定多项式的平坦子概形族的那些商.

实际使用时, 常见的做法有下面几种.

- *构造一族.* 在 $X_T$ 中写出方程, 检查所得 $Z->T$ 平坦且多项式为 $P$, 就自动得到分类态射 $T->H$. 通常只需描述这个族, 不必先算出 $H$ 的全部方程.
- *研究退化.* 前面#link(<ex-hilbert-collision>)[两点碰合的例子]给出 $AA_k^1->Hilb_(PP_k^1 slash k)^2$: 两个点靠拢, 最后成为长度为 $2$ 的非约化点. 对DVR上的族, @prop-hilbert-dvr-extension 告诉我们怎样取唯一的平坦极限. 算理想时, 应从一般纤维收缩回来; 直接把任意一组选取的方程代入 $t=0$, 未必得到平坦极限.
- *在局部坐标里计算.* 取Grassmann标准图, 把商写成前文的标准矩阵. 它的核给出一组随矩阵系数变化的 $m$ 次方程, Hilbert概形的闭条件再选出合法的族. 若只想研究 $[Z]$ 附近, 往往只需这一张图.
- *研究一阶变化.* 把参数取成 $T=Spec(k[epsilon] slash (epsilon^2))$, 并要求唯一的点映到 $[Z]$. 得到的 $T->H$ 就是 $H$ 在 $[Z]$ 处的切向量, 也就是 $Z$ 在固定 $X$ 中的一阶嵌入变形.

#block(breakable: false)[
#example(title:[在仿射直线上, 又回到了多项式的系数])[
  固定 $d>=1$. 对 $X=AA_k^1$, 长度为 $d$ 的Hilbert概形满足
  $ Hilb_(AA_k^1 slash k)^d tilde.eq AA_k^d $
  这里上标 $d$ 表示常数Hilbert多项式 $P equiv d$. 万有族就是前文的首一多项式族
  $ Spec(k[a_0,dots,a_(d-1),x] slash (x^d+sum_(i=0)^(d-1) a_i x^i)) -> AA_k^d $
  确实, 对任意参数 $T$, 长度 $d$ 的族有限平坦, 其坐标代数以 $1,x,dots,x^(d-1)$ 为基: 这可在各条纤维上检查, 再用 Nakayama 引理提升. 写出 $x^d$ 在这组基下的展开, 就唯一得到这些系数.

  当 $d=2$ 时, 两点碰合的族 $x(x-t)=x^2-t x$ 对应系数空间中的直线 $(a_0,a_1)=(0,-t)$. 所谓退化, 在这里就是沿这条直线走到原点; 原点上方的万有族纤维是 $Spec(k[x] slash (x^2))$.
]
]
