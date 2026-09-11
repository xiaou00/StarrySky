#import "../template.typ":*
#import "@preview/fletcher:0.5.8": diagram, edge

#show: doc => conf(easy: true, doc,)

= 高阶 $K$-理论 / Higher $K$-Theory <chap-higher-k-theory>

== 从低阶 $K$ 群出发 <sec-higher-k-motivation>

前面已经构造了 $K_0$, $K_1$ 与 $K_2$. 现在把它们放进同一个构造, 并按同样的规律继续定义更高次的群. 以下先以含幺环 $R$ 为例, $cat("Proj")(R)$ 仍表示有限生成投射右 $R$-模的范畴.

在#chapter-ref(<chap-k0>)中, 我们从对象的同构类出发, 把直和写成加法:
$ [P plus.o Q]=[P]+[Q] $
再加入形式加法逆, 得到由虚拟差 $[P]-[Q]$ 组成的 $K_0 (R)$. 因而 $K_0$ 关心的是对象的加法分类. 在域上, 有限维向量空间由维数确定, 所以 $K_0 (F)=ZZ$. 在#chapter-ref(<chap-perfect-complex>)中, 同一原则用于余纤维序列 $A->B->C$, 要求 $[B]=[A]+[C]$: 对象的分解对应类的相加.

同一个对象还可以有不同的自同构. 它们不改变对象的 $K_0$ 类, 因而需要进一步记录. 在#chapter-ref(<chap-k1>)中, 我们先用补模把投射模的自同构放进矩阵群, 再稳定化并 Abel 化, 得到
$ K_1 (R)=GL(R)^"ab"=GL(R) slash E(R) $
这里复合对应加法 $[g h]=[g]+[h]$, 初等变换的类为零. 所以 $K_1$ 记录稳定自同构的加性信息. 对域, 行列式给出 $K_1 (F)=F^times$: 即使维数相同, 自同构仍然可以有不同的行列式.

接着考察乘积为单位矩阵的初等变换序列. 它在 $K_1$ 中给出零, 序列本身却可能保留更多信息. 在#chapter-ref(<chap-k2>)中, 我们将初等矩阵换成抽象生成元, 只加入 Steinberg 关系, 得到
$ K_2 (R)=ker ("St"(R)->E(R)) $
这样的序列仍可能给出非零的 $K_2$ 类, 例如 $K_2 (RR)$ 中的 ${-1,-1}$. 前两次矩阵构造由同一条正合列连在一起:
$ 1->K_2 (R)->"St"(R)->GL(R)->K_1 (R)->1 $

这三步提示了一条继续推广的路线:
$ "对象的加法分类" -> "稳定自同构" -> "变换之间的关系" -> "更高相容关系" $
每一步都继续记录前一步中尚未区分的信息, 同时保留直和带来的可加性.

同伦论提供了适合表达这种递进的语言. 对投射模, 可以先把对象及其同构组织成空间, 用直和赋予它相容的交换加法, 再做*空间层面的群完备化*. 在连通分支上, 这仍然是构造 $K_0$ 时的群完备化; 整个空间还会保留群完备化后的闭路与更高同伦信息.

下面先对稳定范畴用滤过与余纤维构造连通 $K$ 谱, 再加入负次数, 得到 $K(C)$. 随后介绍普通正合范畴的 $Q$ 构造, 说明它与前面的模型怎样相接, 最后用可加性, 分解与局部化做计算.

本章始终将 $K^"cn"$ 用于连通谱, 将 $K$ 用于非连通谱. 上一章的 Milnor 群仍记为 $K_n^M$; 它们通过域的单位符号定义. 对域, 两种群在次数 $0,1,2$ 相同, 更高次则需要区分.

== 稳定范畴的 $K$ 谱 <sec-k-spectrum-definition>

记 $Cat_oo^"perf"$ 为小的, 幂等完备的稳定 $oo$-范畴与正合函子组成的 $oo$-范畴. 这里正合是指保持有限余极限, 等价地保持有限极限. 例如#chapter-ref(<chap-perfect-complex>)中的 $cat("Perf")(X)$, 选取小模型后就是其中的对象. 定义 $K$ 谱本身不要求 $C$ 带有张量积.

=== Waldhausen 的 $S_bullet$ 构造 <sec-waldhausen-s-construction>

一个对象的分解, 可以用滤过 $0=X_0->X_1->dots->X_n$ 记录. 为了让取子滤过与取商相容, 我们同时记下所有余纤维 $X_j slash X_i:=cofib(X_i->X_j)$.

为了同时排列这些商, 使用箭头范畴 $cat("Arr")([n])=Fun([1],[n])$. 它把箭头 $i->j$ 当作对象, 把交换方块当作态射. 记这个对象为 $(i,j)$, 就得到下面的图表.

#definition(title: [$S_bullet$ 构造])[
  记 $cat("Arr")([n])$ 为 $[n]={0<dots<n}$ 的箭头范畴. 它的对象是 $(i,j)$, 其中 $0<=i<=j<=n$; 当 $i<=i'$ 且 $j<=j'$ 时, 有唯一的态射 $(i,j)->(i',j')$, 否则没有态射.

  定义 $S_n C$ 为满足以下条件的图表 $F:cat("Arr")([n])->C$ 组成的范畴:
  - $F_(i i) tilde.eq 0$.
  - 对 $i<=j<=k$, 图表诱导的典范映射
    $ F_(i k) coprod_(F_(i j)) 0 -> F_(j k) $
    是等价. 即 $F_(i j)->F_(i k)->F_(j k)$ 是余纤维序列, 零化同伦来自 $F_(j j) tilde.eq 0$.

  对保序映射 $alpha:[m]->[n]$, 沿 $(i,j) mapsto (alpha(i),alpha(j))$ 预合成. 这些函子使 $S_bullet C$ 成为单纯稳定 $oo$-范畴.
] <def-waldhausen-s-construction>

取 $n=2$, 把对象 $(i,j)$ 直接标成它代表的箭头 $i->j$. 方框之间的箭头才是 $cat("Arr")([2])$ 中的态射:

#figure(
  {
    let edge = fletcher.edge
    let node = fletcher.node
    grid(
      columns: (1.3fr, 1fr), column-gutter: 28pt, row-gutter: 10pt,
      align: center + horizon,
      [$cat("Arr")([2])$], [经 $F$ 得到推出方块],
      fletcher.diagram(
        spacing: (17pt, 19pt), node-inset: 5pt,
        node-fill: mist, node-stroke: .5pt + rule-c, node-corner-radius: 3pt,
        edge-stroke: .75pt + muted,
        $
          node(0->0) edge(->) &
          node(0->1, stroke: #blue) edge(->, stroke: #blue) edge("d", ->, stroke: #blue) &
          node(0->2, stroke: #blue) edge("d", ->, stroke: #blue) \
          & node(1->1, stroke: #blue) edge(->, stroke: #blue) &
          node(1->2, stroke: #blue) edge("d", ->) \
          & & node(2->2)
        $,
      ),
      {
        set text(fill: black)
        fletcher.diagram(
          spacing: (35pt, 32pt), edge-stroke: .65pt + black,
          $
            A edge(f, ->) edge("d", ->) & B edge("d", q, ->, label-side: #left) \
            0 edge(->) & D
          $,
        )
      },
    )
  },
  caption: [左图向右增大 $j$, 向下增大 $i$. 蓝框选出中央交换方块; 右图是它在 $S_2 C$ 中的取值, 其中 $f$ 的余纤维是 $D$.],
) <fig-arr2-s-construction>

左图只画出生成箭头; 其余态射由复合得到, 同起点和终点的路径表示同一个态射. 例如 $(0,1)->(1,2)$ 的两条路径组成蓝色交换方块. 经 $F$ 后, 它成为右图的推出方块, 所以 $D tilde.eq B coprod_A 0 tilde.eq cofib(f)$; 对应的滤过是 $0->A->B$.

一般地, $X_j=F_(0 j)$, $F_(i j) tilde.eq X_j slash X_i$. 因此 $S_0 C$ 只含零对象, $S_1 C tilde.eq C$; 更高的 $S_n C$ 记录多步滤过及其相容的商. 参见 @BGT13[定义 7.1 与引理 7.3].

单纯结构也有直接含义. 面映射 $d_i$ 在 $i>0$ 时删去滤过的第 $i$ 项, 而 $d_0$ 把整条滤过改成对 $X_1$ 取商; 退化映射 $s_i$ 则重复第 $i$ 项, 插入一个恒等箭头. 对 $0->A->B$, 三个面分别是
$ d_0 F=D, quad d_1 F=B, quad d_2 F=A $
所以一次余纤维分解自然带有三条边, 这正是下一步几何实现需要的二维单形.

=== 连通 $K$ 谱 <sec-connective-k-spectrum>

沿用#chapter-ref(<chap-animae>)的核心记号 $C^(tilde.eq)$, 即只保留对象与等价所得的生象. 对 $S_n C$ 取核心时, 滤过和余纤维仍保存在对象里, 图表之间只保留等价及其高阶同伦.

接着做几何实现, 即在生象中取这个单纯图表的余极限. 直观上, 它把各维单形按面映射粘起来, 并按退化映射识别重复的数据. 对 $r>=0$, 记
$ X_r (C):=lr(|(S_bullet^r C)^(tilde.eq)|) $
其中 $S_bullet^r$ 表示在 $r$ 个单纯方向反复应用 $S_bullet$, 竖线表示在所有方向取几何实现; 特别地, $X_0 (C)=C^(tilde.eq)$. 零图表给出基点.

第一次实现中, $S_0 C$ 的核心可缩, 可以看成一个基点. 每个对象 $A in S_1 C$ 给出一条两端都在这个基点的边. 一个 $F in S_2 C$ 则填入下面的三角形:

#align(center,
  {
    set text(fill: black)
    simplex2($*$, $*$, $*$,
      ab: $A$, bc: $D$, ac: $B$,
      edge-stroke: .65pt + black,
    )
  },
) <fig-s2-additivity-simplex>

三个顶点最终都粘到同一基点. 三条边分别是 $d_2 F=A$, $d_0 F=D$, $d_1 F=B$. 二维单形 $F$ 将路径 $A$ 接 $D$ 与路径 $B$ 联系起来, 给出 $K_0 (C)$ 中的关系 $[B]=[A]+[D]$.

取环路空间 $Omega X_1 (C)$ 后, 上述闭路成为点, 三角形给出这些点之间的加法关系. 继续应用 $S_bullet$, 可以构造它的解环路. 例如 $S_bullet^2 C$ 逐项取核心后形成双单纯生象, 再沿两个方向取几何实现, 得到 $X_2 (C)$.

在已经迭代的图表上逐项应用上述闭路构造, 得到自然映射
$ X_r (C)->Omega X_(r+1) (C) $
*Waldhausen 可加性定理*保证它们在 $r>=1$ 时是等价. 因而下面的各层确实组成#chapter-ref(<chap-spectra>)意义下的 $Omega$-谱. 这里引用该定理, 参见 @BGT13[§7.1--7.2].

#definition(title: [连通代数 $K$ 谱])[
  对 $C in Cat_oo^"perf"$, 定义 $K^"cn" (C)$ 为各层
  $ K^"cn" (C)_r:=Omega X_(r+1) (C) quad (r>=0) $
  及上述相容环路等价组成的谱. 它是连通谱, 且
  $ Omega^oo K^"cn" (C) tilde.eq Omega lr(|(S_bullet C)^(tilde.eq)|) $
  右边称为 $C$ 的*代数 $K$ 理论空间*. 对 $n>=0$, 暂记
  $ K_n^"cn" (C):=pi_n K^"cn" (C) $
] <def-connective-k-spectrum>

这里 $r$ 是谱的层号, $n$ 是同伦群的次数. 各层通过环路等价接在一起, 将对象的类, 闭路与更高同伦组织成同一个谱. 连通是指负次同伦群为零; 它的 $K$ 理论空间仍可有多个连通分支, 由 $K_0$ 标记.

正合函子保持零对象和余纤维, 因而作用于上面的全部图表, 给出函子 $K^"cn":Cat_oo^"perf"->Sp_(>=0)$.

在零次, $S_1 C$ 中的对象给出生成元, $S_2 C$ 中的余纤维序列给出关系
$ [B]=[A]+[D] quad (A->B->D) $
所以 $pi_0 K^"cn" (C)$ 就是#chapter-ref(<chap-perfect-complex>)中定义的 Grothendieck 群. 例如 $A->0->A[1]$ 给出 $[A[1]]=-[A]$, 因而在 $cat("Perf")(k)$ 中有 $[k plus.o k[1]]=0$.

=== 非连通延拓 <sec-nonconnective-k-spectrum>

连通构造已经包含全部非负次信息. 要加入负次数, 先把 $C$ 嵌入一个 $K$ 理论可由 Eilenberg 消去法消掉的范畴, 再取商. 这个商扮演范畴悬挂的角色, 所以先定义所需的 Verdier 商.

#definition(title: [Verdier 商])[
  设 $i:A->B$ 是小稳定 $oo$-范畴之间的全忠实正合函子. *Verdier 商* $B slash A$ 是一个小稳定 $oo$-范畴, 配有正合函子
  $ q:B->B slash A, quad q compose i tilde.eq 0 $
  并满足以下泛性质. 对任意小稳定 $oo$-范畴 $D$, 沿 $q$ 预合成给出等价
  $ Fun^"ex" (B slash A,D) tilde.eq {F in Fun^"ex" (B,D) | F compose i tilde.eq 0} $
  这里 $Fun^"ex"$ 取正合函子, 右边取将 $A$ 送到零的那些函子.
] <def-verdier-quotient>

这一步把 $A$ 中对象的像变成零. 若一个态射的余纤维属于 $A$, 取商后它的余纤维为零, 所以它变成等价. 反过来, 将这些态射局部化就得到 $B slash A$. 例如 $B slash 0 tilde.eq B$, $B slash B tilde.eq 0$.

这个商中可能出现尚未分裂的幂等图表. 上标 $"idem"$ 表示补入这些图表的分裂, 使所有收缩对象都存在; 这样便回到 $Cat_oo^"perf"$ 中. 商的存在及其性质参见 @BGT13[§5].

#definition(title: [稳定范畴的正合列])[
  $Cat_oo^"perf"$ 中的序列 $A->^i B->^p C$ 称为*正合列*, 若 $i$ 全忠实, 配有 $p compose i tilde.eq 0$, 且诱导等价
  $ (B slash A)^"idem" tilde.eq C $
] <def-stable-category-exact-sequence>

也就是说, 在 $B$ 中把 $A$ 的对象置零, 再补齐收缩对象, 得到 $C$.

固定不可数正则基数 $kappa$. 记 $op("Ind")(C)$ 为给 $C$ 添入滤过余极限得到的范畴, 上标 $kappa$ 表示 $kappa$-紧对象, 即其映射空间函子保持 $kappa$-滤过余极限.

$op("Ind")$ 添入了接下来需要的可数直和. 再取 $kappa$-紧对象, 则能在保留这些直和的同时控制范畴的大小. $kappa$ 是构造中的辅助选择.

#definition(title: [范畴悬挂])[
  对 $C in Cat_oo^"perf"$, 定义
  $ cal(F)_kappa (C):=op("Ind")(C)^kappa, quad
    Sigma_kappa C:=(cal(F)_kappa (C) slash C)^"idem" $
  这里通过 Yoneda 嵌入将 $C$ 看作 $cal(F)_kappa (C)$ 中的子范畴. 两者都取小模型, 并得到自然的正合列
  $ C->cal(F)_kappa (C)->Sigma_kappa C $
] <def-category-suspension>

$cal(F)_kappa (C)$ 本质小, 并有可数直和. 对正合自函子 $T(M):=plus.o.big_(j>=0) M$, 有自然等价 $"id" plus.o T tilde.eq T$. 可加性定理于是给出
$ K^"cn" (cal(F)_kappa (C)) tilde.eq 0 $
因为可数份 $M$ 再加一份仍可通过重编号识别, 可加性给出 $"id"+K^"cn" (T) tilde.eq K^"cn" (T)$, 从而恒等谱态射为零. 这正是 Eilenberg 消去法.

因此 $cal(F)_kappa (C)$ 在 $K$ 理论下起到可缩锥的作用, 对其中的 $C$ 取商就类似于把锥的底部压成一点. 不可数性保证可数直和仍在所选的小模型中, 参见 @BGT13[定义 9.1 与引理 9.4].

上面正合列的复合函子带有零化同伦. 经 $K^"cn"$ 后, 由余纤维的泛性质得到比较映射
$ cofib(K^"cn" (C)->K^"cn" (cal(F)_kappa (C)))->K^"cn" (Sigma_kappa C) $
中间的谱为零, 因而左边就是 $K^"cn" (C)$ 的悬挂. 这个映射写成
$ Sigma K^"cn" (C)->K^"cn" (Sigma_kappa C) $
取伴随, 得到自然映射 $eta_C:K^"cn" (C)->Omega K^"cn" (Sigma_kappa C)$. 这里左边的 $Sigma$ 是谱的悬挂, $Sigma_kappa$ 是刚定义的范畴悬挂.

#definition(title: [非连通代数 $K$ 谱])[
  对 $C in Cat_oo^"perf"$, 定义
  $ K(C):=varinjlim(r>=0) Omega^r K^"cn" (Sigma_kappa^r C) in Sp $
  其中 $Sigma_kappa^0 C=C$, 过渡映射由 $eta_(Sigma_kappa^r C)$ 再取 $r$ 次环路得到. 对每个整数 $n$, 定义
  $ K_n (C):=pi_n K(C) $
] <def-algebraic-k-spectrum>

这里 $Omega$ 作用在谱上, 是逆悬挂 $E mapsto E[-1]$. 因为 $K^"cn"$ 没有负次同伦群, 第 $r$ 个阶段 $Omega^r K^"cn" (Sigma_kappa^r C)$ 的同伦群只可能出现在 $n>=-r$. 所以这些阶段逐步容纳越来越低的次数:

#figure(
  {
    let edge = fletcher.edge
    let node = fletcher.node
    let stage(body, bound) = stack(
      dir: ttb, spacing: 6pt, body,
      text(size: 9pt, fill: muted, bound),
    )
    let first = stage($K^"cn" (C)$, $n>=0$)
    let second = stage($Omega K^"cn" (Sigma_kappa C)$, $n>=-1$)
    let third = stage($Omega^2 K^"cn" (Sigma_kappa^2 C)$, $n>=-2$)
    let result = stack(dir: ttb, spacing: 5pt, $K(C)$, text(size: 9pt, fill: blue, [顺序余极限]))
    set text(size: 9.5pt)
    fletcher.diagram(
      spacing: (19pt, 30pt), node-inset: 6pt, edge-stroke: .75pt + muted,
      node-fill: mist, node-stroke: .5pt + rule-c, node-corner-radius: 3pt,
      $
        node(#first) edge(->) edge("dr", ->, stroke: #blue) &
        node(#second) edge(->) edge("d", ->, stroke: #blue) &
        node(#third) edge(->) edge("dl", ->, stroke: #blue) &
        node(dots, fill: #none, stroke: #none) \
        & node(#result, stroke: #blue) & &
      $,
    )
  },
  caption: [每个方框标出允许出现同伦群的次数. 横向过渡由 $eta$ 给出, 蓝色箭头是各阶段到 $K(C)$ 的相容结构映射.],
) <fig-nonconnective-k-stages>

非连通化定理保证, 所得谱与 $kappa$ 的选择无关, 且自然映射 $K^"cn" (C)->K(C)$ 诱导等价
$ K^"cn" (C) tilde.eq tau_(>=0) K(C) $
这里 $tau_(>=0)$ 取连通覆盖, 即只保留非负次同伦群. 因而上述等价说明加入负次数后, 已有的 $K_0,K_1,K_2,dots$ 都保留下来. 整个构造给出函子 $K:Cat_oo^"perf"->Sp$. 构造及比较结果参见 @BGT13[定义 9.6 与注 9.33].

对环或环谱 $R$, 以及#chapter-ref(<chap-perfect-complex>)中的预层 $X$, 统一记
$ K(R):=K(cat("Perf")(R)), quad K(X):=K(cat("Perf")(X)) $
这一步先把环或空间转换为完美对象的范畴, 再使用同一套 $K$ 构造.
对普通环 $R$, 比较定理说明 $pi_1 K(R)$ 与 $pi_2 K(R)$ 分别恢复#chapter-ref(<chap-k1>)与#chapter-ref(<chap-k2>)的矩阵定义, 而 $pi_(-1) K(R)$ 恢复#chapter-ref(<chap-k1>)中的 Bass 负一次群. 各个 $K_n$ 因而是同一个谱在不同次数上的同伦群.

=== 几个例子 <sec-k-spectrum-examples>

下面也简记 $K^"cn" (R):=K^"cn" (cat("Perf")(R))$, 对概形采用同样的约定. 比较映射 $K^"cn" (C)->K(C)$ 是等价, 当且仅当 $K_n (C)=0$ 对所有 $n<0$ 成立.

#example(title: [零范畴])[
  若 $C=0$, 所有滤过都只有零对象, 各次几何实现都可缩. 因而
  $ K^"cn" (0) tilde.eq K(0) tilde.eq 0 $
  右边是零谱, 所有同伦群都为零.
] <ex-k-spectrum-zero>

#example(title: [域与有限域])[
  对域 $k$, 完美复形就是有界有限维向量空间复形. 正则 Noetherian 环的负 $K$ 群全部消失, 所以
  $ K^"cn" (cat("Perf")(k)) tilde.eq K(cat("Perf")(k))=K(k) $
  其低次同伦群是 $pi_0 K(k)=ZZ$, $pi_1 K(k)=k^times$, 而 $pi_2 K(k)$ 由#chapter-ref(<chap-k2>)的 Matsumoto 定理描述. 负次消失见 @Wei13[III, §4].

  若 $k=bb(F)_q$ 是有限域, Quillen 的计算进一步给出
  $ K_n (bb(F)_q) tilde.eq cases(
      0 & quad n<0,
      ZZ & quad n=0,
      ZZ slash (q^r-1) & quad n=2r-1 quad (r>=1),
      0 & quad n=2r quad (r>=1),
    ) $
  这里引用 @Wei13[IV, 推论 1.13]. 例如 $K_1 (bb(F)_2)=K_2 (bb(F)_2)=0$, 但 $K_3 (bb(F)_2) tilde.eq ZZ slash 3$. 与之相比, #link(<ex-milnor-finite-real>)[有限域的 Milnor 群]在次数 $n>=2$ 都为零. 这给出了两种高阶理论不同的具体例子.
] <ex-k-spectrum-finite-fields>

#example(title: [直积与矩阵环])[
  对 $C,D in Cat_oo^"perf"$, 滤过与余纤维逐分量计算, 可加性给出
  $ K^"cn" (C times D) tilde.eq K^"cn" (C) plus.o K^"cn" (D), quad
    K(C times D) tilde.eq K(C) plus.o K(D) $
  特别地, $cat("Perf")(R times S) tilde.eq cat("Perf")(R) times cat("Perf")(S)$, 所以环的有限乘积对应 $K$ 谱的有限直和.

  Morita 等价给出 $cat("Perf")(M_m (R)) tilde.eq cat("Perf")(R)$, 因而
  $ K^"cn" (M_m (R)) tilde.eq K^"cn" (R), quad K(M_m (R)) tilde.eq K(R) quad (m>=1) $
  这将#chapter-ref(<chap-k1>)与#chapter-ref(<chap-k2>)中的 Morita 不变性统一到了谱的层面.
] <ex-k-spectrum-products-morita>

#example(title: [射影直线])[
  设 $k$ 是域, $p:bb(P)_k^1->Spec k$. 射影丛公式给出
  $ K^"cn" (bb(P)_k^1) tilde.eq K^"cn" (k) plus.o K^"cn" (k), quad
    K(bb(P)_k^1) tilde.eq K(k) plus.o K(k) $
  从右边到左边的映射由两个正合函子
  $ P mapsto p^* P, quad Q mapsto p^* Q times.o cal(O)(-1) $
  相加得到. 两份分别对应线丛 $cal(O)$ 与 $cal(O)(-1)$; 公式见 @Wei13[V, 定理 1.5]. 因为 $K(k)$ 连通, 这里两个版本也相同. 特别地,
  $ K_0 (bb(P)_k^1) tilde.eq ZZ plus.o ZZ, quad K_1 (bb(P)_k^1) tilde.eq k^times plus.o k^times $
] <ex-k-spectrum-projective-line>

#example(title: [粘合两点的曲线])[
  回到#chapter-ref(<chap-k1>)中#link(<ex-negative-k-node>)[粘合两点的例子]. 设 $k$ 是域, 令
  $ R={f in k[t] | f(0)=f(1)}, quad C=cat("Perf")(R) $
  前面已经算出 $K_(-1) (R) tilde.eq ZZ$, 因而
  $ pi_(-1) K(C) tilde.eq ZZ, quad pi_(-1) K^"cn" (C)=0 $
  所以 $K^"cn" (C)->K(C)$ 不是等价. 非连通版本保留了两个粘合点上秩之差所给出的障碍.

  不过它们仍有相同的零次无限环路空间:
  $ Omega^oo K^"cn" (C) tilde.eq Omega^oo K(C) $
  因为 $Omega^oo$ 只看到非负次同伦信息. 要保留这里的负群, 就需要整个谱.
] <ex-k-spectrum-negative-node>

=== 局部化与泛性质 <sec-k-theory-localizing-property>

上面的构造还满足一个重要性质: 范畴的正合列会变成谱的余纤维序列. 先把这个性质单独命名, 再说明它给出的另一种 $K$ 谱刻画.

#definition(title: [局部化不变量])[
  对稳定可呈示 $oo$-范畴 $D$, 称 $E:Cat_oo^"perf"->D$ 为*局部化不变量*, 若它保持滤过余极限, 满足 $E(0) tilde.eq 0$, 并将每条正合列送到余纤维序列
  $ E(A)->E(B)->E(C) $
  记这些函子组成的范畴为 $Fun_("loc") (Cat_oo^"perf",D)$.
] <def-localizing-invariant>

正合列把范畴分成子范畴与商. 局部化条件要求这种分解在 $D$ 中成为余纤维关系; 当 $D=Sp$ 时, 就能用同伦群的长正合列比较各部分. 保持滤过余极限则保证逐步拼合范畴时, 不变量也能按相同过程拼合.

非连通 $K$ 理论是局部化不变量. 特别地, 正合列 $A->B->C$ 给出谱的余纤维序列 $K(A)->K(B)->K(C)$, 取同伦群便得到延伸到所有整数次数的长正合列. 这是非连通延拓的局部化定理, 参见 @BGT13[§9].

#definition(title: [局部化非交换动机范畴])[
  *局部化非交换动机范畴* $bold(cal(M))_"loc"$ 是一个稳定可呈示 $oo$-范畴, 配有局部化不变量
  $ U_("loc"):Cat_oo^"perf"->bold(cal(M))_"loc" $
  使对每个稳定可呈示 $oo$-范畴 $D$, 沿 $U_"loc"$ 预合成给出等价
  $ Fun^L (bold(cal(M))_"loc",D) tilde.eq Fun_("loc") (Cat_oo^"perf",D) $
  左边取保持小余极限的函子. 称 $U_"loc"$ 为*普遍局部化不变量*, $U_("loc") (C)$ 为 $C$ 的局部化非交换动机.
] <def-localizing-motives>

每个局部化不变量都通过 $U_"loc"$ 分解, 且相容分解的选择空间可缩. 这个泛性质将 $(bold(cal(M))_"loc",U_"loc")$ 确定到等价; 存在性见 @BGT13[定理 1.1 与 8.7].

因此, 局部化动机范畴同时容纳了这些不变量. 对 $K$ 理论, 下面的定理将它识别为从一个固定对象出发的映射谱. 这是已有构造的泛性质刻画.

#theorem(title: [$K$ 谱的动机刻画])[
  对 $C in Cat_oo^"perf"$, 有自然的谱等价
  $ K(C) tilde.eq underline(Map)_(bold(cal(M))_"loc") (U_("loc") (Sp^omega),U_("loc") (C)) $
  其中 $Sp^omega=cat("Perf")(SS)$ 是紧谱组成的范畴. 这里引用 @BGT13[定理 1.3 与 9.8].
] <thm-k-spectrum-corepresentability>

== Quillen 的 $Q$ 构造 <sec-quillen-q>

回到普通范畴, 也可以直接用短正合列构造 $K$ 理论空间. Quillen 的做法是把子商关系组织成一个新范畴 $Q cal(E)$, 再取分类空间与环路空间:
$ cal(E) mapsto Q cal(E) mapsto B Q cal(E) mapsto Omega B Q cal(E) $
一条短正合列会在 $B Q cal(E)$ 中产生路径之间的关系, 给出 $K_0$ 的加法; 更高维的单形则继续保留相容的子商数据. 关键是把这些数据放进 $Q cal(E)$ 的态射与复合中.

下面先定义正合范畴与 $Q$ 构造, 验证它恢复 $K_0$, 再用滤过与前面的 $S_bullet$ 模型比较. 主要参考 @Wei13[IV, §6--§8]; 正合范畴的公理与图表引理参见 @Buh10[§2--§3]. 本节的普通范畴都假设本质小, 并选取小模型.

=== 正合范畴 <sec-q-exact-categories>

Abel 范畴中的每条短正合列都可以使用. 对投射模或向量丛, 我们只保留三项仍在原范畴中的短正合列. 正合范畴把这种选择抽象出来.

#definition(title: [正合范畴])[
  *正合范畴*是加性范畴 $cal(E)$, 连同一类指定的核--余核对
  $ A ->^i B ->^p C, quad i=ker p, quad p=coker i $
  称为*容许短正合列*. 其中的 $i$ 称为*容许单态射*, $p$ 称为*容许满态射*, 分别记作 $A arrow.r.hook B$ 与 $B ->> C$. 指定的序列满足:
  + 对图表同构封闭, 并包含全部分裂短正合列 $A->A plus.o C->C$.
  + 容许单态射的复合仍容许; 容许满态射也一样.
  + 容许单态射沿任意态射的推出存在, 推出后仍是容许单态射.
  + 容许满态射沿任意态射的拉回存在, 拉回后仍是容许满态射.

  加性函子 $F:cal(E)->cal(F)$ 若保持容许短正合列, 就称为*正合函子*.
] <def-quillen-exact-category>

核与余核都在 $cal(E)$ 内理解. 公理只对指定的序列提出要求, 不要求每个态射都有核与余核. 容许短正合列是否分裂, 取决于所选的正合结构.

#example(title: [三类基本例子])[
  Abel 范畴配上全部短正合列就是正合范畴. 更一般地, Abel 范畴中对扩张封闭的全加性子范畴, 继承三项都在其中的短正合列, 也得到正合结构.

  对含幺环 $R$, $cat("Proj")(R)$ 仍表示有限生成投射右 $R$-模的范畴. 其中的短正合列全部分裂, 因为商模投射. 任意加性范畴也可以只指定分裂短正合列, 得到*分裂正合结构*.

  概形 $X$ 上的有限秩向量丛, 配上底层 $cal(O)_X$-模的短正合列, 形成正合范畴 $cat("Vect")(X)$. 这些序列局部分裂, 但不必整体分裂.
] <ex-quillen-exact-categories>

例如在 $cat("Proj")(ZZ)$ 中, $ZZ ->^2 ZZ$ 虽然是单态射, 却不是容许单态射: 它在 $Ab$ 中的余核 $ZZ slash 2$ 不是投射模. 这说明构造时必须保留“容许”的限制.

#lemma(title: [复合所需的拉回])[
  设 $i:M arrow.r.hook Y$ 为容许单态射, $q:N->>Y$ 为容许满态射. 则拉回 $P=M times_Y N$ 存在, 并有交换方块
  #align(center, {
    set text(fill: black)
    diagram(edge-stroke: .65pt + black, spacing: 2.5em, $
      P edge(b, "hook->") edge("d", a, ->>) & N edge("d", q, ->>, label-side: #left) \
      M edge(i, "hook->") & Y
    $)
  })
  其中 $a$ 是容许满态射, $b$ 是容许单态射, 且 $ker a tilde.eq ker q$. 正合函子保持这个拉回方块.
] <lem-q-pullback>

#proof[
  拉回的存在与 $a$ 的容许性来自公理. 核的泛性质给出 $ker a tilde.eq ker q$. 若 $c:Y->>C$ 是 $i$ 的余核, 则 $c q$ 是容许满态射. 而 $P->N$ 正是 $c q$ 的核, 所以 $b$ 也是容许的.

  为了验证最后一句, 将方块写成容许短正合列
  $ 0->P ->^((b,a)) N plus.o M ->^((q,-i)) Y->0 $
  右边的映射是容许满态射: 它分解成 $q plus.o id_M$ 与分裂满态射 $(id_Y,-i)$. 正合函子保持这条序列和有限直和, 所得核仍给出拉回.
]

对偶地, 容许满态射沿容许单态射推出时, 也得到同样类型的方块. 这些性质让子对象与商对象可以相容地交替使用.

=== 子商与 $Q$ 范畴 <sec-q-category>

把 $X$ 看成 $Y$ 的一个子商, 就是先选子对象 $M arrow.r.hook Y$, 再选商映射 $M->>X$. 这正是 $Q$ 中从 $X$ 到 $Y$ 的态射.

#definition(title: [Quillen 的 $Q$ 范畴])[
  $Q cal(E)$ 的对象与 $cal(E)$ 相同. 一个态射 $alpha:X->Y$ 是跨度
  $ X stretch(arrow.l.twohead)^p M stretch(arrow.r.hook)^i Y $
  的同构类, 其中 $p$ 与 $i$ 都是容许的. 两个跨度 $(M,p,i)$ 与 $(M',p',i')$ 表示同一个态射, 当且仅当存在同构 $h:M->^~M'$, 满足
  $ p' h=p, quad i' h=i $
  两端 $X,Y$ 固定. 恒等态射由 $X <-^id X ->^id X$ 表示.
] <def-quillen-q-category>

若 $U=ker p$, 这个跨度也可以写成容许滤过 $U arrow.r.hook M arrow.r.hook Y$, 连同同构 $M slash U tilde.eq X$. 这个同构属于数据的一部分. 仅仅知道 $X$ 与某个子商同构, 还没有确定一个 $Q$ 态射.

#definition(title: [$Q$ 中的复合])[
  给定 $alpha=(X arrow.l.twohead M arrow.r.hook Y)$ 与 $beta=(Y arrow.l.twohead N arrow.r.hook Z)$, 取 $P=M times_Y N$:
  #align(center, {
    set text(fill: black)
    diagram(edge-stroke: .65pt + black, spacing: (1.5em, 1.8em), $
      & & P edge("dl", a, ->>) edge("dr", b, "hook->") & & \
      & M edge("dl", p, ->>) edge("dr", i, "hook->") & & N edge("dl", q, ->>) edge("dr", j, "hook->") & \
      X & & Y & & Z
    $)
  })
  定义 $beta compose alpha$ 为外侧跨度
  $ X stretch(arrow.l.twohead)^(p a) P stretch(arrow.r.hook)^(j b) Z $
] <def-q-composition>

#proposition(title: [复合良定义])[
  上述公式不依赖代表元与拉回的选择, 满足结合律与单位律, 因而确实定义了一个范畴 $Q cal(E)$.
] <prop-q-composition>

#proof[
  由 @lem-q-pullback, $a$ 是容许满态射, $b$ 是容许单态射. 再用复合公理, 外侧跨度的两条腿仍然容许.

  替换同构的代表元, 会诱导拉回之间的同构; 改选拉回, 也有保持各投影的唯一同构. 因为 $Q$ 态射已经按中间对象的同构取商, 这些选择给出同一个态射.

  对第三个跨度 $Z arrow.l.twohead L arrow.r.hook W$, 两种括号分别使用
  $ (M times_Y N) times_Z L, quad M times_Y (N times_Z L) $
  它们都表示同一组相容的三重投影, 因而典范同构, 且到 $X,W$ 的映射相同. 所以结合律成立. 与恒等跨度复合时, 拉回典范同构于原来的中间对象, 单位律也成立.
]

#proposition(title: [两类基本态射])[
  容许单态射 $i:M arrow.r.hook Y$ 与容许满态射 $p:M->>X$ 分别给出
  $ i_(!):M->Y, quad p^(!):X->M $
  它们由跨度 $(M <-^id M ->^i Y)$ 与 $(X <-^p M ->^id M)$ 表示. 每个 $Q$ 态射都可分解为
  $ alpha=i_(!) compose p^(!) $
  单态射保持原来的方向, 满态射反转方向. 此外,
  $ (j i)_(!)=j_(!) compose i_(!), quad (p q)^(!)=q^(!) compose p^(!) $
] <prop-q-factorization>

#proof[
  将这些跨度代入复合公式, 相应的拉回分别就是中间对象本身. 因而公式直接成立. 给定跨度的分解只差一个中间对象的同构.
]

对 @lem-q-pullback 的方块, 复合公式还给出
$ q^(!) compose i_(!)=b_(!) compose a^(!) $
这条关系解释了为何复合必须用拉回: 它允许先取子对象再取商, 与先拉回再取子对象相互转换.

#proposition(title: [函子性与同构])[
  正合函子 $F:cal(E)->cal(F)$ 逐项作用于跨度, 给出函子 $Q F:Q cal(E)->Q cal(F)$. 自然同构给出自然同构, 正合等价给出范畴等价.

  $Q cal(E)$ 中的同构恰好来自 $cal(E)$ 中的同构. 特别地, 两个范畴的同构群胚等价.
] <prop-q-functoriality>

#proof[
  正合函子保持跨度两条腿的容许性, 并由 @lem-q-pullback 保持计算复合的拉回, 所以得到函子. 其余函子性由逐项作用得到.

  若一个跨度有逆跨度, 两次复合都是恒等. 恒等跨度的右腿是同构, 因而两次复合中的右腿迫使原来两个容许单态射都是同构. 将它们识别为恒等后, 剩下两个反向的容许满态射必须互逆, 所以也都是同构. 反方向显然成立.
]

#example(title: [向量空间中的子商])[
  设 $cal(E)=cat("Vect")^"fd" (k)$. 一个 $Q$ 态射 $V->W$ 就是一对线性子空间 $U subset.eq M subset.eq W$, 连同同构 $M slash U tilde.eq V$.

  因而 $0->W$ 的态射恰好对应 $W$ 的全部子空间. 当 $W=k$ 时, 正好有两个, 分别来自 $0 subset.eq k$ 与 $k subset.eq k$. 当 $k=bb(F)_q$ 且 $W=k^2$ 时, 有 $q+3$ 个: 零空间, $q+1$ 条直线, 以及整个平面.

  一个 $Q$ 态射只能从较小维数指向较大维数. 若两端维数相同, 则 $U=0$, $M=W$, 所以它必为同构. 例如 $Hom_(Q cal(E)) (k,k)=k^times$.
] <ex-q-vector-spaces>

=== 分类空间与 $K_0$ <sec-q-classifying-space>

回顾#chapter-ref(<chap-animae>)的神经与几何实现. 普通范畴 $cal(D)$ 的神经 $N cal(D)$ 在次数 $n$ 由可复合链 $D_0->dots->D_n$ 组成. 面映射删去端点或复合相邻箭头, 退化映射插入恒等. 其分类空间是
$ B cal(D):=lr(|N cal(D)|) $
对象给出顶点, 态射给出边, 一次复合给出填充三角形的二维单形. 三维单形记录结合律, 更高维继续记录相容的复合.

直接取 $B cal(E)$ 会得到可缩空间, 因为 $cal(E)$ 有零对象. 换成 $Q cal(E)$ 后, 零对象通常已经不是始对象: 刚才的例子中就有两条不同的 $0->k$.

对任意 $M$, 记下面两条 $Q$ 态射为
$ u_M=(0<-0 arrow.r.hook M), quad v_M=(0 arrow.l.twohead M ->^id M) $
它们都从 $0$ 指向 $M$. 因为每个顶点都由 $u_M$ 连到 $0$, $B Q cal(E)$ 是连通的. 选择顶点 $0$ 为基点, 定义闭路 $gamma_M$ 为先沿 $v_M$ 到 $M$, 再沿 $u_M$ 反向返回. 反向行走发生在分类空间中, 不要求 $u_M$ 在 $Q cal(E)$ 中可逆.

#definition(title: [Quillen 的 $K$ 理论空间])[
  对本质小正合范畴 $cal(E)$, 定义
  $ cal(K)_Q (cal(E)):=Omega B Q cal(E), quad
    K_n^Q (cal(E)):=pi_n cal(K)_Q (cal(E))=pi_(n+1) B Q cal(E) quad (n>=0) $
  基点是零对象处的常值闭路. 选取不同的小模型得到等价的空间.
] <def-quillen-k-space>

次数移了一位, 是因为对象的类在 $B Q cal(E)$ 中由闭路表示, 到环路空间后才变成连通分支. 下面证明这个定义的零次确实恢复 Grothendieck 群.

暂记 $K_0^"ex" (cal(E))$ 为由对象的同构类生成的 Abel 群, 对每条容许短正合列 $A arrow.r.hook B ->> C$ 加入关系 $[B]=[A]+[C]$. 这是#chapter-ref(<chap-k0>)中定义的同一类加法关系.

#theorem(title: [$Q$ 构造恢复 $K_0$])[
  存在自然同构
  $ K_0^"ex" (cal(E)) ->^~ pi_1 (B Q cal(E),0)=K_0^Q (cal(E)), quad [M] mapsto [gamma_M] $
] <thm-q-recovers-k0>

#proof[
  *先求基本群的生成元.* 由非退化边 $u_M$ 构成连接全部顶点的一棵树. 压缩这棵树后, 基本群由全部 $Q$ 态射生成, 关系来自二维单形:
  $ [beta compose alpha]=[beta][alpha], quad [u_M]=1 $
  这是神经的二维骨架给出的标准呈示. 这里暂用乘法记基本群.

  对容许单态射 $i:A arrow.r.hook B$, 有 $i_(!) u_A=u_B$, 所以 $[i_(!)]=1$. 结合 @prop-q-factorization, 只需保留 $p^(!)$ 型的生成元. 若 $p:B->>C$, 则
  $ p^(!) v_C=v_B, quad [p^(!)]=[v_B][v_C]^(-1) $
  因而全部基本群由 $[v_M]=[gamma_M]$ 生成.

  *短正合列给出加法关系.* 对 $A stretch(arrow.r.hook)^i B ->>^p C$, 将 $p$ 沿 $0->C$ 拉回, 得到其核 $A$. 复合公式给出
  $ p^(!) u_C=i_(!) v_A $
  压缩树并使用 $[i_(!)]=1$, 就有 $[p^(!)]=[v_A]$. 代回上一式:
  $ [v_B]=[v_A][v_C] $
  对分裂序列 $A->A plus.o C->C$ 以及交换两项后的序列, 得到
  $ [v_A][v_C]=[v_(A plus.o C)]=[v_(C plus.o A)]=[v_C][v_A] $
  中间使用同构对象给出相同的生成元, 这由同构在 $Q$ 中同时属于两类基本态射可知. 所以基本群是 Abel 群, 且有满射 $K_0^"ex" (cal(E))->pi_1 B Q cal(E)$.

  *再证明没有多余关系.* 对跨度 $alpha=(X arrow.l.twohead^p M arrow.r.hook Y)$, 赋予权重
  $ w(alpha):=[ker p] in K_0^"ex" (cal(E)) $
  对 @def-q-composition 的复合, 拉回给出 $ker a tilde.eq ker q$, 并有容许短正合列
  $ 0->ker q->ker(p a)->ker p->0 $
  确实, 将 $a:P->>M$ 沿 $ker p arrow.r.hook M$ 拉回, 所得对象就是 $ker(p a)$, 核仍是 $ker a$. 因而
  $ w(beta compose alpha)=w(alpha)+w(beta) $
  恒等与树中的边权重为零. 所以 $w$ 尊重基本群呈示的全部关系, 给出反向同态
  $ pi_1 B Q cal(E)->K_0^"ex" (cal(E)) $
  它将 $[gamma_M]$ 送回 $[M]$, 因为 $ker(M->0)=M$. 两个同态互逆, 自然性也由正合函子保持核--余核对得到.
]

这个证明还给出具体计算方法. 一条 $Q$ 态射 $X arrow.l.twohead M arrow.r.hook Y$, 用树中的路径接回基点后, 对应的 $K_0$ 类就是 $[ker(M->X)]$. 对向量空间, 这个整数是 $dim M-dim X$.

=== 与 $S_bullet$ 构造的比较 <sec-q-s-comparison>

前面已经验证了 $Q$ 构造的零次群. 要识别整个空间, 可以把一条子商跨度重新写成滤过. 对正合范畴 $cal(E)$, 定义 $S_n cal(E)$ 为容许滤过
$ 0=X_0 arrow.r.hook X_1 arrow.r.hook dots arrow.r.hook X_n $
及其相容商对象组成的范畴. 等价地, 沿用#link(<sec-waldhausen-s-construction>)[$S_bullet$ 构造]中的 $cat("Arr")([n])$, 要求 $F_(i i)=0$, 且
$ F_(i j) arrow.r.hook F_(i k) ->> F_(j k) $
是容许短正合列. 记 $S_n cal(E)^"iso"$ 为只保留图表同构的群胚, 并令 $W_n:=B(S_n cal(E)^"iso")$. 所有商对象都保留在数据中, 因而取子滤过与取商给出相容的单纯结构.

#theorem(title: [$Q$ 与 $S_bullet$ 的比较])[
  对本质小正合范畴 $cal(E)$, 有自然的空间等价
  $ B Q cal(E) tilde.eq lr(|W_bullet|), quad
    cal(K)_Q (cal(E)) tilde.eq Omega lr(|W_bullet|) $
] <thm-q-s-comparison>

#proof[
  *把一条跨度改写成滤过.* 对 $X arrow.l.twohead^p M arrow.r.hook Y$, 记 $U=ker p$. 它等价于三步滤过
  $ 0 arrow.r.hook U arrow.r.hook M arrow.r.hook Y $
  以及商 $M slash U=X$. 因而一个 $Q$ 态射正好由 $S_3 cal(E)$ 的数据表达. 在次数零, 一个对象则由 $S_1 cal(E)$ 表达. 这提示我们把第 $n$ 次数据放到 $S_(2n+1) cal(E)$ 中寻找.

  *同时读取一串跨度.* 对 $F in S_(2n+1) cal(E)$, 令
  $ A_i:=F_(n-i,n+1+i) quad (0<=i<=n) $
  相邻两项之间有跨度
  $ A_i arrow.l.twohead F_(n-i-1,n+1+i) arrow.r.hook A_(i+1) quad (0<=i<n) $
  左腿对滤过的下端取商, 右腿扩大上端. 于是得到 $Q cal(E)$ 中的链 $A_0->dots->A_n$. 例如五步滤过给出
  $ X_3 slash X_2 -> X_4 slash X_1 -> X_5 $
  其中箭头在 $Q cal(E)$ 中理解.

  反过来, 可以从末端向前取逆像, 恢复整条滤过. 对两条跨度
  $ A_0 arrow.l.twohead^p M arrow.r.hook^i A_1, quad
    A_1 arrow.l.twohead^q N arrow.r.hook A_2 $
  恢复的滤过是
  $ 0 arrow.r.hook ker q arrow.r.hook q^(-1)(i(ker p)) arrow.r.hook q^(-1)(i(M)) arrow.r.hook N arrow.r.hook A_2 $
  这里的逆像都是 @lem-q-pullback 中的拉回. 对更长的链重复这一步即可. 核, 拉回与商的唯一性说明, 恢复只差唯一的相容同构.

  *组织次数与面映射.* 定义边式细分
  $ (op("esd") W)_n:=W_(2n+1) $
  它由保序集合 $[n]^"op" star [n]$ 给出, 其中 $star$ 表示先排左边再排右边的有序拼接. 对 $alpha:[m]->[n]$, 使用 $alpha^"op" star alpha$ 诱导结构映射. 这样同时从两端读取滤过, 正好给出上述 $A_i$; 删去中间的 $A_i$ 对应跨度的拉回复合.

  令 $cal(G)_n$ 为 $Q cal(E)$ 中长度 $n$ 的链与这些链之间的自然同构组成的群胚. 上述对应给出与单纯结构相容的群胚等价
  $ S_(2n+1) cal(E)^"iso" tilde.eq cal(G)_n $
  保留链之间的同构很重要: 单个滤过可能有非平凡自同构, 所以这里先比较群胚.

  *最后做几何实现.* 边式细分只重新剖分单形, 不改变实现的同伦型, 因而 $lr(|op("esd") W|) tilde.eq lr(|W|)$. 另一方面, $lr(|B cal(G)_bullet|) tilde.eq B Q cal(E)$. 后一个事实可逐个神经方向验证: 固定同构方向后, 得到的是若干互相同构的图表组成的范畴, 在任一端取值都是范畴等价. 再实现另一个方向即可.

  将这些等价连起来,
  $ lr(|W_bullet|) tilde.eq lr(|op("esd") W_bullet|)
    tilde.eq lr(|B cal(G)_bullet|) tilde.eq B Q cal(E) $
  它们都保持零对象给出的基点, 取环路便得到第二个等价. 细分与实现的上述性质, 以及这种比较的高阶版本, 参见 @BRQ[§2, 命题 3.7 与定理 3.10].
]

这里比较的是整个空间, 所以它同时识别全部非负次 $K$ 群. 反复应用正合范畴版的 $S_bullet$, 就得到连通谱 $K^"cn" (cal(E))$, 满足
$ Omega^oo K^"cn" (cal(E)) tilde.eq cal(K)_Q (cal(E)), quad
  pi_n K^"cn" (cal(E)) tilde.eq K_n^Q (cal(E)) quad (n>=0) $
谱的各层与解环路映射按前面#link(<sec-connective-k-spectrum>)[连通 $K$ 谱]的方式构造. 这也解释了为何 $Q$ 空间能够反复解环路.

#theorem(title: [投射模与完美复形的比较])[
  对普通含幺环 $R$, 将投射模放在次数零, 给出自然等价
  $ K^"cn" (cat("Proj")(R)) tilde.eq K^"cn" (cat("Perf")(R)) $
  因而
  $ cal(K)_Q (cat("Proj")(R)) tilde.eq Omega^oo K^"cn" (R) $
] <thm-q-perfect-comparison>

这里引用 Gillet--Waldhausen 比较定理在投射模上的情形, 见 @Wei13[V, 定理 2.2 与 §2.7.2] 及 @BGT13[§7]. 比较先经过有界复形, 以拟同构为弱等价, 再到相应的稳定范畴. 在 $K_0$ 上, 按次数滤过将复形的类写成各项的交错和; 定理把这种比较提升到了整个 $K$ 理论空间.

同样的跨度方法也可用于小稳定 $oo$-范畴 $C$. 此时两条腿都允许是任意态射, 复合用同伦拉回, 并保留跨度之间的全部等价与高阶同伦. 得到的 $oo$-范畴记为 $Q_oo C$, 满足
$ Omega B Q_oo C tilde.eq Omega^oo K^"cn" (C) $
其中 $B Q_oo C$ 表示将这个 $oo$-范畴中的全部态射变成可逆后所得的生象. 这是 @BRQ[定理 3.10] 的稳定情形. 在普通正合范畴中取跨度的同构类是可行的, 因为固定两端后, 中间同构若存在就是唯一的; 在稳定情形则需要保留整个同伦空间.

本节的 $Q$ 构造直接给出连通理论. 若要得到负群, 继续使用前面的#link(<sec-nonconnective-k-spectrum>)[非连通延拓]. 因而 $K_n^Q (cat("Proj")(R))=K_n (R)$ 的比较在这里取 $n>=0$.

=== 环与 Abel 范畴 <sec-q-examples>

#theorem(title: [分裂正合范畴与群完备化])[
  设 $cal(E)$ 的每条容许短正合列都分裂. 令 $cal(E)^"iso"$ 为其同构群胚, 并用直和赋予 $B(cal(E)^"iso")$ 交换加法. 则有自然等价
  $ cal(K)_Q (cal(E)) tilde.eq (B(cal(E)^"iso"))^"gp" $
  右边是在交换幺半生象中取群完备化.
] <thm-q-split-group-completion>

这里引用 Quillen 的比较定理, 见 @Wei13[IV, 定理 7.1]. 每条滤过都可拆成各个商的直和, 所以滤过模型与直和模型相连; 同构与分裂选择之间的相容性由空间层面的群完备化处理. 仅在同构类的集合上取群完备化, 得到的是 $K_0$, 不会得到整个空间.

#corollary(title: [环的 $+=Q$ 定理])[
  对含幺环 $R$, 有空间等价
  $ Omega B Q cat("Proj")(R) tilde.eq K_0 (R) times B GL(R)^+ $
  其中 $K_0 (R)$ 看作离散空间, $B GL(R)^+$ 是相对于完美正规子群 $E(R)$ 的加号构造.
] <cor-quillen-plus-equals-q>

加号构造在分类空间上添入二维与三维胞腔, 杀掉基本群中的 $E(R)$, 同时保持相应局部系数同调. 这里使用它的存在与比较结果, 见 @Wei13[IV, §1 与推论 7.2]. 因为 $cat("Proj")(R)$ 分裂正合, 上一定理先给出直和的群完备化, 再用稳定一般线性群的加号模型描述其各个连通分支, 就得到这个公式.

在零分支取基本群, 恢复#chapter-ref(<chap-k1>)的
$ K_1^Q (cat("Proj")(R)) tilde.eq pi_1 B GL(R)^+ tilde.eq GL(R) slash E(R)=K_1 (R) $
二次同伦群也能接回前面的定义. 令 $Y=B GL(R)^+$, $tilde(Y)$ 为其万有覆盖. 加号构造的局部系数同调性质给出 $H_2 (tilde(Y);ZZ) tilde.eq H_2 (E(R);ZZ)$. 由 Hurewicz 定理,
$ K_2^Q (cat("Proj")(R)) tilde.eq pi_2 Y tilde.eq pi_2 tilde(Y)
  tilde.eq H_2 (E(R);ZZ) tilde.eq K_2 (R) $
最后一步使用#chapter-ref(<chap-k2>)中 Steinberg 群的泛中心扩张. 至此, 同一个 $K$ 理论空间的前三个同伦群, 已经分别接回对象的加法关系, 稳定自同构的 Abel 化与初等群的二次同调.

#example(title: [有限维向量空间])[
  对域 $k$, $cal(E)=cat("Vect")^"fd" (k)=cat("Proj")(k)$ 分裂正合, 而
  $ B(cal(E)^"iso") tilde.eq coprod_(d>=0) B GL_d (k) $
  直和对应块对角矩阵. 群完备化将维数 $NN$ 扩成 $ZZ$, 同时保留稳定自同构与高阶同伦:
  $ Omega B Q cal(E) tilde.eq ZZ times B GL(k)^+ $
  因而 $pi_1 B Q cal(E)=ZZ$, $pi_2 B Q cal(E)=k^times$. 当 $k$ 是有限域, 更高群由#link(<ex-k-spectrum-finite-fields>)[前面的有限域计算]给出.
] <ex-q-field-k-theory>

#example(title: [同一个加性范畴的两种正合结构])[
  固定素数 $p$, 令 $cal(A)$ 为有限 Abel $p$-群的范畴. 对通常的短正合列, 逐次取组成因子得到
  $ [M]=ell(M)[ZZ slash p], quad ell(M)=log_p |M| $
  长度对短正合列可加, 因而 $K_0^Q (cal(A)) tilde.eq ZZ$.

  若在同一个加性范畴上只保留分裂短正合列, 记为 $cal(A)_"split"$, 有限 Abel 群的分解定理却给出
  $ K_0^Q (cal(A)_"split") tilde.eq plus.o.big_(r>=1) ZZ[ZZ slash p^r] $
  恒等正合函子 $cal(A)_"split"->cal(A)$ 将第 $r$ 个生成元送到 $r$. 例如通常正合结构中的序列
  $ 0->ZZ slash p->ZZ slash p^2->ZZ slash p->0 $
  给出 $[ZZ slash p^2]=2[ZZ slash p]$, 但它不是分裂正合结构允许的序列. 因而 $Q$ 构造确实依赖所选的正合结构.
] <ex-q-exact-structure-matters>

#definition(title: [环的 $G$ 群])[
  设 $R$ 右 Noetherian, $cat("mod")(R)$ 为有限生成右 $R$-模的 Abel 范畴. 定义
  $ G_n (R):=K_n^Q (cat("mod")(R)) quad (n>=0) $
  正合包含 $cat("Proj")(R)->cat("mod")(R)$ 给出 Cartan 映射 $K_n (R)->G_n (R)$.
] <def-q-g-theory>

例如 $R=k[epsilon] slash (epsilon^2)$. 它是局部环, 所以 $K_0 (R)=ZZ[R]$. 每个有限生成 $R$-模都有以 $k$ 为因子的有限组成列, 故 $G_0 (R)=ZZ[k]$. 序列 $0->k->R->k->0$ 说明 Cartan 映射在这些基下是乘以 $2$. 这也将#chapter-ref(<chap-k0>)中投射模与全部有限生成模的两种 Grothendieck 群放进了同一个构造框架.

#proposition(title: [换环与有限投射转移])[
  设 $f:R->S$ 为含幺环同态. 扩张标量给出正合函子
  $ -times.o_R S:cat("Proj")(R)->cat("Proj")(S) $
  因而诱导全部 $n>=0$ 的映射 $f^*:K_n (R)->K_n (S)$. 若 $S$ 作为右 $R$-模有限生成投射, 限制标量还给出
  $ f_*:K_n (S)->K_n (R) $
] <prop-q-transfer>

#proof[
  投射模是有限自由模的直和项, 扩张标量仍保留这个性质. 投射模之间的容许短正合列分裂, 所以即使 $S$ 不平坦, 这个函子仍正合.

  若 $S_R$ 有限生成投射, 每个有限生成投射 $S$-模作为 $R$-模仍是有限个 $S_R$ 的直和项. 限制标量保持短正合列, 因而也得到正合函子. 两个映射都由 @prop-q-functoriality 后取分类空间, 环路与同伦群得到. 在次数 $0,1,2$, 它们恢复前面各章的构造.
]

这些映射都来自同一个原则: 正合函子作用于 $Q$ 构造, 再通过分类空间与环路空间, 同时诱导各个非负次数的映射. 下面研究这些映射何时为等价, 以及它们组成的正合列.

== 常用定理与计算 <sec-higher-k-basic-theorems>

常用的计算方法可以归为三类: 用加性拆开正合列, 用分解或滤过换成较小的范畴, 用局部化连接子范畴与商. 本节陈述所需定理并推导应用, 一般定理的证明见 @Wei13[V, §1 与 §3--§6]. 以下范畴都本质小, 简记 $K_n (cal(E))=K_n^Q (cal(E))$, 且 $n>=0$.

*可加性.*

#theorem(title: [可加性定理])[
  设 $F',F,F'':cal(E)->cal(F)$ 是正合函子, 配有自然变换, 使每个对象 $M$ 都给出容许短正合列
  $ F'(M) arrow.r.hook F(M) ->> F''(M) $
  则在 $K$ 理论空间上有同伦
  $ cal(K)_Q (F) tilde.eq cal(K)_Q (F')+cal(K)_Q (F'') $
  加法由直和诱导. 因而在全部非负次数上,
  $ K_n (F)=K_n (F')+K_n (F'') $
] <thm-higher-k-additivity>

这把 $K_0$ 中的短正合列关系提升到了整个空间, 不要求序列自然分裂. 定理见 @Wei13[V, 定理 1.2]. 对函子的有限容许滤过反复应用它, 就得到各个商函子所诱导映射的和; 这里要求滤过中的函子与商函子都正合.

例如 $F(M)=M^(plus.o r)$ 在每个 $K_n$ 上诱导乘以 $r$. 若有正合自函子 $T$ 和自然同构 $"id" plus.o T tilde.eq T$, 则
$ "id"+K_n (T)=K_n (T), quad K_n (cal(E))=0 $
这就是 Eilenberg 消去法在所有非负次数上的形式.

*有限分解与 Resolution.*

投射分解让一般模可以由投射模计算. Resolution 定理把这一原则推广到正合范畴.

#theorem(title: [Resolution 定理])[
  设 $cal(H)$ 是正合范畴, $cal(P) subset.eq cal(H)$ 是带诱导正合结构的满子范畴, 对扩张封闭, 并对 $cal(P)$ 中对象之间的容许满态射取核封闭. 假设每个 $M in cal(H)$ 都有有限分解
  $ 0->P_d->dots->P_0->M->0, quad P_i in cal(P) $
  分解的每一步都由 $cal(H)$ 中的容许短正合列组成. 则包含诱导等价
  $ cal(K)_Q (cal(P)) ->^~ cal(K)_Q (cal(H)) $
  特别地, $K_n (cal(P)) tilde.eq K_n (cal(H))$.
] <thm-higher-k-resolution>

分解长度可以随对象变化. 只要能用 $cal(P)$ 中的对象作有限分解, 就能用 $cal(P)$ 计算 $cal(H)$ 的全部高阶群, 见 @Wei13[V, 定理 3.1]. 在零次, 逆映射就是熟悉的 $[M] mapsto sum_(i=0)^d (-1)^i [P_i]$; 更高次的结论还需要处理分解选择之间的相容性.

#corollary(title: [正则环的 $K$ 理论与 $G$ 理论])[
  若 $R$ 右 Noetherian, 且每个有限生成右 $R$-模都有有限投射维数, 则 Cartan 映射给出
  $ K_n (R) ->^~ G_n (R) $
]

#proof[
  在 Resolution 定理中取 $cal(P)=cat("Proj")(R)$, $cal(H)=cat("mod")(R)$. 投射模的扩张与投射模之间满射的核都仍投射. Noetherian 性保证可以逐次选取有限生成自由模, 有限投射维数保证分解在有限步终止.
]

还有一个直接应用. 记 $cal(H)(R)$ 为具有有限生成投射模的有限分解的右 $R$-模范畴. 对任意环 $R$, Resolution 给出 $K_n (cal(H)(R)) tilde.eq K_n (R)$. 若环同态 $f:R->S$ 的 $S_R$ 属于 $cal(H)(R)$, 则限制标量落在
$ cat("Proj")(S)->cal(H)(R) $
因为有限生成投射 $S$-模是有限个 $S_R$ 的直和项. 所以仍可构造转移 $f_*:K_n (S)->K_n (R)$. 这把 @prop-q-transfer 中 $S_R$ 有限生成投射的假设, 放宽为存在有限生成投射模的有限分解, 见 @Wei13[V, §3.3.2].

*滤过与 Dévissage.*

另一种简化是给对象选有限滤过, 使各个商落在较小的 Abel 范畴中. 这正是组成列计算的推广.

#theorem(title: [Dévissage 定理])[
  设 $cal(A) subset.eq cal(B)$ 是满 Abel 子范畴, 包含函子正合, 且 $cal(A)$ 对在 $cal(B)$ 中取子对象与商对象封闭. 若每个 $M in cal(B)$ 都有有限滤过
  $ 0=M_0 subset.eq M_1 subset.eq dots subset.eq M_r=M, quad M_i slash M_(i-1) in cal(A) $
  则包含诱导等价
  $ cal(K)_Q (cal(A)) ->^~ cal(K)_Q (cal(B)) $
  特别地, $K_n (cal(A)) tilde.eq K_n (cal(B))$.
] <thm-higher-k-devissage>

这里不要求 $cal(A)$ 对扩张封闭. 各层在小范畴中, 整个对象可以只在大范畴中. 这是#chapter-ref(<chap-k0>)中 @thm-abelian-k0-devissage 的高阶版本, 见 @Wei13[V, 定理 4.1].

#example(title: [有限长度模与幂零理想])[
  设 $(R,frak(m))$ 是交换 Noetherian 局部环, 剩余域为 $k$. 记 $cal(L)(R)$ 为有限长度 $R$-模的范畴. 其每个对象都有因子为 $k$ 的组成列, 所以
  $ K_n (cal(L)(R)) tilde.eq K_n (k) $
  例如有限 Abel $p$-群范畴的高阶 $K$ 群就是 $K_n (bb(F)_p)$, 可直接使用#link(<ex-k-spectrum-finite-fields>)[有限域的计算].

  更一般地, 若 $R$ 右 Noetherian, $I$ 是幂零双边理想, 则限制标量诱导
  $ G_n (R slash I) ->^~ G_n (R) $
  因为有限滤过 $0 subset.eq dots subset.eq M I^2 subset.eq M I subset.eq M$ 的每个商都被 $I$ 消去. 这里不要求函子 $M mapsto M slash M I$ 正合.

  因而 $G_n (k[epsilon] slash (epsilon^2)) tilde.eq K_n (k)$. 但 $K$ 理论一般不满足幂零不变性: 对 $R=k[epsilon] slash (epsilon^2)$, 映射 $K_1 (R)=R^times->k^times$ 的核是非平凡的 $1+epsilon k$.
] <ex-higher-k-devissage>

*局部化与边界.*

当一类对象在取商后变成零, 局部化定理就将它们与商范畴的 $K$ 理论接成正合列.

#theorem(title: [Abel 范畴的局部化定理])[
  设 $cal(S)$ 是 Abel 范畴 $cal(A)$ 的 Serre 子范畴. 则有同伦纤维序列
  $ cal(K)_Q (cal(S))->cal(K)_Q (cal(A))->cal(K)_Q (cal(A) slash cal(S)) $
  从而得到长正合列
  $ dots->K_(n+1) (cal(A) slash cal(S)) ->^partial K_n (cal(S))
    ->K_n (cal(A))->K_n (cal(A) slash cal(S))->dots $
  末端为
  $ K_1 (cal(A) slash cal(S)) ->^partial K_0 (cal(S))
    ->K_0 (cal(A))->K_0 (cal(A) slash cal(S))->0 $
] <thm-higher-k-abelian-localization>

Serre 子范畴与商沿用#chapter-ref(<chap-k0>)的 @def-serre-subcategory-k0. 上式将那里的局部化正合列向左延长, 见 @Wei13[V, 定理 5.1]. 边界 $partial$ 描述商范畴中的类提升回原范畴时留下的障碍.

特别地, 若 $alpha:M->M$ 在商范畴中成为同构, 则
$ partial[alpha]=[coker alpha]-[ker alpha] in K_0 (cal(S)) $
右边两项都属于 $cal(S)$. 这与#chapter-ref(<chap-k1>)中两项复形给出的边界相容, 符号约定见 @Wei13[V, 习题 5.1].

#example(title: [离散赋值环的局部化列])[
  沿用#chapter-ref(<chap-k2>)的记号, 设 $cal(O)_v$ 是分式域为 $F$ 的离散赋值环, 剩余域为 $k_v=cal(O)_v slash frak(m)_v$. 有限长度模构成 $cat("mod")(cal(O)_v)$ 的 Serre 子范畴, 商等价于 $cat("Vect")^"fd" (F)$.

  对子范畴使用 Dévissage, 对赋值环使用 Resolution, 局部化便给出
  $ dots->K_n (k_v)->K_n (cal(O)_v)->K_n (F)
    ->^partial_v K_(n-1) (k_v)->dots quad (n>=1) $
  在次数 $1$, 边界正是赋值
  $ partial_v:F^times->ZZ, quad a mapsto v(a) $
  确实, 对一致化参数 $pi$, 乘以 $pi$ 的核为零, 余核为 $k_v$, 所以 $partial_v[pi]=1$. 单位的边界为零, 再写 $a=pi^m u$ 即可.

  在次数 $2$, 边界是 @prop-tame-symbol 中的 tame symbol, 满足
  $ partial_v {pi,u}=overline(u) in k_v^times quad (u in cal(O)_v^times) $
  因而前面的赋值与留数都来自同一条高阶长正合列. 边界的这一识别见 @Wei13[V, §6.6].
] <ex-higher-k-dvr-localization>

*多项式环与 Laurent 多项式环.*

#theorem(title: [同伦不变性与基本定理])[
  设 $R$ 是交换正则 Noetherian 环. 则扩张标量诱导
  $ K_n (R) ->^~ K_n (R[t]) quad (n>=0) $
  此外, 对 $n>=1$ 有自然分解
  $ K_n (R[t,t^(-1)]) tilde.eq K_n (R) plus.o K_(n-1) (R) $
  而 $K_0 (R[t,t^(-1)]) tilde.eq K_0 (R)$.
] <thm-higher-k-regular-fundamental>

这将#chapter-ref(<chap-k1>)中次数 $0,1$ 的基本定理推广到所有非负次数, 见 @Wei13[V, 定理 6.2--6.3]. 同伦不变性先在 Noetherian 环的 $G$ 理论中成立, 再通过正则情形的 $K_n tilde.eq G_n$ 得到上述结论. Laurent 分解来自对 $t=0$ 的局部化; 第二项的分裂由与 $[t] in K_1 (R[t,t^(-1)])$ 的乘积给出.

例如对域 $k$,
$ K_1 (k[t,t^(-1)]) tilde.eq k^times plus.o ZZ, quad
  K_2 (k[t,t^(-1)]) tilde.eq K_2 (k) plus.o k^times $
第一个分解把单位 $a t^m$ 记成 $(a,m)$. 第二个分解中的 $k^times$ 可由 $u mapsto {t,u}$ 给出, 在 $t=0$ 的留数又将它送回 $u$. 若 $k$ 有限, $K_2 (k)=0$, 因而 $K_2 (k[t,t^(-1)]) tilde.eq k^times$.
