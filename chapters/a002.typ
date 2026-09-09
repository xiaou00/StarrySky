#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= 纤维序列 / Fiber Sequence <chap-fiber-sequence>

纤维序列是同伦论中的基本工具, 它是短正合列的类比.

#table(
  columns: (1fr, 1fr),
  table.header([同伦代数], [同调代数]),
  [
    纤维序列
    $ F stretch(->)^i E stretch(->)^p B $
  ], [
    短正合列
    $ 0->A stretch(->)^j M stretch(->)^q N->0 $
  ],
  [零对象 $0$; 在带基点生象中是 $*$], [零模 $0$],
  [指定零同伦 $p compose i tilde.eq 0$], [等式 $q compose j=0$],
  [同伦拉回 $F tilde.eq E times_B 0$], [经 $j$ 识别 $A tilde.eq ker(q)$, 且 $q$ 满射],
)

这里先作结构上的类比: 将普通模放入导出范畴后, 短正合列就给出纤维序列.

== 从定义开始

本节的拉回、推出和交换图都在无穷范畴中理解: 它们保留同伦及其相容性. 所以这里的 pullback 就是通常所说的*同伦拉回*, 无须再额外作一次同伦修正.

=== 零对象与零态射

#definition(title: "带基点无穷范畴")[
  若无穷范畴 $cal(C)$ 中有一个对象 $0$, 对任意 $X in cal(C)$ 都满足
  $ Map_(cal(C)) (0,X) tilde.eq *, quad Map_(cal(C)) (X,0) tilde.eq * $
  就称 $0$ 为*零对象*. 换句话说, 它同时是始对象和终对象. 存在零对象的无穷范畴称为*带基点无穷范畴* (pointed $oo$-category).

  选定零对象后, 复合
  $ X->0->Y $
  给出*零态射* $0_(X,Y):X->Y$, 通常简记为 $0$. 它的选择空间可缩, 因而为映射生象 $Map_(cal(C)) (X,Y)$ 指定了基点.
] <def-fiber-pointed-category>

例如, 带基点生象的无穷范畴 $Ani_*$ 以单点生象 $*$ 为零对象. 这里"范畴带基点"指的是*有零对象*; 在这个例子中, 对象本身也恰好是带基点的生象.

以下固定带基点无穷范畴 $cal(C)$, 并假设所用的拉回与推出存在. 若 $cal(C)$ 有有限极限与有限余极限, 这些存在性就自动满足.

=== 纤维与余纤维

#definition(title: "纤维与余纤维")[
  给定态射 $f:E->B$, 沿零态射 $0->B$ 拉回 $f$, 所得对象称为 $f$ 的*纤维* (fiber), 记为
  $ fib(f):=E times_B 0 $
  对偶地, 将 $f$ 沿零态射 $E->0$ 推出, 所得对象称为 $f$ 的*余纤维* (cofiber), 记为
  $ cofib(f):=B coprod_E 0 $
  即下面左边是拉回方块, 右边是推出方块:

  #align(center)[
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 24pt,
      align: center + bottom,
      [
        #book-diagram(
          spacing: 26pt, cell-size: 0pt, node-inset: 5pt,
          {
            fletcher.edge((0, 0), (1, 0), marks: "->")
            fletcher.edge((0, 0), (0, 1), marks: "->")
            fletcher.edge((1, 0), (1, 1), $f$, label-side: left, marks: "->")
            fletcher.edge((0, 1), (1, 1), marks: "->")
            fletcher.node((0, 0), $fib(f)$)
            fletcher.node((1, 0), $E$)
            fletcher.node((0, 1), $0$)
            fletcher.node((1, 1), $B$)
          },
        )
        \ 拉回
      ],
      [
        #book-diagram(
          spacing: 26pt, cell-size: 0pt, node-inset: 5pt,
          {
            fletcher.edge((0, 0), (1, 0), $f$, marks: "->")
            fletcher.edge((0, 0), (0, 1), marks: "->")
            fletcher.edge((1, 0), (1, 1), marks: "->")
            fletcher.edge((0, 1), (1, 1), marks: "->")
            fletcher.node((0, 0), $E$)
            fletcher.node((1, 0), $B$)
            fletcher.node((0, 1), $0$)
            fletcher.node((1, 1), $cofib(f)$)
          },
        )
        \ 推出
      ],
    )
  ]

  严格地说, 纤维与余纤维还带着图中的结构态射和交换同伦. 单写 $fib(f)$ 或 $cofib(f)$ 时, 这些数据通常省略. 参见 @Lur17[定义 1.1.1.6].
] <def-fiber-and-cofiber>

纤维的泛性质可以直接用映射生象表达. 对任意测试对象 $T$, 自然映射给出等价
$ Map_(cal(C)) (T,fib(f)) tilde.eq Map_(cal(C)) (T,E) times_(Map_(cal(C)) (T,B)) * $
其中 $*->Map_(cal(C)) (T,B)$ 选取零态射. 右边记录一个态射 $u:T->E$, 连同一个*指定的零同伦* $f compose u tilde.eq 0$, 以及这些数据之间的全部高阶同伦. 因而, 向纤维作映射, 就是在给出"被 $f$ 送到零的态射, 以及它怎样变成零".

例如在 $Ani_*$ 中, $fib(f)$ 的底层生象可用二元组 $(e,gamma)$ 来描述: $e$ 是 $E$ 中的点, $gamma$ 是从 $f(e)$ 到 $B$ 的基点的路径. 路径本身也是纤维记录的信息.

对偶地, 余纤维满足
$ Map_(cal(C)) (cofib(f),T) tilde.eq Map_(cal(C)) (B,T) times_(Map_(cal(C)) (E,T)) * $
所以从 $cofib(f)$ 作映射, 就是给出 $v:B->T$, 连同零同伦 $v compose f tilde.eq 0$. 直观上, 余纤维是让 $f$ 变成零的通用构造, 并保留零化过程的同伦信息.

这些泛性质也说明了唯一性: 对固定的 $f$, 纤维或余纤维连同结构数据的选择空间, 只要非空就是可缩的. 若每个态射都有纤维与余纤维, 便得到函子
$ fib,cofib:Fun([1],cal(C))->cal(C) $
其中 $[1]$ 是只有一条非恒等箭头 $0->1$ 的范畴, 所以 $Fun([1],cal(C))$ 就是 $cal(C)$ 的态射无穷范畴. 参见 @Lur17[注 1.1.1.7].

=== 纤维序列本质上是拉回方块

#definition(title: "纤维序列")[
  给定两条可复合态射, 并指定一个零同伦
  $ F stretch(->)^i E stretch(->)^p B, quad alpha:p compose i tilde.eq 0 $
  这里 $alpha$ 是映射生象 $Map_(cal(C)) (F,B)$ 中从 $p compose i$ 到零态射的一条路径. 若由 $alpha$ 指定交换同伦的下列方块是*拉回方块*, 就称 $(i,p,alpha)$ 为一个*纤维序列* (fiber sequence), 通常简写为 $F->E->B$:

  #align(center)[
    #book-diagram(
      spacing: 30pt, cell-size: 0pt, node-inset: 5pt,
      {
        fletcher.edge((0, 0), (1, 0), $i$, marks: "->")
        fletcher.edge((0, 0), (0, 1), marks: "->")
        fletcher.edge((1, 0), (1, 1), $p$, label-side: left, marks: "->")
        fletcher.edge((0, 1), (1, 1), marks: "->")
        fletcher.node((0, 0), $F$)
        fletcher.node((1, 0), $E$)
        fletcher.node((0, 1), $0$)
        fletcher.node((1, 1), $B$)
      },
    )
  ]

  等价地, 由 $i$ 和 $alpha$ 诱导的比较态射
  $ c_alpha:F->E times_B 0=fib(p) $
  必须是等价. 参见 @Lur17[定义 1.1.1.4].
] <def-pointed-fiber-sequence>

因此, *纤维序列本质上就是左下角为零对象的拉回方块*. 写成三项序列时, 只是把零对象和交换同伦省略了.

这里必须检查的是*由这份数据诱导的* $c_alpha$. 仅有抽象对象之间的等价 $F tilde.eq fib(p)$ 并不够; 它还要与 $i$ 及零同伦相容. 同样, 只说"$p compose i$ 同伦于零"只是一个存在性断言, 定义中还需要选定这个同伦. 不同选择可能给出不同的比较态射.

用泛性质检验, 这就是说: 对每个 $T in cal(C)$, 由 $(i,alpha)$ 给出的自然映射
$ Map_(cal(C)) (T,F)->Map_(cal(C)) (T,E) times_(Map_(cal(C)) (T,B)) * $
都是等价. 于是任何 $u:T->E$ 连同零同伦 $p compose u tilde.eq 0$, 都能经 $F$ 分解, 且与所给数据相容的分解空间可缩. 这就是无穷范畴中"唯一分解"的含义.

#definition(title: "余纤维序列")[
  对同一份数据 $(i,p,alpha)$, 若上面的方块是*推出方块*, 就称 $F->E->B$ 为*余纤维序列* (cofiber sequence). 等价地, 由 $(p,alpha)$ 诱导的态射
  $ cofib(i)=E coprod_F 0->B $
  是等价.
] <def-pointed-cofiber-sequence>

特别地, 每个态射 $f:E->B$ 自带两条序列及其零同伦:
$ fib(f)->E stretch(->)^f B, quad E stretch(->)^f B->cofib(f) $
前一条是纤维序列, 后一条是余纤维序列. 一般的带基点无穷范畴中, 这两个条件不同; 在稳定无穷范畴中, 拉回方块与推出方块一致, 因而两种序列才是同一个概念.

=== 例: 点到圆周

这里把拓扑空间 $X$ 通过*奇异单纯集* $"Sing"(X)$ 视作生象: 其 $n$-单形是连续映射 $|Delta^n| ->X$. 它是 Kan 复形, 表示 $X$ 的弱同伦型; 选定基点后便得到 $Ani_*$ 中的对象, 下文仍简记为 $X$. 参见 @Ker26[Tag 002K].

在 $Ani_*$ 中, 给 $S^1 subset CC$ 取基点 $1$, 考虑包含 $p:*->S^1$. 普通纤维只有一个点; 同伦纤维还记录从 $1$ 回到自身的路径, 即环路. 因而
$ fib(p)=* times_(S^1) * tilde.eq Omega S^1 tilde.eq ZZ_"disc" $
其中 $ZZ_"disc"$ 是以 $0$ 为基点的离散整数生象.

最后一个等价由绕数给出. 沿覆盖 $RR->S^1$, $u |-> exp(2 pi i u)$, 环路唯一提升为从 $0$ 到某个整数 $n$ 的路径, 这个 $n$ 就是绕数. 固定 $n$ 后, 所有这样的路径都能线性收缩到 $t |-> n t$, 所以*每个环路分支都可缩*, 得到上述等价. 参见 @Hat02[第 1.1 节, 定理 1.7].

于是有纤维序列
$ ZZ_"disc"->* stretch(->)^p S^1 $
它配备的零同伦是
$ alpha(n,t)=exp(2 pi i n t), quad t in [0,1] $
它把整数 $n$ 对应到绕 $n$ 圈的环路, 因而诱导等价 $ZZ_"disc"->Omega S^1$. 若换成常值同伦, 所有整数都会落到常值环路, 就不再是纤维序列. *这个例子的绕数信息, 正是由零同伦保存的*.

最后, 基本群由基点环路的同伦类组成, 也就是环路生象的连通分支. 因而这个纤维计算给出
$ pi_1 (S^1,1)=pi_0 (Omega S^1) tilde.eq pi_0 (fib(p)) tilde.eq ZZ $
这个对应还保留群运算: 若两条环路的提升终点分别为 $m,n$, 拼接时把第二条提升平移 $m$, 所得路径的终点就是 $m+n$. 所以*环路拼接对应绕数相加*, 反向环路对应取负, 得到群同构 $pi_1 (S^1,1) tilde.eq (ZZ,+)$, 其中逆时针绕一圈的环路对应生成元 $1$.

== 纤维的基本性质

以下设 $cal(C)$ 带基点且具有有限极限. 对任意 $X in cal(C)$, 记其*环路对象*为
$ Omega X:=0 times_X 0 $
在 $Ani_*$ 中, 这就是前面用过的基点环路生象.

#proposition(title: "三个基本计算")[
  对任意对象 $X$, 有自然等价
  $ fib(id_X) tilde.eq 0, quad fib(X->0) tilde.eq X, quad fib(0->X) tilde.eq Omega X $
] <prop-fiber-basic-computations>

#proof[
  前两式分别来自 $X times_X 0 tilde.eq 0$ 和 $X times_0 0 tilde.eq X$; 第三式就是 $Omega X$ 的定义.
]

#proposition(title: "零态射的纤维")[
  对零态射 $0_(X,Y):X->Y$, 有自然等价
  $ fib(0_(X,Y)) tilde.eq X times Omega Y $
] <prop-fiber-zero-morphism>

#proof[
  零态射由 $X->0->Y$ 给出. 利用拉回的复合性质,
  $ fib(0_(X,Y))=X times_Y 0 tilde.eq X times_0 (0 times_Y 0) tilde.eq X times Omega Y $
  最后一步用了 $0$ 是终对象, 因而在 $0$ 上的拉回就是积. 拉回的复合性质见 @Ker26[Tag 03FZ].
]

零态射的纤维因此同时记录源对象 $X$ 和目标的环路 $Omega Y$.

#proposition(title: "基变换保持对应基点上的纤维")[
  若 $cal(C)$ 中有拉回方块

  #align(center)[
    #book-diagram(
      spacing: 30pt, cell-size: 0pt, node-inset: 5pt,
      {
        fletcher.edge((0, 0), (1, 0), marks: "->")
        fletcher.edge((0, 0), (0, 1), $p'$, label-side: right, marks: "->")
        fletcher.edge((1, 0), (1, 1), $p$, label-side: left, marks: "->")
        fletcher.edge((0, 1), (1, 1), $g$, marks: "->")
        fletcher.node((0, 0), $E'$)
        fletcher.node((1, 0), $E$)
        fletcher.node((0, 1), $B'$)
        fletcher.node((1, 1), $B$)
      },
    )
  ]

  则方块诱导的态射是等价:
  $ fib(p')->^~ fib(p) $
  在 $Ani_*$ 中, 这里取的是 $B'$ 的基点以及它在 $B$ 中对应基点上的纤维.
] <prop-fiber-base-change>

#proof[
  由拉回条件, $E' tilde.eq E times_B B'$. 再沿 $0->B'$ 拉回, 得到
  $ fib(p')=E' times_(B') 0 tilde.eq (E times_B B') times_(B') 0 tilde.eq E times_B 0=fib(p) $
  其中复合 $0->B' stretch(->)^g B$ 与零态射 $0->B$ 典范相容, 所以最后一项确实是所需纤维.
]

#proposition(title: "保持有限极限的函子保持纤维序列")[
  设 $cal(D)$ 也带基点且具有有限极限. 若 $U:cal(C)->cal(D)$ 保持有限极限, 则对任意态射 $f:X->Y$, 有自然等价
  $ U(fib(f)) tilde.eq fib(U(f)) $
  因而纤维序列 $F->E->B$ 被送到纤维序列 $U(F)->U(E)->U(B)$, 零同伦也随 $U$ 一起传递.

  特别地, 下列两条仍是纤维序列:
  $ Omega F->Omega E->Omega B $
  $ Map_(cal(C)) (T,F)->Map_(cal(C)) (T,E)->Map_(cal(C)) (T,B) $
  第二条在 $Ani_*$ 中理解: 各映射生象以零态射为基点.
] <prop-functor-preserves-fiber-sequences>

#proof[
  $U$ 保持终对象, 所以 $U(0) tilde.eq 0$. 再用它保持拉回,
  $ U(X times_Y 0) tilde.eq U(X) times_(U(Y)) U(0) tilde.eq U(X) times_(U(Y)) 0 $
  这也说明定义纤维序列的方块仍被送到拉回方块.

  对两个特例, $Omega$ 保持有限极限, 因为它由拉回定义, 而极限之间可以交换; 表示函子 $Map_(cal(C)) (T,-)$ 也保持极限, 且 $Map_(cal(C)) (T,0) tilde.eq *$. 因此都可应用上述结论.
]

#proposition(title: "向左延长: 环路序列")[
  给定纤维序列 $F stretch(->)^i E stretch(->)^p B$, 有自然的*连接态射* $delta:Omega B->F$, 并可继续向左延长为
  $ dots->Omega F->Omega E->Omega B stretch(->)^delta F stretch(->)^i E stretch(->)^p B $
  其中任意相邻三项都构成纤维序列. 箭头及其零同伦由逐次取纤维给出.
] <prop-fiber-loop-sequence>

#proof[
  由 $F tilde.eq E times_B 0$,
  $ fib(i)=F times_E 0 tilde.eq (E times_B 0) times_E 0 tilde.eq 0 times_B 0=Omega B $
  取这个纤维的结构态射作为 $delta$, 就得到纤维序列 $Omega B->F->E$. 对它重复同一计算, 左边接上 $Omega E$, 再接上 $Omega F$, 如此继续即可.
]

这是同伦群长正合序列背后的对象层面的构造. 上述延长只用有限极限; 在稳定情形, 还能利用余纤维向右延长.

#proposition(title: "复合态射的纤维序列")[
  给定可复合态射 $X stretch(->)^f Y stretch(->)^g Z$, 存在自然纤维序列
  $ fib(f)->fib(g compose f)->fib(g) $
] <prop-fiber-composition-sequence>

#proof[
  拉回的复合性质给出
  $ fib(g compose f)=X times_Z 0 tilde.eq X times_Y (Y times_Z 0)=X times_Y fib(g) $
  因而 $f$ 诱导投影 $fib(g compose f)->fib(g)$. 沿 $0->fib(g)$ 取它的纤维, 得到
  $ (X times_Y fib(g)) times_(fib(g)) 0 tilde.eq X times_Y 0=fib(f) $
  这些拉回同时给出序列中的态射及指定零同伦, 所以确实得到所述纤维序列.
]

== 稳定情形下的纤维序列

前面只用到了零对象和有限极限. 现在固定一个*稳定无穷范畴* $cal(C)$: 它有零对象、有限极限与有限余极限, 并且一个方块是拉回, 当且仅当它是推出. 回顾 @def-stable-infty-category. 这一条件把纤维与余纤维联系起来, 也让纤维序列具有同调代数中熟悉的移位、旋转和分裂性质.

以下所有序列都保留指定的零同伦. 写 $"h"cal(C)$ 时才转到同伦范畴, 其中态射是映射生象的连通分支.

=== 稳定性带来的移位与加法

沿用记号
$ Sigma X:=0 coprod_X 0, quad Omega X:=0 times_X 0 $
稳定性使定义 $Sigma X$ 的推出方块同时成为拉回, 因而 $X tilde.eq Omega Sigma X$. 对偶地, 定义 $Omega X$ 的拉回方块也成为推出, 因而 $Sigma Omega X tilde.eq X$. 这些等价对 $X$ 自然, 所以
$ Sigma Omega tilde.eq id_(cal(C)), quad Omega Sigma tilde.eq id_(cal(C)) $
这就是说, *悬挂与环路可以互相撤销*. 写 $X[1]=Sigma X$, $X[-1]=Omega X$, 反复作用就得到所有整数次移位 $X[n]$.

还需要一个稳定范畴中的基本事实: 有限积与有限余积典范等价, 共同记为*直和*
$ X ⊕ Y tilde.eq X times Y tilde.eq X coprod Y $
它同时有嵌入和投影, 满足熟悉的矩阵关系. 映射生象也有与高阶同伦相容的加法和取负; 取 $pi_0$ 后,
$ Hom_("h"cal(C)) (X,Y)=pi_0 Map_(cal(C)) (X,Y) $
成为 Abel 群, 态射复合是双线性的. 因此后面可以写 $f-g$ 和矩阵形式的态射. 这些加法结构的一个来源是
$ Map_(cal(C)) (X,Y) tilde.eq Omega^n Map_(cal(C)) (X,Y[n]) quad (n>=0) $
即映射生象可以反复解环路. 参见 @Lur17[第 1.1.2 节, 注 1.1.3.5].

=== 纤维与余纤维相差一次移位

#proposition(title: "稳定时的纤维与余纤维")[
  对同一份带零同伦的数据 $A->B->C$, 下列条件等价:
  + 它是纤维序列.
  + 它是余纤维序列.

  此时统一称为*正合序列*, 并有与结构态射相容的等价
  $ A tilde.eq fib(B->C), quad C tilde.eq cofib(A->B) $

  另一方面, 对同一个态射 $f:X->Y$, 有自然等价
  $ cofib(f) tilde.eq Sigma fib(f), quad fib(f) tilde.eq Omega cofib(f) $
] <prop-stable-fiber-cofiber-shift>

#proof[
  前半部分直接来自稳定性: 定义纤维序列的方块也是推出方块, 反之亦然.

  对后半部分, 令 $F=fib(f)$. 因为 $F->X->Y$ 也是余纤维序列, 有 $Y tilde.eq X coprod_F 0$. 再取 $f$ 的余纤维, 利用推出的复合性质,
  $ cofib(f)=Y coprod_X 0 tilde.eq (X coprod_F 0) coprod_X 0 tilde.eq 0 coprod_F 0=Sigma F $
  对这个等价作用 $Omega$, 就得到第二式.
]

这里要分清两句话: *同一条三项序列*可以同时是纤维序列与余纤维序列; 但*同一个态射*的纤维与余纤维一般相差一次移位. 例如对 $X->0$,
$ fib(X->0) tilde.eq X, quad cofib(X->0) tilde.eq Sigma X $
所以稳定性并不把 $X$ 与 $Sigma X$ 识别成同一个对象.

#example(title: "复形中的映射锥")[
  在普通环 $R$ 的导出无穷范畴 $Dcat(R)$ 中, 采用上链复形约定, 对复形态射 $f:M->N$,
  $ cofib(f) tilde.eq op("Cone")(f), quad fib(f) tilde.eq op("Cone")(f)[-1] $
  例如把整数看成集中在零次的复形, 对乘 $n$ 的态射 $n:ZZ->ZZ$, $n>=2$, 有
  $ cofib(n) tilde.eq ZZ slash n ZZ, quad fib(n) tilde.eq (ZZ slash n ZZ)[-1] $
  普通核虽然为零, 纤维仍保留了余核移位后的信息.
]

=== 连接态射与旋转

#proposition(title: "连接态射与双向延长")[
  每条正合序列 $A stretch(->)^f B stretch(->)^g C$ 都自然给出连接态射 $delta:C->Sigma A$, 得到
  $ A stretch(->)^f B stretch(->)^g C stretch(->)^delta A[1] $
  其中 $B->C->A[1]$ 仍是正合序列, 特别地
  $ B tilde.eq fib(delta) $
  继续取纤维与余纤维, 可得到双向延长的序列
  $ dots->C[-1]->A->B->C->A[1]->B[1]->C[1]->dots $
  各相邻三项都带有相应的正合序列结构.
] <prop-stable-connecting-morphism>

#proof[
  对 $g:B->C$ 取余纤维. 下图的两个小方块都是推出, 因而外框也是推出:

  #align(center)[
    #book-diagram(
      spacing: 29pt, cell-size: 0pt, node-inset: 5pt,
      {
        fletcher.edge((0, 0), (1, 0), $f$, marks: "->")
        fletcher.edge((1, 0), (2, 0), marks: "->")
        fletcher.edge((0, 0), (0, 1), marks: "->")
        fletcher.edge((1, 0), (1, 1), $g$, label-side: left, marks: "->")
        fletcher.edge((2, 0), (2, 1), marks: "->")
        fletcher.edge((0, 1), (1, 1), marks: "->")
        fletcher.edge((1, 1), (2, 1), $delta$, marks: "->")
        fletcher.node((0, 0), $A$)
        fletcher.node((1, 0), $B$)
        fletcher.node((2, 0), $0$)
        fletcher.node((0, 1), $0$)
        fletcher.node((1, 1), $C$)
        fletcher.node((2, 1), $Sigma A$)
      },
    )
  ]

  外框把右下角识别为 $Sigma A$, 于是右边方块给出 $delta$. 它也为拉回, 所以 $B tilde.eq fib(delta)$. 向右重复取余纤维, 向左使用 @prop-fiber-loop-sequence, 就得到双向延长.
]

连接态射记录了正合序列中的粘合信息. 它由整份正合序列数据产生, 因而也随序列之间的态射自然变化. 后面会看到, 它是否零同伦恰好决定序列能否分裂.

#proposition(title: "同伦范畴中的旋转")[
  稳定无穷范畴 $cal(C)$ 的同伦范畴 $"h"cal(C)$ 自然是三角范畴. 由上述构造得到的图表
  $ A stretch(->)^f B stretch(->)^g C stretch(->)^delta A[1] $
  称为*区分三角* (distinguished triangle). 按通常的符号约定, 它的旋转是
  $ B stretch(->)^g C stretch(->)^delta A[1] stretch(->)^(-f[1]) B[1] $
] <prop-stable-triangle-rotation>

#proofsketch[
  上面的推出构造给出三角及其旋转. 旋转时, 悬挂方块中两份零对象的角色发生交换; 在映射生象中, 这对应把一条环路反向, 因而在同伦类上出现负号. 这解释了最后一箭头是 $-f[1]$.

  任意态射都能取余纤维, 图表间的相容态射也能延拓到余纤维. 余纤维的复合性质进一步给出八面体公理. 这些构造验证三角范畴公理; 完整表述与证明见 @Lur17[定义 1.1.2.11, 定理 1.1.2.14].
]

双向长序列没有标出的箭头, 应按逐次取纤维、余纤维的结构理解. 若把它们逐个写成原态射的移位, 就要遵守旋转的符号约定. 三角范畴保留了这些构造在同伦类上的结果; 无穷范畴还保留了构造本身及其相容同伦.

=== 纤维序列的长正合列

先给出适用于任意稳定无穷范畴的形式: 固定测试对象, 用映射的同伦类得到 Abel 群, 再把对象层面的正合序列变成长正合列.

#proposition(title: "纤维序列诱导长正合列")[
  设 $cal(C)$ 为稳定无穷范畴, 给定纤维序列及其连接态射
  $ A stretch(->)^f B stretch(->)^g C stretch(->)^delta A[1] $
  对任意 $T in cal(C)$ 和 $n in ZZ$, 记
  $ H_T^n (X):=Hom_("h"cal(C)) (T,X[n])=pi_0 Map_(cal(C)) (T,X[n]) $
  则有对纤维序列自然的 Abel 群长正合列
  $ dots->H_T^n (A) stretch(->)^(f_*) H_T^n (B) stretch(->)^(g_*) H_T^n (C) stretch(->)^(partial^n) H_T^(n+1) (A)->dots $
  这里 $f_*,g_*$ 分别由后复合 $f[n],g[n]$ 给出, *连接同态*为
  $ partial^n:H_T^n (C)->H_T^(n+1) (A), quad [u] |-> [delta[n] compose u] $
  "正合"指每一项上, 前一同态的像等于后一同态的核.
] <prop-stable-long-exact-sequence>

#proof[
  先说明一个直接来自纤维定义的事实. 对任意纤维序列 $U stretch(->)^i V stretch(->)^p W$, 序列
  $ Hom_("h"cal(C)) (T,U) stretch(->)^(i_*) Hom_("h"cal(C)) (T,V) stretch(->)^(p_*) Hom_("h"cal(C)) (T,W) $
  在中间一项正合. 因为 $p compose i tilde.eq 0$, 显然 $op("im")(i_*) subset.eq ker(p_*)$. 反过来, 若 $[v] in ker(p_*)$, 就是说 $p compose v:T->W$ 的同伦类为零. 选择一个零同伦 $p compose v tilde.eq 0$, 拉回泛性质便给出
  $ u:T->V times_W 0 tilde.eq U, quad i compose u tilde.eq v $
  因而 $[v]=i_*[u]$, 证明了反向包含. 这里提升不必唯一; 正合性只要求它存在.

  现在对任意整数 $n$, 移位与旋转给出三条纤维序列
  $ A[n] stretch(->)^(f[n]) B[n] stretch(->)^(g[n]) C[n] $
  $ B[n] stretch(->)^(g[n]) C[n] stretch(->)^(delta[n]) A[n+1] $
  $ C[n] stretch(->)^(delta[n]) A[n+1] stretch(->)^(-f[n+1]) B[n+1] $
  对它们分别应用刚才的事实, 得到在 $H_T^n (B)$、$H_T^n (C)$、$H_T^(n+1) (A)$ 处的正合性. 最后一条中的负号不改变核与像, 因而长正合列可以使用通常的 $f_*$ 记号. 由于 $n$ 任意, 这就覆盖整条序列的每一项.

  各项都是 Abel 群, 后复合给出的映射都是群同态. 连接态射 $delta$ 对纤维序列自然, 所以序列之间的相容态射诱导长正合列之间的交换图. 对 $T$ 的态射作前复合, 也得到相应的反变自然性. 同伦范畴中的对应结论参见 @Stacks26[Tag 0149].
]

特别地, $partial^n[u]=0$ 当且仅当 $u:T->C[n]$ 可以沿 $g[n]$ 提升为 $T->B[n]$. 所以连接同态测量的正是*提升的障碍*: 障碍为零, 就存在提升.

#corollary(title: "谱与复形中的常用形式")[
  对谱中的纤维序列 $A->B->C$, 有同伦群长正合列
  $ dots->pi_n A->pi_n B->pi_n C stretch(->)^partial pi_(n-1) A->pi_(n-1) B->dots $
  其中 $n$ 可以是任意整数, $partial$ 由连接态射 $C->A[1]$ 和 $pi_n (A[1]) tilde.eq pi_(n-1) A$ 诱导.

  对普通环 $R$ 的导出无穷范畴 $Dcat(R)$ 中的纤维序列 $A->B->C$, 有上同调长正合列
  $ dots->cal(H)^n (A)->cal(H)^n (B)->cal(H)^n (C) stretch(->)^(partial^n) cal(H)^(n+1) (A)->cal(H)^(n+1) (B)->dots $
] <cor-stable-homotopy-cohomology-long-exact>

#proof[
  在 $Sp$ 中取 $T=SS$, 则
  $ H_SS^k (X)=Hom_(op("h") Sp) (SS,X[k]) tilde.eq pi_(-k) X $
  在上一命题中令 $k=-n$, 就得到第一条长正合列.

  在 $Dcat(R)$ 中取集中在零次的自由模 $T=R$, 有自然同构
  $ H_R^n (X)=Hom_(op("h") Dcat(R)) (R,X[n]) tilde.eq cal(H)^n (X) $
  因为从 $R$ 作映射由 $1$ 的像决定: 链映射给出闭元, 链同伦识别相差一个边界的闭元; 而 $R$ 自身就是投射模, 这一计算也给出导出范畴中的映射类. 代入上一命题即得第二式, 其中各同态还保持 $R$-线性.
]

=== 例: 球谱、整数自映射与 Moore 谱

现在用球谱来练习上述长正合列. 回顾
$ SS:=Sigma^oo S^0, quad SS smash E tilde.eq E $
它是砸积的单位, 因而自然带有 $EE_oo$ 环谱结构, 乘法就是 $SS smash SS tilde.eq SS$. 它也是交换环谱范畴的始对象: 对任意交换环谱 $R$,
$ Map_(CAlg(Sp)) (SS,R) tilde.eq * $
这对应普通交换环中 $ZZ->R$ 的角色. 同时 $Mod_(SS) tilde.eq Sp$, 所以谱都可以看成球谱上的模.

用球谱探测同伦群, 就能看出它的自映射与整数的联系: 有环同构
$ op("End")_("h"Sp) (SS)=pi_0 SS tilde.eq ZZ $
这里自同态的加法来自稳定结构, 乘法是复合. 具体地,
$ pi_0 SS tilde.eq colim_(d->oo) pi_d (S^d) tilde.eq ZZ $
因为球面自映射的同伦类由度数分类, 悬挂保持度数. 恒等映射对应 $1$, 所以整数 $n$ 对应同伦类 $n dot id_(SS)$: 正整数表示把恒等态射相加 $n$ 次, 负整数再取加法逆元. 选取代表后, 简记为
$ n:SS->SS $
例如, 圆周映射 $z |-> z^n$ 的悬挂谱是 $SS[1]$ 上的乘 $n$ 映射, 再移位 $[-1]$ 就得到上述自映射. 相加与复合分别对应整数的加法与乘法; 因而 $n:SS->SS$ 是等价当且仅当 $n=plus.minus 1$. 参见 @May99[第 25 章, 第 6--7 节].

#remark(title: "谱自映射与环谱自同态")[
  上面的 $ZZ$ 分类的是*底层谱自映射的同伦类*, 也就是 $SS$-模自同态的同伦类. 从环谱角度看, $n in pi_0 SS$ 是标量, $n:SS->SS$ 是乘这个标量的模映射.

  保持单位的环谱自同态则满足
  $ Map_(Alg(Sp)) (SS,SS) tilde.eq Map_(CAlg(Sp)) (SS,SS) tilde.eq * $
  因而只有恒等态射, 到可缩选择为止. 当 $n!=1$ 时, 乘 $n$ 把 $pi_0 SS$ 中的 $1$ 送到 $n$, 不保持单位, 所以不是这里的环谱态射.
]

#definition(title: [模 $n$ 的 Moore 谱])[
  对整数 $n>=2$, 定义
  $ M_n:=SS slash n:=cofib(SS stretch(->)^n SS) $
  称为*模 $n$ 的 Moore 谱*. 它带有正合序列
  $ SS stretch(->)^n SS->M_n->SS[1] $
  这里的余纤维在 $Sp$ 中取; 记号 $SS slash n$ 指这个谱, 本身并未指定环谱乘法.
] <def-mod-n-moore-spectrum>

直观上, 这相当于在球谱上附加一个胞腔, 把乘 $n$ 的映射填掉, 并保留这次填充的同伦数据. Moore 谱的环谱结构是额外的问题, 不能由这个余纤维定义自动得到. 参见 @Bha20[第 1 节].

应用 @cor-stable-homotopy-cohomology-long-exact, 得到
$ dots->pi_k SS stretch(->)^n pi_k SS->pi_k M_n->pi_(k-1) SS stretch(->)^n pi_(k-1) SS->dots $
球谱的负次同伦群为零, 零次为 $ZZ$, 因而立即读出
$ pi_0 M_n tilde.eq ZZ slash n ZZ, quad pi_k M_n=0 quad (k<0) $
更高的同伦群则继续由这条长正合列计算.

Moore 谱的普通整数同调也很简单. 因为砸积保持余纤维,
$ H ZZ smash M_n tilde.eq cofib(H ZZ stretch(->)^n H ZZ) tilde.eq H(ZZ slash n ZZ) $
最后一步就是普通复形 $ZZ stretch(->)^n ZZ$ 的余纤维计算. 所以, 若记谱的整数同调为 $H_k (E;ZZ):=pi_k (H ZZ smash E)$, 则 $M_n$ 的整数同调只在零次非零, 值为 $ZZ slash n ZZ$. 这描述的是它的普通同调, 并不要求它的高次同伦群消失.

最后, 对任意谱 $E$, 乘 $n$ 的映射由标量作用给出:
$ n_E:E tilde.eq SS smash E stretch(->)^(n smash id_E) SS smash E tilde.eq E $
由于砸积保持加法, 它正是 $n dot id_E$, 在每个 $pi_k E$ 上诱导通常的乘 $n$. 因而
$ E slash n:=cofib(n_E) tilde.eq E smash M_n $
这就是 Moore 谱最直接的用途: 通过一次砸积, 构造谱的模 $n$ 系数版本. 其同伦群由
$ dots->pi_k E stretch(->)^n pi_k E->pi_k (E slash n)->pi_(k-1) E stretch(->)^n pi_(k-1) E->dots $
计算; 它同时记录 $pi_k E$ 的模 $n$ 商和相邻次数里被 $n$ 杀掉的元素.

=== 稳定以后仍然要指定零同伦

取非零对象 $A$, 考虑两条零态射
$ A->0->Sigma A $
它们的复合已经是零, 但仍有不同的零同伦可选. 按 @def-pointed-fiber-sequence, 判断它是否为纤维序列, 要看所选零同伦诱导的比较态射
$ A->fib(0->Sigma A)=Omega Sigma A $
是否为等价.

若取定义悬挂的方块自带的交换同伦, 比较态射就是自然等价 $eta_A:A->Omega Sigma A$. 因此得到正合序列. 若改取常值同伦, 比较态射则是零态射. 将 $Omega Sigma A$ 识别为 $A$ 后, 两种情况分别是
$ id_A:A->A, quad 0:A->A $
由于 $A$ 非零, 零自态射不可能是等价: 否则 $id_A tilde.eq 0$, 进而 $A tilde.eq 0$.

所以, 即使在稳定情形, *同样的三个对象和两条箭头, 配上不同零同伦, 也可能一个正合、另一个不正合*. 与圆周的例子一样, 零同伦实际参与了纤维的识别.

=== 用纤维或余纤维判别等价

#proposition(title: "等价判别")[
  稳定无穷范畴中的态射 $f:X->Y$ 满足
  $ f "是等价" quad <==> quad fib(f) tilde.eq 0 quad <==> quad cofib(f) tilde.eq 0 $
] <prop-stable-equivalence-criterion>

#proof[
  若 $f$ 是等价, 它的纤维等价于恒等态射的纤维, 因而为零. 反过来, 若 $fib(f) tilde.eq 0$, 定义纤维的方块可写成

  #align(center)[
    #book-diagram(
      spacing: 27pt, cell-size: 0pt, node-inset: 5pt,
      {
        fletcher.edge((0, 0), (1, 0), marks: "->")
        fletcher.edge((0, 0), (0, 1), marks: "->")
        fletcher.edge((1, 0), (1, 1), $f$, label-side: left, marks: "->")
        fletcher.edge((0, 1), (1, 1), marks: "->")
        fletcher.node((0, 0), $0$)
        fletcher.node((1, 0), $X$)
        fletcher.node((0, 1), $0$)
        fletcher.node((1, 1), $Y$)
      },
    )
  ]

  它也为推出方块, 所以 $f$ 是等价 $0->0$ 的推出, 从而是等价. 最后, 由 @prop-stable-fiber-cofiber-shift, 纤维为零与余纤维为零等价.
]

于是, 在正合序列 $A->B->C$ 中, 第一条态射是等价当且仅当 $C tilde.eq 0$, 第二条态射是等价当且仅当 $A tilde.eq 0$. 在 $Dcat(R)$ 中, 这恢复了熟悉的判据: 复形态射是拟同构, 当且仅当它的映射锥无上同调.

#example(title: "一般带基点情形的区别")[
  在 $Ani_*$ 中, 取带基点的离散两点生象 $S^0$, 则基点包含 $*->S^0$ 的纤维是 $Omega S^0 tilde.eq *$, 即零对象. 但这个映射不是等价, 因为它没有覆盖另一个连通分支. 所以这里确实用到了稳定性.
]

=== 拉回可以通过作差取纤维计算

#proposition(title: "拉回的作差公式")[
  给定 $X stretch(->)^f Z stretch(<-)^g Y$, 令
  $ d:=f compose pr_X-g compose pr_Y:X ⊕ Y->Z $
  这里 $pr_X,pr_Y$ 是直和的两个投影; 也常把 $d$ 简写成 $(f,-g)$ 或 $f-g$. 则有自然等价
  $ X times_Z Y tilde.eq fib(d) $
  因而有正合序列
  $ X times_Z Y->X ⊕ Y stretch(->)^((f,-g)) Z $
] <prop-stable-pullback-difference>

#proof[
  对任意测试对象 $T$, 向 $X times_Z Y$ 作映射, 就是给出 $u:T->X$、$v:T->Y$, 连同一个同伦
  $ f compose u tilde.eq g compose v $
  在映射生象 $Map_(cal(C)) (T,Z)$ 中作平移, 这等价于指定零同伦
  $ f compose u-g compose v tilde.eq 0 $
  而 $(u,v)$ 正好给出态射 $T->X ⊕ Y$. 因而这些数据就是向 $fib(d)$ 作映射的数据. 这个对应对 $T$ 自然, 并保留所有高阶同伦, 所以由 Yoneda 引理得到所需等价.
]

直观上, 拉回要求两边的像相容; 稳定语境中的加法允许把这个条件写成"差为零", 而纤维负责记录零化同伦. 对这条正合序列应用上同调函子, 就得到 Mayer--Vietoris 型的长正合列.

对偶地, 推出也可以通过余纤维计算: 若有 $Y stretch(<-)^f X stretch(->)^g Z$, 则
$ Y coprod_X Z tilde.eq cofib(X stretch(->)^((f,-g)) Y ⊕ Z) $
这两条公式让有限的粘合问题转化为直和与纤维、余纤维的计算.

=== 分裂与扩张类

考虑正合序列及其连接态射
$ A stretch(->)^f B stretch(->)^g C stretch(->)^delta A[1] $
最容易处理的例子是标准直和序列
$ A stretch(->)^(i_A) A ⊕ C stretch(->)^(pr_C) C $
其中 $i_A$ 是自然嵌入, $pr_C$ 是投影, 取标准的零同伦. 若原序列与它等价, 并与两端 $A,C$ 的给定识别相容, 就称原序列*分裂*. 这个要求也包括零同伦的相容性.

#proposition(title: "分裂的等价条件")[
  对上述正合序列, 下列条件等价:
  + $delta tilde.eq 0$, 即连接态射存在零同伦.
  + $g$ 有截面: 存在 $s:C->B$, 使 $g compose s tilde.eq id_C$.
  + $f$ 有收缩: 存在 $r:B->A$, 使 $r compose f tilde.eq id_A$.
  + 这条正合序列分裂.
] <prop-stable-splitting>

#proof[
  *$(1)=>(4)$.* 由 @prop-stable-connecting-morphism, $B tilde.eq fib(delta)$. 选定 $delta$ 的零同伦, 就得到态射图表 $delta$ 与零态射之间的等价. 取纤维并使用 @prop-fiber-zero-morphism,
  $ B tilde.eq fib(0_(C,A[1])) tilde.eq C times Omega A[1] tilde.eq C ⊕ A $
  交换两个直和因子的次序, 就得到 $A ⊕ C$. 由于整个构造在纤维方块之间进行, 这个等价同时把原序列识别为标准直和序列.

  *$(4)=>(2),(3)$.* 标准直和序列有自然截面 $i_C:C->A ⊕ C$ 和自然收缩 $pr_A:A ⊕ C->A$, 沿等价传回即可.

  *$(2)=>(1)$.* 正合序列提供 $delta compose g tilde.eq 0$, 所以若 $g compose s tilde.eq id_C$, 就有
  $ delta tilde.eq delta compose g compose s tilde.eq 0 $

  *$(3)=>(1)$.* 由旋转, $f[1] compose delta tilde.eq 0$. 若 $r compose f tilde.eq id_A$, 则
  $ delta tilde.eq r[1] compose f[1] compose delta tilde.eq 0 $
  因而四个条件等价. 相应的同伦范畴结论见 @Stacks26[Tag 05QT].
]

分裂是否存在, 由 $delta$ 的同伦类决定; 具体选哪个分裂, 则需要选择零同伦. 这种选择一般不唯一. 在同伦范畴中, 选定一个分裂及截面 $s$ 后, 其余截面恰好写成
$ s+f compose t, quad t in Hom_("h"cal(C)) (C,A) $
这与普通模的分裂短正合列完全一致: 可以在截面上加一个落入左端的态射.

现在固定两端 $A,C$. 把正合序列 $A->B->C$ 看成 *$C$ 被 $A$ 扩张*: $B$ 是将两端组合起来的中间对象, $delta$ 则记录组合的方式.

#proposition(title: "连接态射刻画扩张")[
  记 $cal(E)(C,A)$ 为两端带有给定识别的正合序列 $A->B->C$ 所组成的生象; 它的态射是与两端识别相容的序列等价, 并保留全部高阶同伦. 则连接态射给出等价
  $ cal(E)(C,A) tilde.eq Map_(cal(C)) (C,A[1]) $
  特别地, 这类扩张的等价类由
  $ pi_0 cal(E)(C,A) tilde.eq Hom_("h"cal(C)) (C,A[1]) $
  分类, 零元对应分裂扩张.
] <prop-stable-extension-classification>

#proof[
  从扩张出发, 按 @prop-stable-connecting-morphism 取连接态射 $delta$. 反过来, 给定 $delta:C->A[1]$, 令
  $ B:=fib(delta)=C times_(A[1]) 0 $
  投影 $B->C$ 的纤维为 $0 times_(A[1]) 0=Omega A[1] tilde.eq A$, 因而得到扩张 $A->B->C$. 又因为纤维方块也是推出, 它恢复的连接态射正是所给的 $delta$.

  两个构造互逆, 且都由拉回、推出的泛性质给出, 所以它们也保留等价及高阶相容性. 因而得到生象的等价. 关于零元的断言就是 @prop-stable-splitting.
]

在 $Dcat(R)$ 中, 若 $A,C$ 是放在零次的普通 $R$-模, 就有
$ Hom_("h"Dcat(R)) (C,A[1])=Ext_R^1 (C,A) $
此时这些扩张正好对应普通短正合列
$ 0->A->M->C->0 $
确实, 对 $A->B->C$ 取上同调, 长正合列说明 $B$ 仅在零次有上同调, 并给出上述短正合列, 其中 $M=cal(H)^0 (B)$. 因而 $[delta] in Ext_R^1 (C,A)$ 就是通常的扩张类. 参见 @Stacks26[Tags 06XP, 06XU].

#example(title: "一个不分裂的整数模扩张")[
  对 $n>=2$, 考虑
  $ 0->ZZ stretch(->)^n ZZ->ZZ slash n ZZ->0 $
  商映射没有截面: 任何群同态 $ZZ slash n ZZ->ZZ$ 都是零, 因为 $ZZ$ 没有非零挠元. 因此其连接态射
  $ delta:ZZ slash n ZZ->ZZ[1] $
  不零同伦. 用自由分解 $0->ZZ stretch(->)^n ZZ->ZZ slash n ZZ->0$ 计算,
  $ Ext_ZZ^1 (ZZ slash n ZZ,ZZ) tilde.eq coker(ZZ stretch(->)^n ZZ) tilde.eq ZZ slash n ZZ $
  这条短正合列给出其中的一个非零类, 因而中间的 $ZZ$ 无法按此序列分解为 $ZZ ⊕ (ZZ slash n ZZ)$.
]

这也解释了投射模的分裂性质: 若普通模 $C$ 投射, 则对任意 $A$ 都有 $Ext_R^1 (C,A)=0$, 所以每个以 $C$ 为右端的短正合列都分裂. 从稳定语境看, 原因正是所有连接态射 $C->A[1]$ 都零同伦.
