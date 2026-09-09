#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= 谱 / Spectra

本章沿着稳定无穷范畴、谱、环谱及其模这条线展开. 先把"稳定"说清楚: 我们希望悬挂与取环路成为可逆的操作, 让同伦论中的纤维、余纤维和移位像同调代数那样配合起来. 后面再给谱添加 $EE_1$ 或 $EE_oo$ 乘法, 就进入环谱及其模的理论.

== 稳定无穷范畴

本节只介绍定义、直观和几个基本结论. 所有极限、余极限与交换图都在无穷范畴中理解, 因而包含指定的同伦及其相容性. 主要参考 @Lur17[第 1.1 节].

=== 零对象与纤维的回顾

详细定义与泛性质见 @chap-fiber-sequence. 以下设 $C$ 是带基点无穷范畴, 记零对象为 $0$, 并假设 $C$ 具有有限极限与有限余极限.

对态射 $f:x->y$, 沿用纤维与余纤维的记号
$ fib(f):=x times_y 0, quad cofib(f):=y coprod_x 0 $
纤维序列与余纤维序列分别对应左下角为零对象的拉回、推出方块, 都包含指定的零同伦.

=== 悬挂与环路: $Sigma$ 和 $Omega$

#definition(title: "悬挂函子与环路函子")[
  定义*悬挂* (suspension) 与*环路* (loop) 函子
  $ Sigma:C->C, quad Sigma x:=0 coprod_x 0=cofib(x->0) $
  $ Omega:C->C, quad Omega x:=0 times_x 0=fib(0->x) $
  它们对 $x$ 自然, 所以确实给出函子. 参见 @Lur17[第 1.1.2 节].
] <def-suspension-loop>

这两个构造由下面的方块确定:

#align(center)[
  #grid(
    columns: (1fr, 1fr),
    column-gutter: 24pt,
    align: center,
    [
      #book-diagram(
        spacing: 25pt, cell-size: 0pt, node-inset: 5pt,
        {
          fletcher.edge((0, 0), (1, 0), marks: "->")
          fletcher.edge((0, 0), (0, 1), marks: "->")
          fletcher.edge((1, 0), (1, 1), marks: "->")
          fletcher.edge((0, 1), (1, 1), marks: "->")
          fletcher.node((0, 0), $x$)
          fletcher.node((1, 0), $0$)
          fletcher.node((0, 1), $0$)
          fletcher.node((1, 1), $Sigma x$)
        },
      )
      \ 推出方块
    ],
    [
      #book-diagram(
        spacing: 25pt, cell-size: 0pt, node-inset: 5pt,
        {
          fletcher.edge((0, 0), (1, 0), marks: "->")
          fletcher.edge((0, 0), (0, 1), marks: "->")
          fletcher.edge((1, 0), (1, 1), marks: "->")
          fletcher.edge((0, 1), (1, 1), marks: "->")
          fletcher.node((0, 0), $Omega x$)
          fletcher.node((1, 0), $0$)
          fletcher.node((0, 1), $0$)
          fletcher.node((1, 1), $x$)
        },
      )
      \ 拉回方块
    ],
  )
]

在 $Ani_*$ 中, $Omega x$ 就是以基点为起终点的环路生象. $Sigma x$ 则是*约化悬挂*: 可以把 $x$ 沿一个区间展开, 再把两端和原基点扫过的线段压到基点. 例如
$ Sigma S^n tilde.eq S^(n+1) quad (n>=0), quad Omega S^1 tilde.eq ZZ $
第一式让我们把悬挂想成"升一维"; 第二式说明取环路会把绕圆周的次数变成不同的连通分支. 这里并不是在说任意生象都有一个单一的维数.

#proposition(title: "悬挂与环路互为伴随")[
  存在自然伴随 $Sigma tack.l Omega$. 即对任意 $x,y in C$,
  $ Map_C (Sigma x,y) tilde.eq Map_C (x,Omega y) $
  它的单位与余单位分别为
  $ eta_x:x->Omega Sigma x, quad epsilon_x:Sigma Omega x->x $
]

#proofsketch[
  用映射生象检验 @def-suspension-loop 中的推出与拉回, 两边都等价于
  $ * times_(Map_C (x,y)) * $
  其中两个点都取零态射. 这就给出伴随.
]

在带基点空间中, 一个映射 $Sigma x->y$ 可以看成给每个 $a in x$ 指定 $y$ 中的一条环路, 因而也就是映射 $x->Omega y$. 不过, *伴随还不意味着互逆*. 例如带基点的两点生象 $S^0$ 满足
$ Omega S^0 tilde.eq *, quad Sigma Omega S^0 tilde.eq * != S^0 $
取环路后, 另一个连通分支已经看不见了.

=== 稳定性: 推出与拉回成为同一条件

#definition(title: "稳定无穷范畴")[
  无穷范畴 $C$ 称为*稳定的* (stable), 若:
  - $C$ 有零对象.
  - $C$ 有有限极限与有限余极限.
  - $C$ 中的一个交换方块是推出方块, 当且仅当它是拉回方块.

  这是稳定性的标准等价表述. 参见 @Lur17[定义 1.1.1.9, 命题 1.1.3.4].
] <def-stable-infty-category>

因此, 在稳定无穷范畴中, 纤维序列与余纤维序列是同一个概念, 统一称为*正合序列*. 它仍包含相邻态射复合到零的指定同伦.

#proposition(title: "稳定时悬挂与环路互逆")[
  若 $C$ 稳定, 则上述伴随的单位与余单位都是等价:
  $ Omega Sigma tilde.eq id_C, quad Sigma Omega tilde.eq id_C $
  因而 $Sigma$ 与 $Omega$ 是互逆的自等价.

  反过来, 一个带基点且具有有限极限与有限余极限的无穷范畴, 若 $Sigma tack.l Omega$ 是伴随等价, 则它稳定. 参见 @Lur17[推论 1.4.2.27].
] <prop-stable-suspension-loop>

#proofsketch[
  稳定时, 定义 $Sigma x$ 的推出方块也能当作拉回方块读, 于是
  $ x tilde.eq 0 times_(Sigma x) 0=Omega Sigma x $
  对偶地, 定义 $Omega x$ 的拉回方块也是推出方块, 所以 $Sigma Omega x tilde.eq x$. 反向判据使用同样的思想处理一般方块, 这里略去证明.
]

因此, 在稳定环境中可以放心地向两个方向移位. 约定
$ x[n]:=cases(Sigma^n x & quad n>=0, Omega^(-n) x & quad n<0) $
便有 $x[0] tilde.eq x$ 与 $x[n][m] tilde.eq x[n+m]$. 这里的稳定并不是要求 $Sigma x tilde.eq x$, 而是说*悬挂以后仍能完整地恢复原对象*.

=== 用复形理解稳定性

#example(title: "导出无穷范畴中的移位与映射锥")[
  对普通环 $R$, 将 $R$-模复形中的拟同构在无穷范畴意义下取逆, 得到*导出无穷范畴* $Dcat(R)$. 它是稳定的, 同伦范畴就是通常的导出范畴. 参见 @Lur17[第 1.3 节].

  采用上链复形约定, 悬挂与环路正是熟悉的移位:
  $ Sigma M tilde.eq M[1], quad Omega M tilde.eq M[-1], quad (M[1])^q=M^(q+1) $
  其中 $M[1]$ 的微分为 $-d_M$. 对复形态射 $f:M->N$,
  $ cofib(f) tilde.eq op("Cone")(f), quad fib(f) tilde.eq op("Cone")(f)[-1] $
  所以纤维与余纤维是同一个映射锥的不同移位.

  例如, 在 $Dcat(ZZ)$ 中把整数看作集中在零次的复形, 就有正合序列
  $ ZZ stretch(->)^2 ZZ -> ZZ slash 2 ZZ $
  它同时表达: 右端是乘二映射的余纤维, 左端是取模二映射的纤维. 对一般映射, 映射锥还会保留普通核、余核之外的同调信息.
]

这种现象在每个稳定无穷范畴中都成立:
$ cofib(f) tilde.eq Sigma fib(f) $
任意正合序列还可以接出连接态射, 写成
$ x->y->z->x[1] $
再继续向两端移位. 在同伦范畴中, 这些就是区分三角, 并赋予 $op("h") C$ 典范的三角范畴结构. 这里先记住三角来自真实的纤维、余纤维构造即可. 参见 @Lur17[定理 1.1.2.14].

#proposition(title: "有限直和与正合函子")[
  在稳定无穷范畴中, 典范映射 $x coprod y->x times y$ 是等价, 这个共同对象记为 $x ⊕ y$, 称为*直和*. 同伦范畴中的态射集
  $ Hom_("h"C) (x,y)=pi_0 Map_C (x,y) $
  自然是Abel群, 且复合是双线性的.

  稳定无穷范畴之间的函子 $F:C->D$ 称为*正合的*, 若它保持有限极限; 等价地, 它保持有限余极限. 正合函子因而保持零对象、纤维与余纤维序列, 并自然地满足
  $ F(Sigma x) tilde.eq Sigma F(x), quad F(Omega x) tilde.eq Omega F(x) $
  参见 @Lur17[第 1.1.2 节, 命题 1.1.4.1].
]

后面遇到谱及环谱的模时, 这些规则可以直接使用: 用纤维描述零化条件, 用余纤维构造同伦商, 用移位把它们互相转换. 下一节的谱范畴 $Sp$, 就是把这种稳定的运算方式引入生象所得到的基本例子.

== 谱的两种定义

谱可以从两边认识. 一边把它看作一种满足切除性质的"测量规则", 另一边把它写成一列能够不断解环路的生象. 前者方便处理空间的粘合, 后者方便逐层描述. 我们会说明这两种写法保留完全相同的对象、态射与高阶同伦.

=== 第一种定义: 切除函子

记 $Ani_*^"fin"$ 为*有限带基点生象*组成的无穷范畴. 它由 $S^0$ 和零对象 $*$ 经有限同伦余极限生成, 可以用有限带基点 CW 复形来理解. 这里的"有限"指有限的胞腔构造, 所以圆周与各维球面都包括在内. 参见 @Lur17[记号 1.4.2.5].

#definition(title: "约化与切除性质")[
  设 $F:Ani_*^"fin"->Ani_*$ 是无穷函子.
  - 若 $F(*) tilde.eq *$, 称 $F$ 为*约化的* (reduced).
  - 若 $F$ 将每个推出方块变成拉回方块, 称 $F$ 为*切除的* (excisive). 具体地, 对任意推出 $d=b coprod_a c$, 自然映射
    $ F(a) -> F(b) times_(F(d)) F(c) $
    必须是等价.

  这些条件及方块都在无穷范畴中理解. 参见 @Lur17[定义 1.4.2.1].
] <def-reduced-excisive>

约化表示"一个点没有额外信息". 切除则表示: 当 $d$ 由 $b,c$ 沿 $a$ 粘合而成时, $F(a)$ 恰好记录 $F(b)$ 与 $F(c)$ 映入 $F(d)$ 后的全部相容数据. 这是 Mayer–Vietoris 型关系的生象版本.

#definition(title: [谱])[
  一个*谱* (spectrum) 是约化切除函子 $F:Ani_*^"fin"->Ani_*$. 记它们组成的满子无穷范畴为
  $ Sp:=Exc_* (Ani_*^"fin",Ani_*) subset.eq Fun(Ani_*^"fin",Ani_*) $
  谱之间的态射就是自然变换, 并保留自然变换之间的全部同伦. 参见 @Lur17[定义 1.4.2.8, 定义 1.4.3.1].
] <def-spectrum-excisive>

这里 $F$ 是*协变*的. 也可以把值域写成 $Ani$: 因为 $F(*) tilde.eq *$, 映射 $*->k$ 会自然地为每个 $F(k)$ 指定基点, 所以两种写法等价.

=== 第二种定义: $Omega$-谱

#definition(title: [$Omega$-谱])[
  一个 *$Omega$-谱*是一列带基点生象
  $ E_0,E_1,E_2,dots $
  连同指定的基点保持等价
  $ alpha_n:E_n ->^~ Omega E_(n+1) quad (n>=0) $
  从 $E$ 到 $E'$ 的态射由各层映射 $f_n:E_n->E'_n$ 及相容同伦
  $ alpha'_n compose f_n tilde.eq Omega(f_(n+1)) compose alpha_n $
  组成, 并保留全部高阶相容性.

  严格地说, 它们组成的无穷范畴是
  $ Sp_Omega:=lim(dots stretch(->)^Omega Ani_* stretch(->)^Omega Ani_* stretch(->)^Omega Ani_*) $
  这个极限在无穷范畴的无穷范畴中计算. 它把上面的相容同伦一起纳入定义. 参见 @Lur17[命题 1.4.2.24, 注 1.4.2.25].
] <def-omega-spectrum>

可以把 $E_(n+1)$ 看作 $E_n$ 的一次*解环路* (delooping): 取环路以后得到 $E_n$. 因而
$ E_0 tilde.eq Omega E_1 tilde.eq Omega^2 E_2 tilde.eq dots $
谱记录的是这整套可以无限继续的解环路数据. 由 $Sigma tack.l Omega$, $alpha_n$ 也对应结构映射 $Sigma E_n->E_(n+1)$; 要求是 $alpha_n$ 为等价, 并不要求这个伴随过去的结构映射为等价.

=== 两种定义怎样互相恢复

先看容易的方向. 给定切除函子 $F$, 定义
$ E_n:=F(S^n) $
球面的悬挂由推出 $S^(n+1) tilde.eq * coprod_(S^n) *$ 给出. 因为 $F$ 约化且切除, 有
$ F(S^n) tilde.eq * times_(F(S^(n+1))) * = Omega F(S^(n+1)) $
这就得到一个 $Omega$-谱, 并定义函子
$ Phi:Sp_"exc" -> Sp_Omega, quad F |-> (F(S^n))_(n>=0) $

反方向要解释: 只知道这些球面上的值与结构等价, 为什么就能恢复 $F$ 在其他有限生象上的值? 我们用两个简短的准备事实.

#lemma(title: [$Omega$-谱已经组成稳定无穷范畴])[
  $Sp_Omega$ 是稳定的. 它的环路逐层计算, 悬挂则由移位给出:
  $ (Omega E)_n tilde.eq Omega E_n, quad (Sigma E)_n tilde.eq E_(n+1) $
  特别地, 取第零层的函子 $ev_0:Sp_Omega->Ani_*$ 保持有限极限.
] <lem-omega-spectra-stable>

#proofsketch[
  零对象与极限都逐层计算, 因为 $Omega$ 保持极限. 此外, $Ani_*$ 可呈示, $Omega$ 是可达右伴随, 所以上述逆极限仍可呈示, 特别有有限余极限; 这是可呈示无穷范畴的极限定理 @Lur09[定理 5.5.3.18]. 这一步保证了余极限的存在, 不要求它逐层计算.

  记去掉首项的移位为 $s(E)_n=E_(n+1)$. 结构等价给出 $Omega s(E) tilde.eq E$ 和 $s(Omega E) tilde.eq E$. 因而环路是自等价, 由 @prop-stable-suspension-loop 得到稳定性, 且 $Sigma tilde.eq s$.
]

#lemma(title: "从一个对象延拓到有限带基点生象")[
  设 $D$ 是稳定无穷范畴. 对每个 $e in D$, 存在保持有限余极限的函子
  $ L_e:Ani_*^"fin"->D, quad L_e (S^0) tilde.eq e $
  连同这个识别, 延拓的选择组成可缩生象. 更准确地, 在 $S^0$ 处求值给出等价
  $ Fun^"rex" (Ani_*^"fin",D) ->^~ D $
  其中 $"rex"$ 表示保持有限余极限. 因而这条泛性质也确定函子之间的自然变换及全部高阶同伦. 参见 @Lur17[注 1.4.2.6, 引理 1.4.2.19].
] <lem-finite-pointed-extension>

直观上, $L_e$ 就是把有限生象的胞腔粘合过程搬到 $D$ 中, 从 $S^0 |-> e$ 开始执行. 泛性质保证不同的胞腔表达给出相容的同一结果. 特别地,
$ L_e (*) tilde.eq 0, quad L_e (S^n) tilde.eq Sigma^n e $

#theorem(title: "两种谱定义保留同样的信息")[
  在球面上求值给出无穷范畴的等价
  $ Phi:Sp_"exc" ->^~ Sp_Omega $
  以后把这个共同的无穷范畴记为 $Sp$. 这正是 @Lur17[命题 1.4.2.24] 在生象中的情形.
] <thm-spectrum-definitions-equivalent>

#proof[
  *从序列恢复函子.* 给定 $E in Sp_Omega$, 对稳定范畴 $D=Sp_Omega$ 应用 @lem-finite-pointed-extension, 定义
  $ Psi(E):=ev_0 compose L_E:Ani_*^"fin" -> Ani_* $
  $L_E$ 将推出送到 $Sp_Omega$ 中的推出, 稳定性又使它成为拉回; $ev_0$ 保持拉回. 所以 $Psi(E)$ 约化且切除. 而且
  $ Psi(E)(S^n) tilde.eq ev_0(Sigma^n E) tilde.eq E_n $
  这些等价与结构映射相容, 因而 $Phi Psi(E) tilde.eq E$.

  *检查整个函子也能恢复.* 给定 $F in Sp_"exc"$, 对每个有限带基点生象 $k$, 定义一个 $Omega$-谱
  $ hat(F)(k)_n:=F(Sigma^n k) $
  它的结构等价仍来自悬挂方块的切除性质. 因为 $Sigma^n$ 保持推出, $F$ 把推出变成拉回, 而 $Sp_Omega$ 的拉回逐层计算, 所以 $hat(F)$ 也是约化切除函子. 目标稳定, 故它保持有限余极限.

  现在 $hat(F)(S^0)=Phi(F)$. 由 @lem-finite-pointed-extension 的唯一性,
  $ hat(F) tilde.eq L_(Phi(F)) $
  在第零层求值就得到 $F tilde.eq Psi Phi(F)$. 上述构造对态射与高阶同伦都自然, 所以 $Phi,Psi$ 互为逆等价.
]

因此,"同样的信息"也包括映射生象:
$ Map_(Sp_"exc") (F,G) tilde.eq Map_(Sp_Omega) (Phi(F),Phi(G)) $
切除函子怎样随参数变化, 也可以完整地从相应的 $Omega$-谱中读出.

=== 最简单的例子与使用方式

#example(title: "Eilenberg–MacLane 谱")[
  对Abel群 $A$, 令 $K(A,n)$ 为只有第 $n$ 个同伦群是 $A$ 的 Eilenberg–MacLane 生象, 并令 $K(A,0)=A$ 为离散生象. 标准等价
  $ K(A,n) tilde.eq Omega K(A,n+1) $
  给出谱
  $ H A=(A,K(A,1),K(A,2),dots) $
  它把同一个Abel群放到逐渐升高的同伦次数中, 是普通同调代数进入谱论的基本例子. 参见 @Lur17[命题 1.4.3.6].
]

在两种表述下, *第零层*函子记为
$ Omega^oo:Sp->Ani_*, quad Omega^oo E=E_0=F(S^0) $
这个记号表示取谱所带的无穷环路生象. 只保留 $E_0$ 一般会丢失信息: 例如 $H A[-1]$ 的第零层可缩, 第一层却是 $A$. 当 $A!=0$ 时, 它仍是非零谱.

计算时, $Omega$-谱让我们逐层取同伦群. 对任意整数 $q$, 取 $n$ 足够大使 $n+q>=2$, 定义
$ pi_q E:=pi_(n+q) (E_n) $
结构等价保证它与所取的 $n$ 无关, 并自然是Abel群. 例如 $pi_0 (H A)=A$, 其余 $pi_q (H A)$ 为零. 遇到空间的粘合时, 则切回切除函子的表述, 直接将推出转为拉回. 两种定义之间的等价保证这些操作始终作用于同一个谱.

== 从熟悉的空间与上同调出发

先用球面和普通上同调认识谱. 这两个例子已经足以说明: 为什么要把空间送进稳定范畴, 又为什么一个谱能同时记录所有次数的上同调.

=== 悬挂谱与球谱

#definition(title: "悬挂谱")[
  第零层函子 $Omega^oo:Sp->Ani_*$ 有左伴随
  $ Sigma^oo:Ani_*->Sp $
  称 $Sigma^oo x$ 为带基点生象 $x$ 的*悬挂谱*. 它由自然等价
  $ Map_(Sp) (Sigma^oo x,E) tilde.eq Map_(Ani_*) (x,Omega^oo E) $
  刻画. 参见 @Lur17[命题 1.4.4.4].
] <def-suspension-spectrum>

直观上, 从 $x,Sigma x,Sigma^2 x,dots$ 出发, 把"继续悬挂"变成可逆操作, 就得到 $Sigma^oo x$. 这列空间先给出一个*预谱*, 再经过谱化得到上一节意义下的谱; 原来的结构映射不必已经满足 $Omega$-谱条件.

因为 $Sigma^oo$ 是左伴随, 它保持余极限, 特别有
$ Sigma^oo (Sigma x) tilde.eq (Sigma^oo x)[1], quad Sigma^oo (*) tilde.eq 0 $
因此, 空间中的余纤维序列会变成谱中的正合序列.

#example(title: "球谱记录稳定同伦")[
  *球谱*定义为
  $ SS:=Sigma^oo S^0 $
  它的移位满足 $SS[d] tilde.eq Sigma^oo S^d$ ($d>=0$). 球谱的同伦群就是球面的稳定同伦群:
  $ pi_q SS tilde.eq colim_(m->oo) pi_(q+m) (S^m) $
  这里从 $q+m>=2$ 开始取余极限, 过渡映射由悬挂给出. 例如 $pi_0 SS tilde.eq ZZ$, 记录球面自映射的度数. 参见 @May99[第 25 章, 第 6--7 节].

  更一般地, $pi_q (Sigma^oo x)$ 记录 $x$ 在不断悬挂后保留下来的同伦类. 所以悬挂谱提供了一种把空间问题送入稳定同伦论的办法.
]

对任意谱 $E$ 与整数 $q$, 有
$ pi_q E tilde.eq Hom_("h"Sp) (SS[q],E) $
也就是说, *同伦群是用各个移位的球谱去探测 $E$*. 这是后面把同调写成映射公式的起点.

=== $H A$: 上同调类就是映射

#example(title: "把普通上同调放进一个谱")[
  对带基点 CW 复形 $x$ 与 $n>=0$, 普通约化上同调满足
  $ tilde(H)^n (x;A) tilde.eq pi_0 Map_(Ani_*) (x,K(A,n)) $
  右边是保持基点的映射的同伦类. 因而一个上同调类可以看作一张映向 $K(A,n)$ 的地图. 参见 @Hat02[定理 4.57].

  上一节的 $H A$ 把这些目标空间组织在一起. 由悬挂谱伴随, 对所有整数 $n$,
  $ tilde(H)^n (x;A) tilde.eq Hom_("h"Sp) (Sigma^oo x,(H A)[n]) $
  这里普通上同调在负次数为零. 对 $n>=0$, 公式正是上式, 因为 $Omega^oo ((H A)[n]) tilde.eq K(A,n)$.

  例如 $K(ZZ,1) tilde.eq S^1$, 所以 $tilde(H)^1 (S^1;ZZ) tilde.eq ZZ$ 可以直接理解成圆周自映射的绕行次数. 现在同一个整数也能读成谱态射 $Sigma^oo S^1->(H ZZ)[1]$ 的同伦类.
]

这个例子提示我们: 如果一种上同调也有悬挂同构、正合序列和粘合性质, 能否找到一个谱来表示它? Brown 可表性给出肯定的回答.

== Brown 可表性与映射谱

=== 哪些上同调理论能够被表示

以下在所有带基点 CW 同伦型上讨论, 即在 $"h"Ani_*$ 上讨论, 不只限于有限 CW 复形. 记
$ [x,y]_*:=pi_0 Map_(Ani_*) (x,y), quad [a,b]_(Sp):=pi_0 Map_(Sp) (a,b) $

#definition(title: "广义约化上同调理论")[
  一套*广义约化上同调理论*由反变函子
  $ tilde(h)^n:("h"Ani_*)^op->Ab quad (n in ZZ) $
  及自然的悬挂同构 $tilde(h)^n (x) tilde.eq tilde(h)^(n+1) (Sigma x)$ 组成, 满足:
  - *约化:* $tilde(h)^n (*)=0$.
  - *正合:* 每个余纤维序列 $a->b->c$ 给出正合序列
    $ tilde(h)^n (c)->tilde(h)^n (b)->tilde(h)^n (a) $
  - *楔和公理:* 对任意小族带基点生象, 自然映射是同构
    $ tilde(h)^n (wedge_i x_i) ->^~ product_i tilde(h)^n (x_i) $

  这里 $wedge_i x_i$ 表示把各个基点粘在一起, 即 $Ani_*$ 中的余积. 悬挂同构与连接态射使上面的三项序列接成长正合序列. 参见 @May99[第 19 章, 第 2 节].
] <def-generalized-cohomology>

"广义"允许系数 $tilde(h)^n (S^0)$ 分布在多个次数. 普通上同调只有零次系数非零, 是其中最熟悉的例子.

#theorem(title: "Brown 可表性: 上同调由谱表示")[
  每个满足 @def-generalized-cohomology 的理论都存在一个表示谱 $E$, 使得对所有 $x$ 和所有整数 $n$, 有自然同构
  $ tilde(h)^n (x) tilde.eq [Sigma^oo x,E[n]]_(Sp) tilde.eq [x,Omega^oo (E[n])]_* $
  这些同构与悬挂及连接态射相容. 表示谱在等价意义下唯一, 但所取的等价不必唯一. 参见 @Hat02[定理 4E.1], @Lur17[第 1.4.1 节].
] <thm-brown-cohomology>

#proofsketch[
  Brown 定理的核心是为各次函子构造表示生象 $e_n$, 使
  $ tilde(h)^n (x) tilde.eq [x,e_n]_* $
  构造先用球面的楔和容纳所需的类, 再逐步接胞腔消除多余的关系. 正合性与楔和公理保证这个过程能推广到所有 CW 复形. 这一部分的胞腔论证略去, 见 @Hat02[第 4.E 节].

  一旦有了这些表示对象, 它们为什么组成谱就很直接了: 悬挂同构给出
  $ [x,e_n]_* tilde.eq tilde(h)^n (x) tilde.eq tilde(h)^(n+1) (Sigma x) $
  $ tilde(h)^(n+1) (Sigma x) tilde.eq [Sigma x,e_(n+1)]_* tilde.eq [x,Omega e_(n+1)]_* $
  由 Yoneda, 得到 $e_n tilde.eq Omega e_(n+1)$. 选择代表这些同伦等价的映射, 就能将 $(e_n)_(n>=0)$ 组织成 $Omega$-谱 $E$. 负次数由取环路恢复. 最后使用 @def-suspension-spectrum 的伴随即可.
]

Brown 定理让我们先研究一套上同调规则, 再把它变成一个几何对象 $E$. 不过, 它并没有说只列出所有系数群就能确定 $E$: 谱还记录这些信息之间的连接方式.

=== 从映射生象到映射谱

在稳定范畴中, 不仅对象能移位, 从一个对象到另一个对象的映射也能按次数组织起来.

#definition(title: "映射谱")[
  设 $C$ 为局部小的稳定无穷范畴, $x,y in C$. 定义*映射谱*
  $ underline(Map)_C (x,y) in Sp $
  为下列 $Omega$-谱:
  $ (underline(Map)_C (x,y))_n:=Map_C (x,y[n]) quad (n>=0) $
  各层以零态射为基点. 其结构等价来自
  $ Omega Map_C (x,y[n+1]) tilde.eq Map_C (x,Omega(y[n+1])) tilde.eq Map_C (x,y[n]) $
  因而这里确实满足 $Omega$-谱条件. 参见 @Lur17[第 1.1.2 节末, 命题 1.4.2.22].
] <def-mapping-spectrum>

它把 $x->y$, $x->y[1]$, $x->y[2]$, $dots$ 的映射生象及其解环路关系放在一起. 特别地,
$ Omega^oo underline(Map)_C (x,y) tilde.eq Map_C (x,y) $
$ pi_q underline(Map)_C (x,y) tilde.eq Hom_("h"C) (x[q],y) tilde.eq Hom_("h"C) (x,y[-q]) $
第二式对所有整数 $q$ 成立. *上移目标 $n$ 次, 对应映射谱的第 $-n$ 个同伦群*, 这个负号后面会经常出现.

#example(title: "熟悉的 Ext 群")[
  把普通 $R$-模 $M,N$ 看成 $Dcat(R)$ 中集中在零次的复形. 对 $n>=0$,
  $ pi_(-n) underline(Map)_(Dcat(R)) (M,N) tilde.eq Hom_("h"Dcat(R)) (M,N[n]) tilde.eq op("Ext")_R^n (M,N) $
  所以 $Hom$ 与各次 $Ext$ 可以从同一个映射谱中读出. $Ext^1$ 所描述的扩张, 就出现在这个谱的第 $-1$ 个同伦群中.
]

现在 Brown 定理的公式可以统一成一个对象. 对任意谱 $E$ 与带基点生象 $x$, 令
$ tilde(C)^* (x;E):=underline(Map)_(Sp) (Sigma^oo x,E) $
称它为*约化 $E$-上同调谱*. 它是一个谱, 这里的星号是记号的一部分, 并不表示已经取了分次群. 定义
$ tilde(E)^n (x):=pi_(-n) tilde(C)^* (x;E)=[Sigma^oo x,E[n]]_(Sp) $
这就同时记录了所有次数的 $E$-上同调. 特别地, 只取第零层映射生象通常看不见正次数的上同调, 因为它们位于映射谱的负同伦次数.

#remark(title: "谱上的 Brown 表述")[
  也可以直接在谱上说 Brown 定理: 若加性函子 $F:("h"Sp)^op->Ab$ 把正合序列 $a->b->c$ 送到正合序列 $F(c)->F(b)->F(a)$, 并把任意余积送到积, 则存在谱 $E$ 使
  $ F(a) tilde.eq [a,E]_(Sp)=pi_0 underline(Map)_(Sp) (a,E) $
  这里可表性来自 $Sp$ 由紧对象 $SS[n]$ ($n in ZZ$) 生成. 因而同样能在其他由一组紧对象生成的可呈示稳定无穷范畴中使用. 参见 @Lur17[定理 1.4.1.2, 例 1.4.1.3].
]

=== 同调怎样写成谱与映射

为了写同调, 还需要一种类似张量积的运算.

#definition(title: "砸积与同调谱")[
  谱范畴具有典范的对称幺半积, 称为*砸积*, 记为 $E smash F$. 它对每个变量保持小余极限, 单位对象为球谱:
  $ SS smash E tilde.eq E $
  对带基点生象, 它与悬挂谱相容:
  $ (Sigma^oo x) smash (Sigma^oo y) tilde.eq Sigma^oo (x smash y) $
  右边空间的砸积是把 $x times y$ 中的 $x wedge y$ 压到基点. 这些运算都按同伦意义理解. 参见 @Lur17[第 4.8.2 节, 尤其推论 4.8.2.19].

  定义*约化 $E$-同调谱*及其同调群为
  $ tilde(C)_* (x;E):=E smash Sigma^oo x, quad tilde(E)_n (x):=pi_n tilde(C)_* (x;E) $
  对有限带基点生象 $x$, 这也就是上一节的延拓 $L_E (x)$: 按 $x$ 的胞腔粘合方式, 用 $E$ 代替 $S^0$ 来构造一个谱.
] <def-spectrum-homology>

砸积与映射谱有熟悉的张量--Hom 关系:
$ Map_(Sp) (a smash b,E) tilde.eq Map_(Sp) (a,underline(Map)_(Sp) (b,E)) $
因此 $underline(Map)_(Sp) (b,E)$ 也称*函数谱*, 是谱范畴中的内部 Hom. 取 $b=SS$ 得到
$ underline(Map)_(Sp) (SS,E) tilde.eq E $
于是, 同调也可以用映射谱或映射类写出:
$ tilde(E)_n (x) tilde.eq pi_n underline(Map)_(Sp) (SS,E smash Sigma^oo x) tilde.eq [SS[n],E smash Sigma^oo x]_(Sp) $
上同调从 $Sigma^oo x$ 映入 $E$ 的移位; 同调先构造 $E smash Sigma^oo x$, 再用球谱的移位去探测它. 前者对 $x$ 反变, 后者对 $x$ 协变. 参见 @May99[第 25 章, 第 6 节].

#remark(title: "恢复通常的非约化记号")[
  对不带基点的生象 $x$, 添一个不相交的基点 $x_+:=x coprod *$, 并记 $Sigma^oo_+ x:=Sigma^oo (x_+)$. 定义
  $ E^n (x):=tilde(E)^n (x_+), quad E_n (x):=tilde(E)_n (x_+) $
  特别地, 点的非约化理论是
  $ E^n (*)=pi_(-n) E, quad E_n (*)=pi_n E $
  因为 $*_+=S^0$. 这与约化理论在点上为零完全相容.
]

=== 怎样用这些公式

#proposition(title: "粘合给出长正合序列")[
  对余纤维序列 $a->b->c$, 有谱的正合序列
  $ tilde(C)_* (a;E)->tilde(C)_* (b;E)->tilde(C)_* (c;E) $
  $ tilde(C)^* (c;E)->tilde(C)^* (b;E)->tilde(C)^* (a;E) $
  取同伦群分别得到同调与上同调的长正合序列. 因此每个谱 $E$ 都定义广义约化同调与上同调理论.
]

#proofsketch[
  $Sigma^oo$ 与 $E smash (-)$ 保持余极限, 所以得到第一条正合序列. 映射谱把源变量中的余纤维序列变成纤维序列, 所以得到第二条. 同理, 同调将楔和送到直和, 上同调将楔和送到积. 悬挂同构则直接来自谱中的移位.
]

#example(title: "先算球面, 再用胞腔粘合")[
  对 $d>=0$, 由 $Sigma^oo S^d tilde.eq SS[d]$, 立刻得到
  $ tilde(E)_n (S^d) tilde.eq pi_(n-d) E, quad tilde(E)^n (S^d) tilde.eq pi_(d-n) E $
  取 $E=H A$, 两式都在 $n=d$ 时为 $A$, 其他次数为零. 更一般地,
  $ (H A)_n (x) tilde.eq H_n (x;A), quad (H A)^n (x) tilde.eq H^n (x;A) $
  这正是普通同调与上同调的谱表示. 参见 @May99[第 22 章, 第 1--2 节; 第 25 章, 第 6 节].

  计算一个由胞腔搭成的空间时, 每接上一批胞腔, 就得到一个余纤维序列. 先使用球面的公式, 再沿长正合序列逐步计算. 例如, 对 $r$ 个圆周的楔和,
  $ tilde(H)^1 (wedge_(i=1)^r S^1;A) tilde.eq A^r $
]

#example(title: "系数正合序列变成谱态射")[
  对素数 $p$, 从系数的短正合序列出发,
  $ 0->ZZ stretch(->)^p ZZ->ZZ slash p ZZ->0 $
  得到谱的正合序列
  $ H ZZ stretch(->)^p H ZZ -> H(ZZ slash p ZZ) stretch(->)^beta (H ZZ)[1] $
  这一点也可由同伦群检查: 乘 $p$ 的余纤维只有零次同伦群 $ZZ slash p ZZ$.

  对它应用 $underline(Map)_(Sp) (Sigma^oo_+ x,-)$ 并取同伦群, 就得到熟悉的系数长正合序列. 其中 *Bockstein 同态*
  $ beta:H^n (x;ZZ slash p ZZ)->H^(n+1) (x;ZZ) $
  就是与同一个谱态射 $beta$ 的移位复合. 因而谱态射能把所有空间、所有次数上的自然上同调运算统一起来.
]

== 谱与Abel群

普通代数在Abel群上添加乘法, 得到环. 谱论也沿着这条路走: 先把谱当作承载加法的对象, 再用砸积添加乘法. 可以先记住这张对应表:

#table(
  columns: (1fr, 1fr),
  table.header([普通代数], [稳定同伦论]),
  [Abel群 $A in Ab$], [谱 $E in Sp$],
  [$Hom_(Ab) (A,B)$], [映射谱 $underline(Map)_(Sp) (E,F)$],
  [张量积 $⊗_ZZ$, 单位 $ZZ$], [砸积 $smash$, 单位 $SS$],
)

这个类比还有一个精确的落点: *Abel群组成谱的标准心*. "心"依赖于所选的 $t$-结构, 我们先把这两个概念说清楚.

=== $t$-结构: 按次数把对象切开

#definition(title: [$t$-结构])[
  设 $C$ 是稳定无穷范畴. 一个 *$t$-结构*由两个对等价封闭的满子范畴 $C_(>=0),C_(<=0)$ 组成. 记
  $ C_(>=n):=C_(>=0)[n], quad C_(<=n):=C_(<=0)[n] $
  要求:
  - *移位:* $C_(>=0)[1] subset.eq C_(>=0)$, $C_(<=0)[-1] subset.eq C_(<=0)$.
  - *正交:* 若 $x in C_(>=0)$, $y in C_(<=-1)$, 则 $Map_C (x,y) tilde.eq *$.
  - *截断:* 每个 $z in C$ 都有正合序列
    $ x->z->y, quad x in C_(>=0), quad y in C_(<=-1) $

  我们采用*同调编号*: $[1]$ 把次数提高一格. 参见 @Lur17[定义 1.2.1.1, 定义 1.2.1.4].
] <def-t-structure>

可以把 $C_(>=0)$ 理解为"没有负次数信息", 把 $C_(<=-1)$ 理解为"只有负次数信息". 正交性说, 从前一种对象映到后一种对象, 只有零态射及可缩的同伦数据. 截断则把任意对象按这个分界切成两部分.

这些分解自动是函子性的. 对每个整数 $n$, 有*截断函子*与自然正合序列
$ tau_(>=n) z -> z -> tau_(<=n-1) z $
其中 $tau_(>=n)$ 是包含 $C_(>=n)->C$ 的右伴随, $tau_(<=n)$ 是包含 $C_(<=n)->C$ 的左伴随. 换句话说, 从高次数对象映入 $z$, 可以先经过 $tau_(>=n) z$; 从 $z$ 映向低次数对象, 可以先经过相应的低次截断. 参见 @Lur17[命题 1.2.1.5, 记号 1.2.1.7].

#definition(title: "心 / Heart")[
  带有 $t$-结构的稳定无穷范畴 $C$ 的*心*定义为
  $ C^suit.heart:=C_(>=0) ∩ C_(<=0) $
  它由同时没有正、负次数信息的对象组成. 对任意 $z in C$, 定义取值于心的*同伦对象*
  $ pi_n^t (z):=tau_(<=0) tau_(>=0) (z[-n]) in C^suit.heart $
  上标 $t$ 用来强调这是心中的对象. 参见 @Lur17[定义 1.2.1.11].
] <def-heart>

#proposition(title: "心是普通Abel范畴")[
  $C^suit.heart$ 的映射生象都是离散的, 因而它等价于一个普通范畴的神经. 这个普通范畴是*Abel范畴*. 以后直接把 $C^suit.heart$ 当作Abel范畴使用.

  对心中的态射 $f:x->y$, 核与余核由下式计算:
  $ op("ker")_(C^suit.heart) (f) tilde.eq pi_0^t (fib(f)), quad coker_(C^suit.heart) (f) tilde.eq pi_0^t (cofib(f)) $
  心中的短正合序列对应 $C$ 中三项都在心内的正合序列. 一般正合序列则在取各次 $pi_n^t$ 后给出心中的长正合序列. 参见 @Lur17[第 1.2.1 节, 尤其注 1.2.1.12].
]

离散性可以直接看出来: 若 $x,y$ 都在心中, 则对 $i>0$, 正交性给出
$ pi_i Map_C (x,y) tilde.eq Hom_("h"C) (x[i],y)=0 $
Abel性是 $t$-结构的基本定理, 这里略去证明. 注意核与余核的公式中要*再取零次*: 纤维或余纤维本身可能带有其他次数的信息.

=== 谱的标准心就是 $Ab$

#proposition(title: "谱的标准截断与标准心")[
  谱范畴有标准 $t$-结构
  $ Sp_(>=0)=brace.l E:pi_i E=0 quad (i<0) brace.r $
  $ Sp_(<=0)=brace.l E:pi_i E=0 quad (i>0) brace.r $
  属于 $Sp_(>=0)$ 的谱称为*连通谱* (connective). 标准截断保留指定范围的同伦群:
  $ pi_i (tau_(<=n) E)=cases(pi_i E & quad i<=n, 0 & quad i>n), quad pi_i (tau_(>=n) E)=cases(0 & quad i<n, pi_i E & quad i>=n) $
  特别地, 心由只有零次同伦群可能非零的谱组成, 并有互逆等价
  $ H:Ab ->^~ Sp^suit.heart, quad pi_0:Sp^suit.heart ->^~ Ab $
  因而心中的每个谱都等价于某个 $H A$. 参见 @Lur17[命题 1.4.3.6].
] <prop-spectrum-heart>

#proofsketch[
  标准 $t$-结构及截断的存在使用上引命题. 若 $E$ 只有 $pi_0 E=A$ 非零, 则其 $Omega$-谱的第 $n$ 层只有第 $n$ 个同伦群 $A$, 所以恢复为 $H A$. 同时
  $ Map_(Sp) (H A,H B) tilde.eq Hom_(Ab) (A,B) $
  右边视为离散生象. 因而这不仅对应对象, 也对应所有态射.
]

在这个等价下, 一般定义的同伦对象就是 $pi_n^t (E) tilde.eq H(pi_n E)$. 所以熟悉的谱同伦群, 正是取值于标准心的同伦对象所对应的Abel群.

这里"连通谱"只要求负次同伦群为零, 不要求 $Omega^oo E$ 连通: 例如 $H A$ 是连通谱, 但它的第零层是离散群 $A$. 此外, "心中的谱"也常称为*离散谱*; 这是关于标准 $t$-结构的说法, 不是说它在整个 $Sp$ 中是零截断对象.

#example(title: "取心后才得到普通核")[
  考虑乘二映射 $f:H ZZ->H ZZ$. 在心中, 它的核为零, 余核为 $H(ZZ slash 2 ZZ)$. 但在谱中,
  $ cofib(f) tilde.eq H(ZZ slash 2 ZZ), quad fib(f) tilde.eq H(ZZ slash 2 ZZ)[-1] $
  纤维还在第 $-1$ 次保留了信息. 取 $pi_0^t$ 后, 才得到心中的零核. 这也说明心通常不是稳定子范畴: 对它的对象移位, 一般会离开心.
]

截断还给出 *Postnikov 塔*. 它逐次加入同伦群, 每一层之间有正合序列
$ H(pi_n E)[n] -> tau_(<=n) E -> tau_(<=n-1) E $
而且谱可以由整座塔恢复:
$ E tilde.eq lim_(n->oo) tau_(<=n) E $
这个收敛性称为标准 $t$-结构的*左完备性*. 每一层的材料是心中对象的移位, 层与层怎样连接也是数据; 因此不能一般地把 $E$ 写成这些移位的直和. 参见 @Lur17[命题 1.4.3.6].

=== 砸积怎样对应普通张量积

连通谱的砸积仍然连通, 且对 $E,F in Sp_(>=0)$ 有
$ pi_0 (E smash F) tilde.eq pi_0 E ⊗_ZZ pi_0 F $
于是心上有诱导的张量积
$ x ⊗^suit.heart y:=tau_(<=0) (x smash y), quad x,y in Sp^suit.heart $
在 @prop-spectrum-heart 的等价下, 它正好对应Abel群的普通张量积:
$ tau_(<=0) ((H A) smash (H B)) tilde.eq H(A ⊗_ZZ B) $
心中的张量单位是 $H ZZ tilde.eq tau_(<=0) SS$. 参见 @Lur17[命题 7.1.3.15, 注 7.1.3.16, 取底环为球谱].

这就是类比的精确范围: 取零次以后, 砸积恢复普通张量积; 砸积本身还可能含有高次信息. 接下来把普通环的"Abel群加上乘法"搬到整个 $Sp$ 中.

== $EE_1$ 与 $EE_oo$ 环谱

普通含幺结合环可以看成 $(Ab,⊗_ZZ,ZZ)$ 中的结合代数对象, 普通交换环则是其中的交换代数对象. 对谱, 我们使用 $(Sp,smash,SS)$, 并让代数公理包含全部相容同伦. 以下的环与环谱都含幺, 态射保持单位.

=== 为什么要用算筹记录乘法

在一个谱 $A$ 上, 首先需要乘法和单位
$ mu:A smash A->A, quad eta:SS->A $
例如结合律比较 $mu compose (mu smash id)$ 与 $mu compose (id smash mu)$. 在无穷范畴中, 要指定它们之间的同伦; 对四个输入, 不同的结合路径之间还要指定相容同伦, 然后继续到所有阶. *算筹* (operad) 就是把这些多输入运算与相容规则组织起来的语言.

#definition(title: "算筹作用的含义")[
  这里使用单色的无穷算筹: 它为每个 $r>=0$ 给出一个 $r$ 输入运算的生象 $O(r)$, 并带有代入、输入置换与恒等运算, 以及它们的全部相容性.

  对谱 $A$, 其*自同态算筹*的运算生象为
  $ op("End")_A (r):=Map_(Sp) (A^(smash r),A), quad A^(smash 0):=SS $
  代入由复合与砸积给出. 一个 $O$-代数结构就是无穷算筹态射 $O->op("End")_A$: 它将每种抽象运算实现为 $A$ 上的运算, 并保持全部相容数据. 参见 @Lur17[第 2.1.1--2.1.3 节].
]

我们只需要两种算筹:
- *$EE_1$:* 可以用一个区间里 $r$ 个互不相交、带标号的小区间来表示运算. 代入就是在小区间里再放小区间. $EE_1 (r)$ 有 $r!$ 个可缩分支, 对应输入的不同排列; 在一个分支内, 输入顺序保持不变. 它编码带全部相容同伦的结合乘法.
- *$EE_oo$:* 可以用无穷维小立方体算筹来建模. 每个运算生象 $EE_oo (r)$ 可缩, 输入置换群的作用在这个模型中是自由的. 它也记录交换输入及交换过程之间的全部相容性, 因而编码带全部相容同伦的交换乘法.

几何上, 一维中互不相交的小区间不能穿过彼此来交换顺序; 不断增加维度以后, 交换和它的高阶相容性都能容纳. 这里保留空输入运算 $r=0$, 用来指定单位. 参见 @Lur17[第 5.1 节, 尤其例 5.1.0.7、推论 5.1.1.5].

=== 环谱的定义

#definition(title: [$EE_1$ 与 $EE_oo$ 环谱])[
  一个 *$EE_1$ 环谱*是 $(Sp,smash,SS)$ 中的 $EE_1$-代数对象, 也称*结合环谱*. 它们组成无穷范畴
  $ Alg_(EE_1) (Sp) tilde.eq Alg(Sp) $
  一个 *$EE_oo$ 环谱*是其中的 $EE_oo$-代数对象, 也称*交换环谱*. 它们组成无穷范畴
  $ Alg_(EE_oo) (Sp) tilde.eq CAlg(Sp) $
  环谱态射保持运算及其相容同伦. 忘掉部分结构, 有自然函子
  $ CAlg(Sp)->Alg(Sp)->Sp $
  参见 @Lur17[定义 7.1.0.1, 注 7.1.0.2--7.1.0.4].
] <def-ring-spectra>

这里乘法之外的加法已经包含在谱的稳定结构中, 砸积则承担双线性运算的角色. $EE_1$ 不要求乘法交换; $EE_oo$ 同时包含交换性和它的高阶相容性. 只在同伦范畴中写下结合、交换等式, 尚未给出这里要求的结构.

=== 从环谱读出普通代数

#proposition(title: "同伦群上的乘法")[
  若 $A$ 是 $EE_1$ 环谱, 则乘法诱导
  $ pi_p A ⊗_ZZ pi_q A -> pi_(p+q) A $
  从而 $pi_* A$ 成为含幺分次结合环. 特别地, $pi_0 A$ 是普通结合环, 每个 $pi_n A$ 都是它的双模.

  若 $A$ 是 $EE_oo$ 环谱, 则 $pi_* A$ 分次交换: 对齐次元素 $a in pi_p A$, $b in pi_q A$,
  $ a b=(-1)^(p q) b a $
  因而 $pi_0 A$ 是交换环, 各个 $pi_n A$ 是其普通模.
] <prop-ring-spectrum-homotopy>

#proofsketch[
  把元素写成谱态射 $a:SS[p]->A$, $b:SS[q]->A$, 乘积就是复合
  $ SS[p+q] tilde.eq SS[p] smash SS[q] stretch(->)^(a smash b) A smash A stretch(->)^mu A $
  结合律与单位从环谱结构传下来. 交换两个移位球谱的因子会产生度数 $(-1)^(p q)$, 因而交换环谱给出上述符号规则.
]

#proposition(title: "离散环谱恢复普通环")[
  若环谱 $A$ 的底层谱在 $Sp^suit.heart$ 中, 称它为*离散环谱*. 取零次同伦环给出等价
  $ Alg(Sp)^"disc" tilde.eq Ring, quad CAlg(Sp)^"disc" tilde.eq CRing $
  逆函子把普通环 $R$ 送到 $H R$. 因而普通结合环自然给出 $EE_1$ 环谱, 普通交换环自然给出 $EE_oo$ 环谱. 这些等价也包含态射; 在离散环谱之间, 映射生象就是普通环同态的离散集合. 参见 @Lur17[注 7.1.0.3, 命题 7.1.3.18].
] <prop-discrete-ring-spectra>

所以, 环谱并没有把普通环排除在外: 普通环正好是没有其他同伦次数的那一层. 对一般环谱, $pi_* A$ 则只是可以读出的代数数据, 并不包含全部高阶乘法信息.

=== 连通与非连通: 信息从哪一层开始

#definition(title: "连通谱与非连通谱")[
  回顾 @prop-spectrum-heart, 谱 $E$ 称为*连通* (connective), 若
  $ pi_i E=0 quad (i<0) $
  若某个负次同伦群非零, 则称它为*非连通谱* (nonconnective). 环谱的连通性指其*底层谱*的连通性, 与选择 $EE_1$ 还是 $EE_oo$ 乘法无关. 例如球谱 $SS$ 与普通环给出的 $H R$ 都连通, 但 $SS$ 并不离散.

  连通性只限制负次数; 正次同伦群仍然可以很丰富. 离散则要求除零次外全部为零. 参见 @Lur17[命题 1.4.3.6, 第 7.1.3 节].
] <def-connective-nonconnective-spectra>

最容易的例子来自移位. 取非零普通环 $R$, 由 $pi_i (E[n]) tilde.eq pi_(i-n) E$ 得到下表; 表中未列出的同伦群全部为零.

#table(
  columns: (1fr, 1.5fr, 1.5fr),
  table.header([谱], [唯一非零的同伦群], [连通性]),
  [$H R$], [$pi_0=R$], [连通且离散],
  [$H R[1]$], [$pi_1=R$], [连通, 不离散],
  [$H R[-1]$], [$pi_(-1)=R$], [非连通],
)

这里移位的是底层谱, 并没有给移位后的对象指定含幺环谱结构. 直观上, $[1]$ 把信息向高次数移动, $[-1]$ 则向低次数移动. 因此连通谱对悬挂封闭, 对取环路却未必封闭. 非连通也不意味着负次数无界: $H R[-1]$ 只有一个非零次数.

#remark(title: "负次同伦怎样看见")[
  这里的"连通"是*次数条件*. 例如 $H R$ 连通, 但 $Omega^oo H R$ 是离散生象 $R$, 通常有很多连通分支.

  第零层 $Omega^oo E$ 只能看到非负次同伦群:
  $ pi_i (Omega^oo E) tilde.eq pi_i E quad (i>=0) $
  因而 $Omega^oo (H R[-1]) tilde.eq *$, 尽管 $H R[-1]$ 不是零谱. 要看负次信息, 就把谱移位后再看第零层:
  $ pi_0 (Omega^oo (E[q])) tilde.eq pi_(-q) E quad (q>0) $
  在 $Omega$-谱的描述中, $Omega^oo (E[q])$ 正是第 $q$ 层. 所以负次同伦仍由普通生象记录, 只是需要看后面的层; 这也是为什么不能只用第零层代替整个谱.
]

对连通环谱, 可以先从普通环 $pi_0 A$ 开始, 再逐层记录 $pi_1 A,pi_2 A,dots$ 及它们之间的相容数据. 一般环谱还允许零次以下的信息. 后面会看到, *正次上同调恰好记录在谱的负次数中*, 因而计算上同调时会自然遇到非连通谱.

=== 截断、等价与基本构造

#proposition(title: "环谱的连通覆盖与 Postnikov 截断")[
  设 $A$ 为 $EE_1$ 或 $EE_oo$ 环谱.
  - 连通覆盖 $tau_(>=0) A->A$ 自然保留同一种环谱结构.
  - 若 $A$ 连通, 则对 $n>=0$, 截断 $A->tau_(<=n) A$ 也保留同一种环谱结构. 特别有环谱态射
    $ A -> H(pi_0 A) $
  - 对连通环谱, Postnikov 塔在环谱范畴中收敛:
    $ A tilde.eq lim_(n->oo) tau_(<=n) A $

  参见 @Lur17[命题 7.1.3.13, 命题 7.1.3.15, 命题 7.1.3.19].
]

第二条中的连通性是条件的一部分. 对任意环谱, 总有的是
$ A <- tau_(>=0) A -> H(pi_0 A) $
因此, 研究连通环谱时可以先看普通环 $pi_0 A$, 再逐层加入更高同伦群及乘法的相容数据.

#proposition(title: "等价、极限与余极限")[
  对 $EE_1$ 环谱和 $EE_oo$ 环谱, 都有以下性质:
  - 一个环谱态射是等价, 当且仅当它在每个 $pi_n$ 上都是同构.
  - 它们的无穷范畴可呈示, 因而具有所有小极限与小余极限.
  - 极限与滤过余极限可以在底层谱上计算, 并自然带上环谱结构.

  参见 @Lur17[第 3.2.2--3.2.3 节].
]

一般余极限还要顾及乘法. 例如在 $CAlg(Sp)$ 中, 两个对象的余积是带自然交换乘法的 $A smash B$; 在 $Alg(Sp)$ 中, 余积则是结合代数意义下的自由积. 两者都不应直接按底层谱的直和来计算. 参见 @Lur17[第 3.2.4 节].

=== 几个可以直接使用的例子

#example(title: "球谱是环谱中的整数")[
  砸积的单位 $SS$ 自然是 $EE_oo$ 环谱. 它在 $Alg(Sp)$ 和 $CAlg(Sp)$ 中都是始对象: 对每个环谱 $A$, 单位给出唯一到可缩选择的环谱态射
  $ SS->A $
  这对应普通代数中 $ZZ->R$ 的角色. 特别地, 连通截断给出自然的交换环谱态射
  $ SS->H ZZ $
]

#example(title: "复合产生结合环谱")[
  对任意谱 $e$, 定义自同态谱
  $ underline(End)(e):=underline(Map)_(Sp) (e,e) $
  复合给出乘法, 恒等映射给出单位, 从而它自然是 $EE_1$ 环谱. 例如取 $e=H ZZ ⊕ H ZZ$, 有
  $ pi_0 underline(End)(e) tilde.eq op("M")_2 (ZZ) $
  这里是通常的二阶矩阵环. 它不交换, 所以这套复合乘法不能成为 $EE_oo$ 乘法. 这说明 $EE_1$ 与 $EE_oo$ 的区别在最普通的线性代数里就能看见.
]

#example(title: "上同调谱的杯积")[
  设 $A$ 是 $EE_oo$ 环谱, $x$ 是生象. 非约化上同调谱
  $ C^* (x;A):=underline(Map)_(Sp) (Sigma^oo_+ x,A) $
  自然也是 $EE_oo$ 环谱. 一个简短的说明是: 把 $x$ 看作无穷群胚, 有
  $ Sigma^oo_+ x tilde.eq colim_x SS, quad C^* (x;A) tilde.eq lim_x A $
  右边是常值图式 $A$ 的极限, 可以直接在交换环谱中计算. 直观上, 对角映射 $x->x times x$ 让我们在同一个点取多个值, 再用 $A$ 的乘法将它们相乘.

  具体地, 对角映射诱导
  $ d:Sigma^oo_+ x -> (Sigma^oo_+ x) smash (Sigma^oo_+ x) $
  若 $a in A^p (x)$, $b in A^q (x)$ 分别由映射 $a:Sigma^oo_+ x->A[p]$, $b:Sigma^oo_+ x->A[q]$ 表示, 记移位后的乘法为 $mu_(p,q):A[p] smash A[q]->A[p+q]$, 则杯积由复合给出
  $ a ∪ b:=mu_(p,q) compose (a smash b) compose d:Sigma^oo_+ x->A[p+q] $
  因而有 $a ∪ b in A^(p+q) (x)$, 并满足
  $ a ∪ b=(-1)^(p q) b ∪ a $
  取 $A=H R$, $R$ 为普通交换环, 就恢复普通上同调的杯积. 若 $A$ 只有 $EE_1$ 结构, 同样得到结合的杯积, 但不再保证交换性.
]

#example(title: "上同调自然给出非连通环谱")[
  取非零普通交换环 $R$. 上例的 $C^* (x;H R)$ 满足
  $ pi_(-q) C^* (x;H R) tilde.eq H^q (x;R) $
  因而只要 $x$ 有非零的正次上同调, 这个交换环谱就非连通. 例如圆周 $S^1$ 给出
  $ pi_0 C^* (S^1;H R) tilde.eq R, quad pi_(-1) C^* (S^1;H R) tilde.eq R $
  其他次数全为零. 第 $-1$ 次记录的正是圆周的 $H^1$. 所以即使系数环谱 $H R$ 离散, 取上同调后也会出现负次同伦; 后面定义整体截面谱 $Gamma$ 时, 使用的也是这个次数约定.
]

最后, 虽然底层的 $Sp$ 稳定, 环谱范畴本身并不稳定: 它的始对象是 $SS$, 终对象是零环谱, 两者不等价. 固定一个环谱以后, 对它的模再做线性代数, 才会重新进入稳定环境; 这正是下一节要介绍的内容.

== 环谱的模

普通模是带有环作用的 Abel群. 把 Abel群换成谱, 把张量积换成砸积, 并保留公理中的相容同伦, 就得到环谱的模. 本节只介绍最常用的构造.

=== 模与自由模

#definition(title: "环谱的模")[
  设 $A$ 是 $EE_1$ 环谱. 一个*左 $A$-模*是谱 $m$ 连同作用
  $ alpha:A smash m->m $
  它满足单位律与结合律, 并带有全部高阶相容同伦. 换句话说, 普通公式 $(a b)x=a(b x)$ 在这里是一整套相容数据. 模态射是保持这些数据的谱态射.

  本节将左模组成的无穷范畴简记为 $Mod_A$. *右 $A$-模*则使用作用 $m smash A->m$. 对一般 $EE_1$ 环谱, 要区分左右; 当 $A$ 是 $EE_oo$ 环谱时, 左右模范畴典范等价, 统一称为 $A$-模. 参见 @Lur17[定义 7.1.1.2, 记号 7.1.1.1].
] <def-ring-spectrum-modules>

最直接的例子是 $A$ 自己, 作用就是乘法. 更一般地, 对谱 $e$, *自由 $A$-模*为 $A smash e$. 若 $U:Mod_A->Sp$ 是忘却函子, 则
$ Map_(Mod_A) (A smash e,m) tilde.eq Map_(Sp) (e,U(m)) $
这正是自由模的熟悉性质: 指定生成元的像, 就指定了模映射. 取 $e=SS$ 得到自由模 $A$; 取若干个球谱的直和, 就得到相应的 $A$ 的直和. 特别地,
$ Mod_(SS) tilde.eq Sp $
球谱的作用就是砸积的单位约束. 参见 @Lur17[第 4.2.4 节].

=== 稳定性与普通模论

#proposition(title: "固定系数以后仍然稳定")[
  对任意 $EE_1$ 环谱 $A$, $Mod_A$ 是可呈示的稳定无穷范畴. 极限与余极限都可以在底层谱上计算, 并自然带上 $A$-作用. 因而移位、纤维和余纤维仍是 $A$-模; 模态射是等价当且仅当它诱导所有同伦群的同构. 参见 @Lur17[第 4.2.3 节, 推论 7.1.1.5].
] <prop-module-spectra-stable>

例如, 模态射的余纤维序列 $m->n->q$ 给出同伦群的长正合列. 作用还使 $pi_* m$ 成为分次环 $pi_* A$ 上的分次模, 特别使每个 $pi_i m$ 成为普通左 $pi_0 A$-模.

由 @def-mapping-spectrum, 模之间也有 *$A$-线性映射谱*
$ underline(Map)_A (m,n):=underline(Map)_(Mod_A) (m,n) $
$ pi_i underline(Map)_A (m,n) tilde.eq Hom_("h"Mod_A) (m[i],n) $
这里要求映射保持 $A$-作用, 因而一般不同于底层谱之间的映射谱.

#proposition(title: "模范畴的心")[
  若 $A$ *连通*, 则由底层谱的同伦群定义
  $ (Mod_A)_(>=0):={m:pi_i m=0 " 对所有 " i<0}, quad (Mod_A)_(<=0):={m:pi_i m=0 " 对所有 " i>0} $
  得到标准 $t$-结构, 且取 $pi_0$ 给出等价
  $ (Mod_A)^suit.heart tilde.eq Mod_(pi_0 A)^"ord" $
  右边表示普通左 $pi_0 A$-模范畴. 逆向地, 普通模 $v$ 给出 $H v$, 沿 $A->H(pi_0 A)$ 获得 $A$-作用. 参见 @Lur17[命题 7.1.1.13].
] <prop-module-spectra-heart>

#example(title: "普通复形已经是环谱模的例子")[
  对普通交换环 $R$, 有无穷范畴的等价
  $ Mod_(H R) tilde.eq Dcat(R) $
  右边是前面定义的无界导出无穷范畴. 因此 $H R$-模可以用 $R$-模复形来计算, 拟同构被视为等价. 按本章的上同调次数约定, 对应的 $m$ 与复形 $v^bullet$ 满足
  $ pi_i m tilde.eq H^(-i) (v^bullet) $
  普通模对应集中在零次的复形. 对普通 $R$-模 $u,v$ 和 $q>=0$, 更有
  $ pi_(-q) underline(Map)_(H R) (H u,H v) tilde.eq Ext_R^q (u,v) $
  所以 $Hom$ 与高阶扩张都装在同一个映射谱里. 参见 @Lur17[定理 7.1.2.13, 注 7.1.1.12].
]

=== 相对张量积

#definition(title: "在环谱上做张量积")[
  设 $A$ 是 $EE_1$ 环谱, $m$ 是右 $A$-模, $n$ 是左 $A$-模. 它们的*相对张量积*定义为双边 bar 构造的几何实现:
  $ m ⊗_A n:=colim_([q] in Delta^op) (m smash A^(smash q) smash n) $
  这里 $Delta$ 是单纯形范畴. 面映射使用 $A$ 的乘法与两端的模作用, 退化映射插入单位. 直观上, 这个构造实行关系 $(x a)⊗y=x⊗(a y)$, 同时保留关系之间的相容同伦. 参见 @Lur17[第 4.4 节].
] <def-relative-tensor-spectra>

对一般结合环谱, 上式得到一个谱, 输入需要一右一左. 若 $A$ 是 *$EE_oo$ 环谱*, 结果自然仍是 $A$-模, 并给出对称幺半结构
$ (Mod_A,⊗_A,A) $
相对张量积分别保持余极限, 因而分别保持余纤维序列; 单位律为 $A⊗_A m tilde.eq m$. 参见 @Lur17[第 4.5 节].

#example(title: "张量积里的高阶信息就是 Tor")[
  对普通交换环 $R$ 及普通 $R$-模 $u,v$, 上面的等价将 $⊗_(H R)$ 对应到导出张量积 $⊗_R^L$. 因而
  $ pi_i (H u ⊗_(H R) H v) tilde.eq Tor_i^R (u,v), quad i>=0 $
  零次恢复普通张量积. 例如, 对素数 $p$, 由自由分解 $0->ZZ stretch(->)^p ZZ->ZZ slash p ZZ->0$ 可得
  $ pi_i (H(ZZ slash p ZZ) ⊗_(H ZZ) H(ZZ slash p ZZ)) tilde.eq cases(ZZ slash p ZZ & quad i=0 " 或 " i=1, 0 & quad "其他次数") $
  因为这个两项自由复形与 $ZZ slash p ZZ$ 张量后, 微分变成了零, 所以两项都留下了同调. 这里的张量积是在 $H ZZ$ 上取的; 底环本身也是运算的一部分. 参见 @Lur17[定理 7.1.2.13].
]

=== 换系数

给定 $EE_1$ 环谱态射 $A->B$, 一个 $B$-模可以沿它看作 $A$-模, 称为*限制标量*. 反方向用*扩张标量*
$ B⊗_A -:Mod_A->Mod_B $
这里 $B$ 用左乘保留 $B$-作用, 用 $A->B$ 获得右 $A$-作用. 两个构造互为伴随:
$ Map_(Mod_B) (B⊗_A m,n) tilde.eq Map_(Mod_A) (m,op("Res") n) $
这就是把系数从 $A$ 换成 $B$ 的自然方式. 对普通环的 Eilenberg--MacLane 环谱, 它恢复导出的扩张标量. 参见 @Lur17[命题 4.6.2.17].

== 多项式环谱与局部化

有了模与相对张量积, 就可以用泛性质描述加变量和取逆这两个基本构造.

=== 多项式环谱

以下固定交换环谱 $R$, 不要求连通. 记 $CAlg_R:=CAlg(Sp)_(R \/)$, 其对象是交换环谱 $A$ 连同 $R->A$. 对交换 $R$-代数, $A⊗_R B$ 表示推出 $A coprod_R B$; 它的底层模正是上一节介绍的相对张量积.

#definition(title: "多项式环谱的泛性质")[
  *一元多项式环谱* $R[t]$ 是由一个零次生成元自由生成的交换 $R$-代数, 即对每个 $A in CAlg_R$ 有自然等价
  $ Map_(CAlg_R) (R[t],A) tilde.eq Map_(Mod_R) (R,A) tilde.eq Omega^oo A $
  生成元 $t$ 对应恒等映射 $id_(R[t])$. 因而给出 $R[t]->A$, 就是选定 $A$ 中一个元素, 连同元素之间的全部同伦. 特别地,
  $ pi_0 Map_(CAlg_R) (R[t],A) tilde.eq pi_0 A $
  第一式比这个同伦类的等式保留了更多信息.

  更一般地, 忘却函子 $CAlg_R->Mod_R$ 有左伴随 $op("Sym")_R$, 称为*自由交换代数*或*对称代数*, 满足
  $ Map_(CAlg_R) (op("Sym")_R (M),A) tilde.eq Map_(Mod_R) (M,A) $
  所以 $R[t]:=op("Sym")_R (R)$; 多元情形定义为 $R[t_1,dots,t_n]:=op("Sym")_R (R^(⊕n))$. 参见 @Lur17[例 3.1.3.14], @Lur11DAG7[记号 2.12].
] <def-polynomial-ring-spectrum>

#proposition(title: "加变量与换系数")[
  多项式环谱有熟悉的性质:
  - 给出 $R[t_1,dots,t_n]->A$, 等于选择 $n$ 个元素: 映射生象为 $(Omega^oo A)^n$.
  - 加入两组变量可以分步进行:
    $ R[t_1,dots,t_n]⊗_R R[u_1,dots,u_m] tilde.eq R[t_1,dots,t_n,u_1,dots,u_m] $
  - 沿任意交换环谱态射 $R->B$ 换系数, 有
    $ B⊗_R R[t_1,dots,t_n] tilde.eq B[t_1,dots,t_n] $
  - 若 $R$ 连通, 则 $R[t_1,dots,t_n]$ 也连通, 且
    $ pi_0 (R[t_1,dots,t_n]) tilde.eq (pi_0 R)[t_1,dots,t_n] $
] <prop-polynomial-ring-spectrum>

#proofsketch[
  前三条都只需向任意目标 $A$ 取映射生象: 两边描述同样的元素选择. 最后一条由自由交换代数的构造与连通性得到; 取 $pi_0$ 后, 恢复普通交换代数的自由构造. 参见 @Lur17[第 3.1.3 节, 命题 7.1.3.15].
]

#remark(title: "这里的多项式仍有高阶信息")[
  本节的 $R[t]$ 始终按上面的*自由 $EE_oo$ 泛性质*定义; 文献中也常记为 $R\{t\}$. 它一般不同于由离散加法幺半群 $NN$ 构造的幺半群环谱 $R smash Sigma^oo_+ NN$.

  差别来自对称性也要保留同伦. 具体地, 在底层 $R$-模中,
  $ op("Sym")_R (M) tilde.eq ⊕_(n>=0) (M^(⊗_R n))_(h Sigma_n), quad R[t] tilde.eq ⊕_(n>=0) (R smash Sigma^oo_+ B Sigma_n) $
  其中 $Sigma_n$ 是置换 $n$ 个输入的对称群, $(-)_(h Sigma_n)$ 表示对群作用取余极限, 即*同伦轨道*; $n=0$ 项为 $R$. 参见 @Lur17[构造 3.1.3.9, 例 3.1.3.14].

  因而对普通交换环 $K$, $(H K)[t]$ 一般不能直接写成 $H(K[t])$. 例如 $K=bb(F)_2$ 时, $n=2$ 项的第一同伦群是 $H_1 (B Sigma_2;bb(F)_2) tilde.eq bb(F)_2$, 已经产生了高次信息. 对 $QQ$-代数 $K$, 有限群的正次同调消失, 才有 $(H K)[t] tilde.eq H(K[t])$.
]

=== 局部化

#definition(title: "使一个元素可逆")[
  设 $f in pi_0 R$. *局部化* $R[f^(-1)]$ 是一个交换 $R$-代数, 其中 $f$ 的像可逆, 并且对每个交换 $R$-代数 $A$, 有
  $ Map_(CAlg_R) (R[f^(-1)],A) tilde.eq cases(* & quad "若 " f " 在 " pi_0 A " 中可逆", emptyset & quad "否则") $
  也就是说, 它是使 $f$ 可逆的交换 $R$-代数中的始对象. 这里的"唯一"是*延拓的整个生象可缩*, 因而同时包括全部相容同伦.

  等价地, 对任意交换环谱 $A$, 预合成给出
  $ Map_(CAlg(Sp)) (R[f^(-1)],A) -> Map_(CAlg(Sp)) (R,A) $
  它把左边等价地识别为右边中那些使 $f$ 可逆的连通分支. 局部化存在, 并由此泛性质唯一确定到可缩选择. 参见 @Lur11DAG7[定义 2.8, 注 2.9].
] <def-spectral-localization>

#proposition(title: "局部化怎样计算")[
  局部化逐次作用于同伦群:
  $ pi_i (R[f^(-1)]) tilde.eq (pi_i R)[f^(-1)] quad (i in ZZ) $
  因而它保持连通性与离散性. 特别地, 对普通交换环 $K$ 及 $f in K$,
  $ (H K)[f^(-1)] tilde.eq H(K[f^(-1)]) $
  若 $f$ 已可逆, 则 $R[f^(-1)] tilde.eq R$; 若 $f$ 幂零, 则 $R[f^(-1)] tilde.eq 0$.

  对 $R$-模 $M$, 记 $M[f^(-1)]:=R[f^(-1)]⊗_R M$. 在 $Mod_R$ 中有
  $ M[f^(-1)] tilde.eq colim(M stretch(->)^f M stretch(->)^f M stretch(->)^f dots), quad pi_i (M[f^(-1)]) tilde.eq (pi_i M)[f^(-1)] $
  所以局部化可以直观地想成不断允许再除以一次 $f$. 限制标量将 $Mod_(R[f^(-1)])$ 等价地识别为 $Mod_R$ 中那些乘 $f$ 为等价的模组成的满子范畴.
] <prop-spectral-localization-computation>

#proofsketch[
  在模的上述余极限中, 乘 $f$ 成为等价, 且它对这一性质是泛的. 谱的同伦群保持滤过余极限, 所以每次同伦群都变成普通模的局部化. 取 $M=R$ 得到环谱的公式; 交换环谱结构与泛性质由局部化定理保证. 参见 @Lur17[第 7.2.3 节], @Lur11DAG7[注 2.9].
]

#proposition(title: "所有单元素局部化来自同一个推出方块")[
  记 $SS[t,t^(-1)]:=(SS[t])[t^(-1)]$. 选取 $f in pi_0 R$ 的一个代表, 多项式的泛性质给出 $SS[t]->R$, 将 $t$ 送到 $f$. 则下图是 $CAlg(Sp)$ 中的推出方块:

  #align(center)[
    #book-diagram(
      spacing: 40pt, cell-size: 0pt, node-inset: 5pt,
      {
        fletcher.edge((0, 0), (1, 0), marks: "->")
        fletcher.edge((0, 0), (0, 1), marks: "->")
        fletcher.edge((1, 0), (1, 1), marks: "->")
        fletcher.edge((0, 1), (1, 1), marks: "->")
        fletcher.node((0, 0), $SS[t]$)
        fletcher.node((1, 0), $SS[t,t^(-1)]$)
        fletcher.node((0, 1), $R$)
        fletcher.node((1, 1), $R[f^(-1)]$)
      },
    )
  ]

  因而
  $ R[f^(-1)] tilde.eq R⊗_(SS[t]) SS[t,t^(-1)] $
  上边先把通用变量 $t$ 变成可逆元素, 再将 $t$ 代成 $f$, 就得到 $R$ 中的局部化. 参见 @Lur11DAG7[注 2.13].
] <prop-localization-polynomial-pushout>

#proof[
  对任意交换 $R$-代数 $A$, 从推出对象映到 $A$, 等于把 $SS[t]->R->A$ 延拓到 $SS[t,t^(-1)]$. 由局部化的泛性质, 当 $f$ 的像可逆时, 延拓生象可缩; 否则为空. 这正是 $R[f^(-1)]$ 的泛性质.
]

同理, 任意换系数 $R->B$ 都有 $B⊗_R R[f^(-1)] tilde.eq B[f_B^(-1)]$, 其中 $f_B$ 是 $f$ 的像. 连续局部化则满足
$ (R[f^(-1)])[g^(-1)] tilde.eq R[f^(-1),g^(-1)] tilde.eq R[(f g)^(-1)] $
这里 $f,g in pi_0 R$: 在交换环中, $f g$ 可逆等价于二者都可逆. 特别地, $R[f^(-1)]⊗_R R[f^(-1)] tilde.eq R[f^(-1)]$.

记 *Laurent 多项式环谱* $R[t,t^(-1)]:=(R[t])[t^(-1)]$. 多项式选择一个任意元素, Laurent 多项式则选择一个可逆元素:
$ Map_(CAlg_R) (R[t,t^(-1)],A) tilde.eq (Omega^oo A)^times $
右边是 $Omega^oo A$ 中对应 $(pi_0 A)^times$ 的连通分支. 后面从点函子看, $R[t]$ 因而给出仿射直线, 而 $R[t,t^(-1)]$ 给出其中的乘法群. 在普通零次环上, 局部化对应主开集 $D(f) subset.eq Spec(pi_0 R)$; 各个 $pi_i R$ 都在同一主开集上局部化. 这正是下一章用局部化定义局部自由模的依据.
