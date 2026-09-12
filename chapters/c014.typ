#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *

#show: doc => conf(easy: true, doc,)

= 群概形 / Group Schemes <chap-group-schemes>

先在普通概形中讨论群对象, 再把仿射情形接到 #chapter-ref(<chap-hopf-algebras>) 的 Hopf 代数上. 本章的张量积取普通张量积.

== 群概形与 Hopf 代数

#definition(title: [群概形])[
  设 $S$ 是概形. 一个 *$S$-群概形*是 $Sch_(\/ S)$ 中的群对象, 即一个 $S$-概形 $G$, 配备 $S$-态射
  $ m:G times_S G->G, quad e:S->G, quad i:G->G $
  分别表示乘法, 单位与取逆, 并满足结合律, 单位律与逆元律.

  等价地, 对每个 $S$-概形 $T$, 集合
  $ G(T):=Hom_S (T,G) $
  自然地成为群, 且沿 $T'->T$ 的拉回是群同态. 群概形态射是保持群结构的 $S$-态射, 也就是在所有 $T$-点上给出群同态的态射.
] <def-group-scheme>

#definition(title: [仿射群概形])[
  若结构态射 $G->S$ 仿射, 则称 $G$ 为*仿射群概形*. 特别地, 对任意普通交换环 $R$ 及 $S=Spec R$, 它可以写成
  $ G=Spec H, quad H=Gamma(G,cal(O)_G) $
  其中 $H$ 是交换 $R$-代数, 称为 $G$ 的*坐标环*.
] <def-affine-group-scheme>

#theorem(title: [仿射群概形与 Hopf 代数])[
  仿射 $R$-群概形与交换 $R$-Hopf 代数反变等价:
  $ cat("AffGrp")_R tilde.eq (cat("Hopf")_R^"comm")^opp $
  两个方向分别为 $G mapsto Gamma(G,cal(O)_G)$ 与 $H mapsto Spec H$.

  对 $G=Spec H$, 群结构对应于
  $ Delta=m^*:H->H times.o_R H, quad
    epsilon=e^*:H->R, quad S_H=i^*:H->H $
  群概形态射 $f:G->G'$ 对应反方向的 Hopf 代数态射 $f^*:H'->H$.
] <thm-affine-group-hopf>

#proof[
  $Spec$ 给出交换 $R$-代数与仿射 $R$-概形的反变等价, 并且
  $ Spec(H times.o_R H) tilde.eq Spec H times_(Spec R) Spec H $
  所以乘法, 单位与取逆分别变成 $Delta,epsilon,S_H$. 群的结合律与单位律变成余结合律与余单位律; 逆元律变成
  $ mu_H compose (S_H times.o id) compose Delta
    =eta_H compose epsilon
    =mu_H compose (id times.o S_H) compose Delta $
  这正是对极恒等式. 各结构映射都是概形态射, 因而其拉回是代数态射, 给出双代数相容性. 反过来对这些映射取 $Spec$, 就恢复群结构. 同样的对应也保持态射, 因而得到范畴等价. 参见 @MilALA[第一部分, 第 5--6 节].
]

这里 $H$ 的乘法是正则函数的乘法, 群乘法对应的是余乘法 $Delta$. 因而 $H$ 总是交换代数, 而 $G$ 是交换群概形当且仅当 $Delta$ 余交换.

在点上, 这一对应就是卷积. 对交换 $R$-代数 $B$,
$ G(B)=Hom_(Alg_R) (H,B), quad
  phi star psi=mu_B compose (phi times.o psi) compose Delta $
单位为 $eta_B compose epsilon$, $phi$ 的逆为 $phi compose S_H$. 这也直接把 Hopf 结构读成了群运算.

#example(title: [加法群与乘法群])[
  *加法群* $bb(G)_a=Spec R[t]$ 的结构为
  $ Delta(t)=t times.o 1+1 times.o t, quad epsilon(t)=0, quad S_H (t)=-t $
  所以 $bb(G)_a (B)=(B,+)$.

  *乘法群* $bb(G)_m=Spec R[t,t^(-1)]$ 的结构为
  $ Delta(t)=t times.o t, quad epsilon(t)=1, quad S_H (t)=t^(-1) $
  所以 $bb(G)_m (B)=B^times$. 两个例子都适用于任意底环 $R$.
]

== 子群与核

下面固定底概形 $S$. 核可以直接用纤维积构造, 子群也能在所有测试概形的点上识别. 像和商需要再用到层化.

=== 子群与正规子群

#definition(title: [子群概形])[
  一个群概形态射 $j:H->G$ 若是单态, 就称它给出一个*子群概形*, 记作 $H subset.eq G$. 等价地, 对每个 $T->S$, 映射 $H(T)->G(T)$ 单射, 因而将 $H(T)$ 识别为子群.

  若 $j$ 是闭浸入或开浸入, 分别称 $H$ 为*闭子群概形*或*开子群概形*. 对一个给定的闭子概形 $H subset.eq G$, 只需检查单位, 取逆及乘法 $H times_S H->G$ 都经过 $H$, 就得到闭子群结构.

  若共轭态射
  $ G times_S H->G, quad (g,h) mapsto g h g^(-1) $
  经过 $H$, 则称 $H$ *正规*, 记作 $H ⊴ G$. 等价地, 对所有 $T->S$, 都有 $H(T) ⊴ G(T)$.
] <def-subgroup-scheme>

这里的单态是范畴意义下的单态, 必须在所有 $T$-点上单射. 只检查域上的点会丢掉无穷小信息. 闭子群的判据见 @Stacks26[Tag 022R].

#proposition(title: [闭子群与 Hopf 理想])[
  设 $G=Spec A$ 是仿射 $R$-群概形. 闭子群 $H=Spec(A \/ I)$ 对应于满足下列条件的理想 $I subset A$:
  $ epsilon_A (I)=0, quad S_A (I) subset.eq I, quad
    (pi times.o pi) Delta_A (I)=0 $
  其中 $pi:A->A \/ I$ 是商映射. 这样的理想称为*Hopf 理想*.
]

#proof[
  三个条件分别保证余单位, 对极与余乘法下降到 $A \/ I$. Hopf 恒等式随商映射下降, 所以 $A \/ I$ 成为交换 Hopf 代数, 给出闭子群. 反过来, 闭子群的坐标环是 Hopf 代数商, 其核必满足这些条件.
]

Hopf 理想描述闭子群, 不自动保证子群正规. 例如 $GL_2$ 的上三角子群是闭子群, 但共轭可把它变成下三角子群.

#proposition(title: [子群的拉回与交])[
  对群概形态射 $f:G->Q$ 与子群 $H subset.eq Q$, 原像
  $ f^(-1)(H):=G times_Q H $
  是 $G$ 的子群. 两个子群的交由
  $ H_1 inter H_2:=H_1 times_G H_2 $
  表示. 闭子群的原像与有限交仍闭, 正规性也被这些运算保持. 这些构造均与任意底变换相容.
]

#proof[
  纤维积在 $T$-点上分别给出普通群的原像与交, 因而有唯一的群结构. 单态与闭浸入对底变换稳定, 正规性可在每个 $T$-点上检查. 纤维积与底变换交换, 给出最后的断言.
]

特别地, 仿射闭子群由 $I_1,I_2 subset A$ 定义时,
$ H_1 inter H_2=Spec(A \/ (I_1+I_2)) $
这里保留整个商环, 不对理想取根.

=== 核的纤维积

#definition(title: [群概形态射的核])[
  对 $f:G->Q$, 沿单位截面 $e_Q:S->Q$ 取纤维积, 定义
  $ ker(f):=G times_(Q,e_Q) S $
  它在 $T$-点上满足
  $ ker(f)(T)={g in G(T) | f(g)=e_Q (T)} $
] <def-group-scheme-kernel>

#align(center, diagram(edge-stroke: .65pt + black, spacing: 2em, $
  ker(f) edge("hook->") edge("d", ->) & G edge("d", f, ->) \
  S edge(e_Q, ->) & Q
$))

#proposition(title: [核的基本性质])[
  $ker(f)$ 是 $G$ 的正规子群. 若 $Q->S$ 分离, 则它是闭子群. 对任意 $S'->S$,
  $ ker(f) times_S S' tilde.eq ker(f_(S')) $
  此外, $f$ 是单态当且仅当 $ker(f)$ 是平凡群概形 $S$.
]

#proof[
  在每个 $T$-点上, 核是普通群同态的正规子群. 若 $Q->S$ 分离, 单位截面 $e_Q$ 是闭浸入, 其底变换 $ker(f)->G$ 也闭. 核与底变换的相容性来自纤维积. 最后, 群同态单射当且仅当核平凡, 再用 Yoneda 引理即可.
]

#proposition(title: [仿射核的方程])[
  设 $G=Spec A$, $Q=Spec B$, $f$ 对应 $phi:B->A$. 记 $B^+=ker(epsilon_B\:B->R)$ 为增广理想. 则
  $ cal(O)(ker(f))=A times.o_B R
    tilde.eq A \/ (A dot phi(B^+)) $
  其中 $R$ 通过 $epsilon_B$ 成为 $B$-代数.
]

#proof[
  仿射纤维积对应张量积. 因为 $R tilde.eq B \/ B^+$, 右正合性给出
  $ A times.o_B (B \/ B^+) tilde.eq A \/ (A dot phi(B^+)) $
  这个计算不需要平坦性假设.
]

=== 核的典型例子

#example(title: [行列式与单位根])[
  对整数 $n>=1$, 一般线性群由
  $ GL_n=Spec R[x_(i j),det(x_(i j))^(-1)] $
  表示, 其 $B$-点为可逆矩阵. 行列式的核是
  $ SL_n=ker(det\:GL_n->bb(G)_m)
    =Spec(R[x_(i j)] \/ (det(x_(i j))-1)) $
  因而 $SL_n$ 是闭正规子群.

  对整数 $n>=1$, 幂映射 $[n]:bb(G)_m->bb(G)_m$, $u mapsto u^n$ 的核为
  $ mu_n=Spec(R[t,t^(-1)] \/ (t^n-1)), quad
    mu_n (B)={u in B^times | u^n=1} $
  它在 $R$ 上有限局部自由, 秩为 $n$.
]

#example(title: [Frobenius 的无穷小核])[
  设 $k$ 是特征 $p>0$ 的域. 群同态
  $ op("Frob"):bb(G)_a->bb(G)_a, quad x mapsto x^p $
  的核是
  $ alpha_p=Spec(k[t] \/ (t^p)), quad
    alpha_p (B)={b in B | b^p=0} $
  对每个扩域 $K \/ k$, 都有 $alpha_p (K)={0}$. 但在 $B=k[epsilon] \/ (epsilon^2)$ 中, $epsilon$ 给出非零的 $alpha_p$-点. 所以 $alpha_p$ 是非平凡群概形, 即使它的所有域值点都是单位.
]

== 商与 fppf 层

群概形的商首先是一个层. 这允许一个商点只在覆盖后具有代表元, 再把这些局部代表元粘合起来.

=== 商层的定义

在 $S$ 上的 fppf 拓扑中, 覆盖是一族平坦且局部有限表示的态射 $T_i->T$, 其像合起来覆盖 $T$. 概形的点函子都是这个拓扑上的层. 记 $a_"fppf"$ 为集合值预层的 fppf 层化.

#definition(title: [子群的商层])[
  对子群概形 $H subset.eq G$, 定义右平移轨道组成的预层
  $ T mapsto G(T) \/ H(T) $
  并取其层化
  $ G \/ H:=a_"fppf" (T mapsto G(T) \/ H(T)) $
  称为 *fppf 商层*. 记商映射为 $q:G->G \/ H$. 若这个层由概形表示, 就称它为商概形, 并沿用记号 $G \/ H$.
] <def-fppf-group-quotient>

一个 $G \/ H$ 的 $T$-点可以局部写成 $g_i H$, 其中 $g_i in G(T_i)$. 在重叠部分, 它们相差一个 $H$-元素. 因而 $G(T) \/ H(T)->(G \/ H)(T)$ 总是单射, 却未必满射.

#proposition(title: [商的泛性质])[
  若 $F$ 是 fppf 层, 则从 $G \/ H$ 到 $F$ 的态射, 等价于满足
  $ u(g h)=u(g) $
  的态射 $u:G->F$. 换言之, $q$ 是右平移作用与投影
  $ G times_S H ⇉ G $
  在 fppf 层范畴中的余等化子, 其中两条箭头为 $(g,h) mapsto g h$ 与 $(g,h) mapsto g$.
]

#proof[
  在每个 $T$ 上, 不变映射唯一地经过陪集集合. 这些映射随 $T$ 自然, 因而给出陪集预层到 $F$ 的态射. 因 $F$ 已是层, 层化的泛性质再把它唯一地延拓到 $G \/ H$. 反方向与 $q$ 复合即可. 参见 @Stacks26[Tag 02VE].
]

#proposition(title: [正规子群的商群])[
  若 $N ⊴ G$, 则 $G \/ N$ 自然是群层, 且 $q:G->G \/ N$ 是群层同态. 它满足群范畴中的商泛性质, 并且
  $ ker(q)=N $
  若 $G \/ N$ 由概形表示, 则这个概形唯一地成为群概形, 使 $q$ 为群概形同态.
]

#proof[
  正规性使 $G(T) \/ N(T)$ 成为群, 层化保留有限积, 所以群运算下降到商层. 一个 $g in G(T)$ 在商层中为单位, 当且仅当它 fppf 局部属于 $N$; 由于 $N$ 是子层, 这等价于 $g in N(T)$. 商的泛性质由上一命题得到. 若商可表, Yoneda 引理将这些运算变成概形态射.
]

一般子群的商仍带有 $G$ 的左平移作用, 但只有在正规时, 商映射才可成为群同态.

=== 商映射与挠子

#proposition(title: [陪集关系与挠子])[
  对任意子群 $H subset.eq G$, 有 fppf 层的自然同构
  $ G times_S H stretch(->)^~ G times_(G \/ H) G, quad
    (g,h) mapsto (g,g h) $
  且 $q:G->G \/ H$ fppf 局部有截面. 因而它是一个 $H$-挠子: 每个纤维局部都是 $H$, 但没有指定的单位点.

  如果 $H->S$ 平坦且局部有限表示, 且 $G \/ H$ 可表, 那么 $q$ 满射, 平坦且局部有限表示.

  商层也与任意底变换 $S'->S$ 相容:
  $ (G \/ H) times_S S' tilde.eq G_(S') \/ H_(S') $
] <prop-group-quotient-torsor>

#proof[
  两个局部代表元 $g,g'$ 的商点相同, 当且仅当 $g^(-1)g'$ 局部属于 $H$. 因为 $H$ 是子层, 这个条件直接给出唯一的 $h=g^(-1)g' in H$. 这就是所写同构的逆.

  商层的每个点局部来自 $G$, 所以局部截面存在. 选定一个截面 $g$, 映射 $h mapsto g h$ 就将相应底变换识别为 $H$ 的平凡挠子. 平坦性与局部有限表示性由这个局部模型下降, 满射性由局部截面得到.

  对 $T->S'$, 两边的局部代表元及其等价关系相同, 因而给出同一个 fppf 层. 这证明底变换公式.
]

#example(title: [商点未必有全局代表元])[
  幂映射给出 fppf 群层的正合列
  $ 1->mu_n->bb(G)_m stretch(->)^([n]) bb(G)_m->1 $
  确实, 对 $b in B^times$, 环
  $ B'=B[u] \/ (u^n-b) $
  是秩 $n$ 的有限自由忠实平坦 $B$-代数, 且 $u$ 可逆. 在这个 fppf 覆盖上, $b$ 就有了 $n$ 次根. 因而
  $ bb(G)_m \/ mu_n tilde.eq bb(G)_m $
  但取 $B=RR$, $n=2$, 商预层的值是 $RR^times \/ {plus.minus 1}$, 到商层值 $RR^times$ 的映射由平方给出, 不包含 $-1$.
]

=== 何时能得到商概形

#theorem(title: [商的常用可表性结论])[
  设 $H subset.eq G$ 是子群概形.

  - 若 $H->S$ 平坦且局部有限表示, 则 $G \/ H$ 是代数空间, $G->G \/ H$ 是 fppf $H$-挠子.
  - 若 $G->S$ 仿射, $H$ 是有限局部自由的闭子群, 则 $G \/ H$ 由概形表示, $G \/ H->S$ 仿射, 且 $G->G \/ H$ 有限局部自由.
  - 若 $S=Spec k$, $G$ 是有限型仿射 $k$-群概形, $H$ 是闭子群, 则 $G \/ H$ 是有限型概形. 若 $H$ 正规, 则 $G \/ H$ 还是仿射群概形.
] <thm-group-quotient-representability>

#proof[
  第一条使用平坦且局部有限表示的自由作用商定理, 见 @Stacks26[Tag 06PH]. 对这里的右平移作用, 自由性来自 $g h=g$ 蕴含 $h=e$. 对应关系由 $G times_S H$ 表示, 两个投影都平坦且局部有限表示, 因而定理适用; 挠子性质也由 @prop-group-quotient-torsor 给出.

  第二条可先在 $S$ 的仿射开集上应用有限局部自由等价关系的仿射商定理, 见 @Stacks26[Tag 03BE, 命题 39.23.9], 再由商的泛性质粘合. 这里 $G times_S H$ 到 $G$ 的两个投影均有限局部自由, 且到 $G times_S G$ 的映射为单态, 正好满足其条件.

  第三条使用域上代数群的商存在定理, 以及正规子群商的仿射性, 见 @Mil17AG[定理 5.28, 命题 5.29]. 这些是可表性定理的输入; 商的群结构仍由前面的层论泛性质得到.
]

这些结论只在第三条要求底是域. 第一条一般先得到代数空间, 不能仅凭正规性就在任意底概形上断言商是仿射概形.

#proposition(title: [仿射商的坐标环])[
  设 $G=Spec A$, $H=Spec C$ 为闭子群, 对应 $pi:A->C$. 右平移给出余作用
  $ rho=(id_A times.o pi) compose Delta_A:A->A times.o_R C $
  若 $Q=G \/ H$ 是仿射概形且 $q:G->Q$ 忠实平坦, 则
  $ cal(O)(Q) tilde.eq A^H:={a in A | rho(a)=a times.o 1} $
]

#proof[
  忠实平坦下降将 $cal(O)(Q)$ 识别为两个拉回 $A ⇉ cal(O)(G times_Q G)$ 的等化子. 根据 @prop-group-quotient-torsor, $G times_Q G tilde.eq G times_S H$. 两个拉回分别为 $a mapsto a times.o 1$ 与 $rho$, 因而等化子正是 $A^H$.
]

#example(title: [非正规的射影商])[
  在任意普通环 $R$ 上, 令 $B subset GL_2$ 为可逆上三角矩阵组成的闭子群. 它是标准直线 $R e_1 subset R^2$ 的稳定子. 映射
  $ GL_2->bb(P)^1_R, quad g mapsto g(R e_1) $
  给出
  $ GL_2 \/ B tilde.eq bb(P)^1_R $
  因为一条局部直和的线丛可局部选取生成元并补成基, 所以该映射 Zariski 局部有提升; 两个提升相差唯一的右乘 $B$-元素. 由商层的泛性质得到同构.

  取 $R=k$ 为域, 这个商是射影直线, 并非仿射概形. 它的整体函数只有 $k$, 所以直接取不变函数环的 $Spec$ 只得到一点, 无法恢复这个商. $B$ 不正规, 因而这个商也不带使商映射成为同态的群结构.
]

== 像与同构定理

对 $f:G->Q$, 点集的像, fppf 层的像和概形论的像是三个不同层面的构造. 前者只记录能直接提升的点, 第二个允许局部提升, 第三个则用闭子概形的方程定义.

=== fppf 像与第一同构定理

#definition(title: [fppf 像])[
  群概形态射 $f:G->Q$ 的 *fppf 像*定义为群层
  $ op("im")_"fppf" (f):=a_"fppf" (T mapsto im(G(T)->Q(T))) $
  它是 $Q$ 的子群层. 具体地, $y in Q(T)$ 属于这个像, 当且仅当存在 fppf 覆盖 $T_i->T$ 及 $g_i in G(T_i)$, 使
  $ f(g_i)=y|_(T_i) $
  若这个子层等于 $Q$, 就称 $f$ 在 fppf 层意义下满射.
] <def-fppf-group-image>

例如满射, 平坦且局部有限表示的群概形态射一定是这样的满射: 对 $T->Q$, 直接沿 $G times_Q T->T$ 提升即可.

#theorem(title: [第一同构定理])[
  对任意群概形态射 $f:G->Q$, 令 $N=ker(f)$. 则有 fppf 群层的自然同构
  $ G \/ N tilde.eq op("im")_"fppf" (f) $
  因而若 $f$ 在 fppf 层意义下满射, 则 $G \/ N tilde.eq Q$. 这时商已经由群概形 $Q$ 表示.
] <thm-fppf-first-isomorphism>

#proof[
  对每个 $T$, 普通群的第一同构定理给出
  $ G(T) \/ N(T) tilde.eq im(G(T)->Q(T)) $
  这些同构随 $T$ 自然. 两边同时作 fppf 层化, 就得到所需同构. 像层到 $Q$ 单射, 因为层化保持单态.
]

#definition(title: [群概形的正合列])[
  写
  $ 1->N->G stretch(->)^q Q->1 $
  在 fppf 意义下正合, 是指 $N tilde.eq ker(q)$, 且 $q$ 在 fppf 层意义下满射. 最后的满射允许在覆盖后提升, 并不要求 $G(T)->Q(T)$ 对每个 $T$ 都满射.
]

对这样的正合列, $G(T) \/ N(T)$ 在 $Q(T)$ 中的像, 恰好是纤维挠子 $G times_Q T->T$ 有截面的那些点. 选定截面就能把纤维识别为 $N_T$, 所以全局提升是否存在正是挠子是否平凡的问题.

例如行列式有截面 $u mapsto op("diag")(u,1,dots,1)$, 因而在任意底环上
$ 1->SL_n->GL_n stretch(->)^det bb(G)_m->1, quad
  GL_n \/ SL_n tilde.eq bb(G)_m $
这里每个测试概形上的行列式映射也满射. 幂映射的例子则说明, 一般正合列没有这个额外性质.

=== 概形论的像

#definition(title: [概形论的像])[
  $f:G->Q$ 的*概形论像* $op("im")_"sch" (f)$ 是使 $f$ 经过它的最小闭子概形. 对仿射态射
  $ f:Spec A->Spec B, quad phi=f^*:B->A $
  有
  $ op("im")_"sch" (f)=Spec(B \/ ker(phi)) $
] <def-schematic-group-image>

确实, $f$ 经过 $Spec(B \/ J)$ 当且仅当 $J subset.eq ker(phi)$, 所以最大的可用理想就是 $ker(phi)$. 一般定义及其存在性见 @Stacks26[Tag 01R5]. 对群概形, 概形论像与层像的比较还涉及群结构和忠实平坦性.

#theorem(title: [域上的像分解])[
  设 $k$ 为域, $G,Q$ 是有限型仿射 $k$-群概形, $f:G->Q$ 是同态. 则 $I=op("im")_"sch" (f)$ 是闭子群, 并有分解
  $ G stretch(->)^p I stretch(arrow.r.hook)^j Q $
  其中 $p$ 忠实平坦且有限表示, $j$ 为闭浸入. 因而
  $ G \/ ker(f) tilde.eq op("im")_"fppf" (f) tilde.eq I $
  这里右侧两种像作为 fppf 层一致. 此分解与任意扩域 $k' \/ k$ 相容.
] <thm-group-scheme-image-factorization>

#proof[
  写 $G=Spec A$, $Q=Spec B$, $phi:B->A$, 并令 $C=im(phi)$. 因为底环是域, 单射 $C->A$ 张量自身后仍单射. 对 $b in ker(phi)$,
  $ (phi times.o phi) Delta_B (b)=Delta_A (phi(b))=0 $
  所以 $Delta_B$ 下降到 $C->C times.o_k C$. 余单位与对极也下降, 故 $C$ 是 $A$ 的 Hopf 子代数, $I=Spec C$ 是 $Q$ 的闭子群.

  此处使用 Hopf 代数的忠实平坦性定理: 域上有限生成交换 Hopf 代数的包含 $C subset.eq A$ 使 $A$ 成为忠实平坦 $C$-代数, 见 @Mil17AG[定理 3.31]. 两个代数均有限生成, 且 $C$ Noetherian, 所以 $A$ 在 $C$ 上有限表示. 因而 $p:Spec A->Spec C$ 是 fppf 覆盖.

  $j$ 为单态, 所以 $ker(p)=ker(f)$. @thm-fppf-first-isomorphism 给出所写商同构. 扩域是平坦的, 与 $phi$ 的核和像交换, 因而这个分解也与扩域相容. 这就是 @Mil17AG[定理 3.34] 的像分解.
]

#corollary[
  域上有限型仿射群概形的同态若核平凡, 则它是闭浸入.
]

#proof[
  在上述分解中, $p$ 核平凡, 因而是单态; 它又在 fppf 层意义下满射. 局部提升由单射性唯一地粘合, 故 $p$ 是同构. 所以 $f$ 就是闭浸入 $j$.
]

#example(title: [一般底环上的两种像])[
  在 $ZZ$ 上取加法群同态 $[p]:bb(G)_a->bb(G)_a$, 其中 $p$ 为素数. 坐标环映射
  $ ZZ[t]->ZZ[x], quad t mapsto p x $
  单射, 所以概形论像是整个 $bb(G)_a$. 但对 $T=Spec bb(F)_p$, 映射在任何 fppf 覆盖后仍是零映射, 因而点 $1$ 不属于 fppf 像. 这两种像并不相同.

  它的核是 $Spec(ZZ[x] \/ (p x))$, 在 $ZZ$ 上不平坦. 底变换到 $bb(F)_p$ 后, 原映射变成零映射, 其概形论像只剩单位截面; 原来的整个概形论像却变成 $bb(G)_(a,bb(F)_p)$. 因而概形论像也不与任意底变换交换.
]

即使在域上, 拓扑空间的满射也不能代替 fppf 满射. 例如特征 $p$ 下的单位截面 $Spec k->alpha_p$ 在底层拓扑空间上满射, 但它无法在覆盖后提升 $alpha_p (k[epsilon] \/ (epsilon^2))$ 中的非零点.

=== 商与子群的对应

#theorem(title: [子群对应定理])[
  设 $q:G->Q$ 是满射, 平坦且局部有限表示的群概形态射, $N=ker(q)$. 则
  $ J mapsto q^(-1)(J), quad H mapsto H \/ N $
  给出 $Q$ 的闭子群与 $G$ 中包含 $N$ 的闭子群之间的对应. 它保留包含关系与正规性, 并有
  $ q^(-1)(J) \/ N tilde.eq J $
  特别地, 对 $N subset.eq H ⊴ G$,
  $ (G \/ N) \/ (H \/ N) tilde.eq G \/ H $
  最后一式总是在 fppf 群层中成立.
]

#proof[
  对闭子群 $J subset.eq Q$, 其原像 $H$ 是闭子群, 且 $H->J$ 是 $q$ 的底变换, 所以是 fppf 满射, 核为 $N$. 第一同构定理给出 $H \/ N tilde.eq J$.

  反过来, 设 $H subset.eq G$ 闭且包含 $N$. 商层 $H \/ N$ 是 $Q=G \/ N$ 的子层, 将它沿 $q$ 拉回恰好得到 $H$. 因而闭浸入 $H->G$ 带有忠实平坦下降数据, 下降为一个闭浸入 $J->Q$, 且 $J$ 表示 $H \/ N$. 群运算随之下降, 给出闭子群.

  包含关系直接由原像和商保持. 正规性可以在 $Q$ 的点局部提升到 $G$ 后检查, 所以也被这个对应保持. 最后一式由商泛性质得到: 两边都使恰好所有 $H$-元素成为单位, 并且对具有这一性质的群层同态是泛的.
]

#corollary(title: [第二同构定理])[
  对 $H subset.eq G$ 与 $N ⊴ G$, 在 fppf 群层中记 $H N$ 为局部能写成 $h n$ 的元素组成的子群层. 则
  $ H \/ (H inter N) tilde.eq (H N) \/ N $
]

#proof[
  第一同构定理的同一层论证明也适用于 $H->G \/ N$. 核是 $H inter N$, 像是 $(H N) \/ N$, 因而结论成立. 这里的 $H N$ 先作为层定义, 其可表性仍需另行判断.
]

== 群概形的 Lie 代数

群概形的 Lie 代数记录单位元附近的一阶变化, 括号则记录两个无穷小变化不交换的程度. 以下仍允许任意普通底概形 $S$, 不预先假设群概形光滑. 所得括号是 #chapter-ref(<chap-lie-algebras>) 中的普通 Lie 括号, 满足交替性 $[x,x]=0$, 包括特征 $2$ 的情形.

=== 单位元处的切空间

#definition(title: [无穷小单位元])[
  对 $T->S$, 记
  $ T[epsilon]:=Spec_T (cal(O)_T[epsilon] \/ (epsilon^2)) $
  其中 $epsilon$ 表示平方为零的一阶参数. 定义群概形 $G$ 的 *Lie 函子*
  $ op("Lie")(G)(T):=ker(G(T[epsilon])->G(T)) $
  因而一个 Lie 元素是 $T[epsilon]->G$, 其在 $epsilon=0$ 时限制为单位截面. 这里的核先取在普通群中.

  更一般地, 对 $T$ 上的拟凝聚模 $M$, 令
  $ T[M]:=Spec_T (cal(O)_T plus.o M), quad M^2=0 $
  其中 $(a,m)(b,n)=(a b,a n+b m)$. 记
  $ op("Lie")(G)(T,M):=ker(G(T[M])->G(T)) $
  它允许无穷小变化取值于任意模 $M$, 而不只是 $cal(O)_T$.
] <def-group-lie-functor>

当 $S=Spec R$, $T=Spec B$ 时, 简写 $op("Lie")(G)(B)=ker(G(B[epsilon] \/ (epsilon^2))->G(B))$. 乘以标量 $b in B$ 来自环映射 $epsilon mapsto b epsilon$.

#proposition(title: [余切模与切向量])[
  令 $e:S->G$ 为单位截面, 并记
  $ omega_(G\/S):=e^* Omega^1_(G\/S) $
  其中相对微分层 $Omega^1_(G\/S)$ 由相对导子的泛性质定义. 对 $u:T->S$, 有自然同构
  $ op("Lie")(G)(T,M)
    tilde.eq Hom_(cal(O)_T) (u^* omega_(G\/S),M) $
  左侧的群运算在这个同构下就是右侧的加法.

  特别地, 若 $G=Spec A$ 是仿射 $R$-群概形, $epsilon_A:A->R$ 是余单位, $I=ker(epsilon_A)$, 则
  $ omega_(G\/R) tilde.eq I \/ I^2, quad
    op("Lie")(G)(B) tilde.eq Hom_R (I \/ I^2,B) $
  这里在仿射底上将拟凝聚模与对应的模识别.
] <prop-group-lie-cotangent>

#proof[
  先在仿射情形计算. 记 $epsilon_B:A->R->B$ 为单位点. 一个提升 $A->B plus.o M$ 唯一地写成 $a mapsto (epsilon_B (a),d(a))$. 它是代数态射当且仅当
  $ d(a b)=epsilon_B (a)d(b)+epsilon_B (b)d(a), quad d|_R=0 $
  也就是说, $d$ 是沿单位点取值的 $R$-导子. 它在 $I^2$ 上为零, 因而对应于 $I \/ I^2->M$ 的 $R$-线性映射. 反过来, 由此线性映射作用于 $a-eta_A epsilon_A (a)$ 就恢复 $d(a)$.

  将两个提升用群乘法复合, 坐标环上就是卷积. 展开余乘法, 利用 $M^2=0$ 和余单位恒等式, 得到导子的和 $d+d'$. 因而这个无穷小核是交换群, 并自然成为模. 对一般概形, 平方零提升与相对导子的对应在局部作同样计算后粘合, 再用微分层的泛性质即可.
]

因此 Lie 函子由一个仿射 $S$-概形表示:
$ op("Lie")(G)=Spec_S (op("Sym")_(cal(O)_S) (omega_(G\/S))) $
这是单位元处的相对切概形. 它不一定是向量丛. 在 $S$ 的开集上取 Lie 元素, 得到模层
$ frak(g):=underline(op("Hom"))_(cal(O)_S) (omega_(G\/S),cal(O)_S) $
当 $omega_(G\/S)$ 有限局部自由时, $frak(g)=omega_(G\/S)^or$ 也是有限局部自由模, 上述切概形才是其对应的向量丛. 下文在域 $k$ 上也按惯例用 $op("Lie")(G)$ 或 $frak(g)$ 表示向量空间 $op("Lie")(G)(k)$.

=== 左不变导子与 Lie 括号

一阶核的群运算总是交换的, 因而不能直接用这个核内部的群交换子作为 Lie 括号. 要得到括号, 可以把切向量延拓为左不变导子, 再取导子的交换子.

#proposition(title: [切向量的左不变延拓])[
  设 $G=Spec A$ 为仿射 $R$-群概形, $x in op("Lie")(G)(R)$. 将 $x$ 看作沿 $epsilon_A$ 的导子 $A->R$, 定义
  $ D_x:=(id_A times.o x) compose Delta_A:A->A $
  则 $D_x$ 是普通 $R$-导子, 并且*左不变*, 即
  $ Delta_A compose D_x=(id_A times.o D_x) compose Delta_A $
  反过来, 每个左不变导子都唯一地由这个公式得到. 逆映射为 $D mapsto epsilon_A compose D$.
] <prop-group-left-invariant-derivation>

#proof[
  余乘法保持乘法, 而 $x$ 满足沿余单位的 Leibniz 律, 因而
  $ D_x (a b)=a D_x (b)+b D_x (a) $
  左不变等式直接来自 $Delta_A$ 的余结合律. 余单位恒等式给出 $epsilon_A compose D_x=x$. 对任意左不变导子 $D$, 同样有
  $ D=(id_A times.o epsilon_A) compose Delta_A compose D
    =(id_A times.o (epsilon_A compose D)) compose Delta_A $
  所以这两个构造互逆. 域上的叙述见 @Mil17AG[命题 10.28--10.29]; 这里的计算适用于任意交换底环.
]

几何上, $D_x$ 在点 $g$ 处的取值是把单位处的 $x$ 用左乘 $L_g$ 推过去. 等价地, 无穷小右平移 $g mapsto g x(epsilon)$ 给出一个模 $epsilon$ 为恒等的自同构, 对应导子 $D_x$. 它与所有左平移交换. 这个描述对非仿射群概形也成立, 并将单位切向量与左不变的相对向量场识别.

#theorem(title: [群概形的典范 Lie 括号])[
  左不变导子对交换子封闭. 通过上面的识别, 定义
  $ D_([x,y]):=D_x compose D_y-D_y compose D_x $
  便使 $op("Lie")(G)(T)$ 成为 $Gamma(T,cal(O)_T)$ 上的 Lie 代数, 且随 $T$ 的变化自然. 在仿射底 $R$ 上, 其坐标公式为
  $ [x,y]=epsilon_A compose [D_x,D_y]
    =(x times.o y-y times.o x) compose Delta_A $
  因而 Lie 括号是卷积代数 $Hom_R (A,R)$ 的交换子在单位导子上的限制. 模层 $frak(g)$ 也由此成为 $cal(O)_S$-Lie 代数层.
] <thm-group-lie-bracket>

#proof[
  对导子 $D,E$, 展开 $D(E(a b))-E(D(a b))$, 两个交叉项相消, 故 $[D,E]$ 仍满足 Leibniz 律. 若 $D,E$ 左不变, 则
  $ Delta_A compose [D,E]=(id_A times.o [D,E]) compose Delta_A $
  所以左不变导子形成 $End_R (A)$ 的 Lie 子代数. 结合代数的交换子双线性, 满足 $[D,D]=0$ 和 Jacobi 恒等式, 从而把这些性质传给切向量. 在一般概形上, 对相对导子的层作同样运算即可.

  最后由余结合律和余单位恒等式,
  $ epsilon_A compose D_x compose D_y=(x times.o y) compose Delta_A $
  减去交换 $x,y$ 后的式子, 得到坐标公式. 这个推导也说明整个构造与测试概形的变化相容.
]

#proposition(title: [括号的无穷小交换子解释])[
  取 $x,y in op("Lie")(G)(B)$, 用 $x(t),y(u)$ 表示对应的一阶点. 在
  $ C=B[t,u] \/ (t^2,u^2) $
  上有
  $ x(t)y(u)x(t)^(-1)y(u)^(-1)=[x,y](t u) $
  右边表示将 Lie 元素 $[x,y]$ 的参数代入 $t u$. 所以括号恰好是群交换子的混合二阶项.
]

#proof[
  在坐标环上, $x(t)$ 写成 $epsilon_B+t x$, 其逆为 $epsilon_B-t x$. 对四个映射作卷积并展开, 常数项是 $epsilon_B$, 一次项相消, 剩下
  $ t u (x star y-y star x) $
  这正是 @thm-group-lie-bracket 的公式. 一般情形可以在单位附近进行这个计算, 或用无穷小平移的复合作相同展开. 这里必须保留 $t u$; 若只使用一个满足 $epsilon^2=0$ 的参数, 交换子便只能看到单位.
]

=== 微分与伴随作用

#proposition(title: [群同态的微分])[
  对群概形同态 $f:G->Q$, 复合一阶点得到自然的 Lie 态射
  $ d f_e:op("Lie")(G)->op("Lie")(Q) $
  它也记作 $op("Lie")(f)$, 并满足
  $ d(h compose f)_e=d h_e compose d f_e, quad d(id)_e=id $
  若 $f^*:B->A$ 是对应的 Hopf 代数态射, 则
  $ d f_e (x)=x compose f^* $
  这是 $I_Q \/ I_Q^2->I_G \/ I_G^2$ 的对偶方向.
] <prop-group-lie-differential>

#proof[
  复合保持单位点, 所以先得到无穷小核之间的映射. 它对模加法及标量作用自然. 坐标公式直接来自复合环态射; 因 $f^*$ 保持余乘法, 该公式保持卷积交换子, 因而保持 Lie 括号. 也可以直接对无穷小群交换子应用 $f$. 复合公式与恒等公式随即成立.
]

#definition(title: [伴随作用与表示的微分])[
  共轭 $c_g (h)=g h g^(-1)$ 固定单位元, 因而给出
  $ op("Ad")(g):=d(c_g)_e $
  这是 $G$ 在其 Lie 函子上的典范作用. 若 $omega_(G\/S)$ 有限局部自由, 它给出群概形态射
  $ op("Ad"):G->GL(frak(g)) $
  称为*伴随表示*.

  同样, 对有限局部自由模 $V$ 上的表示 $rho:G->GL(V)$, 取微分得到
  $ d rho_e:frak(g)->underline(op("End"))_(cal(O)_S) (V) $
  即 $frak(g)$ 的表示. 这里 $op("Lie")(GL(V))$ 的括号是自同态的交换子.
] <def-group-adjoint-representation>

#proposition(title: [伴随作用的微分])[
  在上述有限局部自由条件下,
  $ d(op("Ad"))_e=op("ad"), quad op("ad")(x)(y)=[x,y] $
  对任意子群 $H subset.eq G$, $op("Lie")(H)$ 是 $op("Lie")(G)$ 的子 Lie 函子. 若 $H$ 正规, 则其 Lie 代数在 $G$ 的伴随作用下稳定, 并且是 Lie 理想.
]

#proof[
  由无穷小交换子公式, 共轭 $y(u)$ 与原来的 $y(u)$ 之差在混合项上是 $t u[x,y]$. 因而 $op("Ad")(x(t))$ 在 $y$ 上的一阶变化为 $[x,y]$, 正是所写微分.

  子群在所有测试概形的点上单射, 所以在一阶核上也单射; 微分保持括号, 给出子 Lie 结构. 正规性使共轭限制到 $H$, 再对共轭取微分, 就得到伴随稳定性与 $[frak(g),frak(h)] subset.eq frak(h)$. 最后这个结论也可直接由无穷小交换子证明, 不需要有限局部自由假设.
]

例如 $G$ 交换时, 所有共轭都为恒等, 所以 Lie 括号为零. 反过来, 仅凭 Lie 括号为零一般不能恢复整个群的交换性, 因为它只记录单位附近的无穷小信息.

=== 底变换与正合性

#proposition(title: [Lie 函子的底变换])[
  对任意 $v:S'->S$, 有
  $ omega_(G_(S')\/S') tilde.eq v^* omega_(G\/S), quad
    op("Lie")(G_(S')) tilde.eq op("Lie")(G) times_S S' $
  第二个式子是切概形及其 Lie 运算的底变换. 以 $frak(g)'$ 表示从 $G_(S')$ 定义的 Lie 模层, 则模层之间只有自然映射
  $ v^* frak(g)->frak(g)' $
  若 $omega_(G\/S)$ 有限局部自由, 此映射是同构. 特别地, 若 $G->S$ 光滑, 则 $frak(g)$ 是有限局部自由的 Lie 代数层, 且其形成与任意底变换交换.
] <prop-group-lie-base-change>

#proof[
  相对微分层与任意底变换交换, 拉回到单位即得第一个式子. 对称代数与底变换交换, 或者直接用一阶点的定义, 得到切概形的式子. 对偶与拉回之间总有自然映射; 对有限局部自由模, 可以局部选基, 直接验证它是同构. 光滑态射的微分层有限局部自由, 所以适用.
]

#proposition(title: [平移与切丛])[
  写 $pi:G->S$. 左平移给出自然同构
  $ Omega^1_(G\/S) tilde.eq pi^* omega_(G\/S) $
  若 $G->S$ 光滑, 则对偶后有
  $ cal(T)_(G\/S) tilde.eq pi^* frak(g) $
  其中 $cal(T)_(G\/S)$ 是相对切丛. 因而光滑群概形的整个相对切丛, 都由单位处的 Lie 代数通过平移得到.
]

#proof[
  自同构 $tau:G times_S G->G times_S G$, $(g,h) mapsto (g,g h)$ 保持第一投影, 且其逆为 $(g,h) mapsto (g,g^(-1)h)$. 沿第一投影取相对微分, 得到
  $ m^* Omega^1_(G\/S) tilde.eq op("pr")_2^* Omega^1_(G\/S) $
  再沿 $(id_G,e compose pi):G->G times_S G$ 拉回, 就得到第一个同构. 这个论证不需要平坦性. 光滑时微分层有限局部自由, 因而对偶与拉回交换, 得到切丛公式. 参见 @Stacks26[Tag 045W, 引理 39.6.3].
]

#example(title: [Lie 模未必与底变换交换])[
  在 $ZZ$ 上取 $G=mu_p$, $p$ 为素数. 令 $z=t-1$, 则模 $z^2$ 时, 关系 $t^p-1=0$ 变成 $p z=0$. 因而
  $ omega_(mu_p\/ZZ) tilde.eq ZZ \/ p ZZ, quad
    op("Lie")(mu_p)(B)={b in B | p b=0} $
  特别地,
  $ op("Lie")(mu_p)(ZZ)=0, quad
    op("Lie")(mu_(p,bb(F)_p))(bb(F)_p)=bb(F)_p $
  所以不能把后者认作前者与 $bb(F)_p$ 的张量积. 完整 Lie 函子一直保留着这个变化; 切概形在这里是 $Spec(ZZ[z] \/ (p z))$, 不是向量丛.
]

#proposition(title: [核与切空间的正合性])[
  Lie 函子保持有限极限. 特别地, 对群概形同态 $f:G->Q$,
  $ op("Lie")(ker(f)) tilde.eq ker(d f_e) $
  所以正合列 $1->N->G->Q$ 总给出左正合列
  $ 0->op("Lie")(N)->op("Lie")(G)->op("Lie")(Q) $
  如果 $G,Q$ 在 $S$ 上光滑, 且 $q:G->Q$ 光滑, 则 $N=ker(q)$ 也光滑, 并有 Lie 代数模层的短正合列
  $ 0->frak(n)->frak(g) stretch(->)^(d q_e) frak(q)->0 $
] <prop-group-lie-exactness>

#proof[
  对每个 $T$, 点函子保持极限, 取单位纤维也保持极限, 因而得到第一部分. 最后的满射来自光滑态射的无穷小提升性质: 给定 $T[epsilon]->Q$ 及其在 $T$ 上的单位提升 $T->G$, 可以在 $T$ 上局部把整个图提升到 $G$. 这正是 $d q_e$ 作为模层态射满射. 而 $N->S$ 是 $q$ 沿单位截面的底变换, 因而光滑.
]

#example(title: [fppf 满射的微分未必满射])[
  在特征 $p$ 的域 $k$ 上, $op("Frob"):bb(G)_a->bb(G)_a$, $t mapsto t^p$ 是有限忠实平坦态射, 核为 $alpha_p$. 但
  $ (epsilon a)^p=0 $
  所以 $d op("Frob")_e=0$. 相应 Lie 代数列为
  $ 0->k stretch(->)^id k stretch(->)^0 k $
  它在最后一项不满射. 因而不能仅凭群层的短正合列, 就断言 Lie 代数也短正合.
]

#corollary(title: [商空间的单位切空间])[
  设 $G$ 是域 $k$ 上的光滑有限型仿射群概形, $H$ 是光滑闭子群, $Q=G \/ H$. 令 $o=e H in Q(k)$, 则
  $ T_o Q tilde.eq frak(g) \/ frak(h) $
  若 $H$ 正规, 这个同构进一步给出
  $ op("Lie")(G \/ H) tilde.eq frak(g) \/ frak(h) $
  作为 Lie 代数的同构.
]

#proof[
  $G->Q$ 是 $H$-挠子, 因而是光滑满射. 其单位处纤维为 $H$, 相应切空间列为 $0->frak(h)->frak(g)->T_o Q->0$. 若 $H$ 正规, 商映射是群同态, 所以这个向量空间同构还保持括号. 一般 $H$ 不正规时, 这里只是商空间的切空间, 不附带商 Lie 括号.
]

=== 典型计算与光滑性

#example(title: [一般线性群与特殊线性群])[
  在任意交换环 $B$ 上, 单位矩阵附近的一阶点唯一地写成 $1+epsilon X$, $X in M_n (B)$, 其逆为 $1-epsilon X$. 因而
  $ op("Lie")(GL_n)(B)=gl_n (B)=M_n (B) $
  将两个不同的一阶参数保留下来,
  $ (1+t X)(1+u Y)(1-t X)(1-u Y)
    =1+t u(X Y-Y X) $
  所以 $[X,Y]=X Y-Y X$. 这说明抽象构造确实恢复了矩阵 Lie 代数.

  再由
  $ det(1+epsilon X)=1+epsilon op("tr")(X) $
  得到 $d(det)_e=op("tr")$, 以及
  $ op("Lie")(SL_n)(B)=sl_n (B)
    ={X in M_n (B) | op("tr")(X)=0} $
  例如 $sl_2$ 中取 $E=E_(12)$, $F=E_(21)$, $H=op("diag")(1,-1)$, 就有
  $ [H,E]=2E, quad [H,F]=-2F, quad [E,F]=H $
  这些式子对所有底环成立. 在特征 $2$ 下, 前两个括号变成零, 正好显示特征对 Lie 结构的影响.
]

#example(title: [稳定子与保形式群])[
  设 $V$ 是有限局部自由模, $W subset V$ 是局部直和项. 稳定子 $P subset GL(V)$ 的一阶条件为
  $ op("Lie")(P)=\{X in underline(op("End"))(V) | X(W) subset.eq W\} $
  因为 $1+epsilon X$ 保持 $W[epsilon]$ 当且仅当 $X(W) subset.eq W$. 所以可逆上三角群的 Lie 代数是全部上三角矩阵, 幺幂上三角群的 Lie 代数是严格上三角矩阵.

  若固定可逆矩阵 $J$, 由 $g^t J g=J$ 定义保双线性形式的群 $G_J$, 则展开一阶项得到
  $ op("Lie")(G_J)(B)=\{X | X^t J+J X=0\} $
  取 $J=1$ 且 $2$ 可逆, 得到正交群的反对称矩阵 Lie 代数; 取标准非退化交替矩阵, 得到辛群的 Lie 代数. 在特征 $2$ 下, 保二次型与保其极化双线性形式需要分别定义.
]

#example(title: [交换群与无穷小群])[
  加法群的一阶点为 $epsilon a$, 乘法群的一阶点为 $1+epsilon a$. 因而
  $ op("Lie")(bb(G)_a)(B)=B, quad op("Lie")(bb(G)_m)(B)=B $
  两者括号都为零. 更一般地, 秩 $r$ 的分裂环面 $bb(G)_m^r$ 给出交换 Lie 代数 $B^r$; 有限局部自由模 $V$ 的加法群给出 $V$ 自身, 括号为零.

  对单位根群, $(1+epsilon a)^n=1+n epsilon a$, 所以
  $ op("Lie")(mu_n)(B)=\{a in B | n a=0\} $
  若 $n$ 在 $B$ 中可逆, 这个 Lie 代数为零. 在特征 $p$ 的域上,
  $ op("Lie")(alpha_p)=k, quad op("Lie")(mu_p)=k $
  两个零维群概形都有一维的 Lie 代数. 另一方面, 有限 étale 群概形的 Lie 代数为零, 因为 étale 态射的相对微分层为零; 这包括有限常值群概形.

  非仿射的例子是维数 $g$ 的 Abel 簇 $A \/ k$: 它光滑且交换, 所以 $op("Lie")(A)=T_0 A$ 是 $g$ 维交换 Lie 代数.
]

#proposition(title: [Lie 维数检测光滑性])[
  设 $G$ 是域 $k$ 上的有限型群概形. 则
  $ dim_k op("Lie")(G)>=dim G $
  且等号成立当且仅当 $G$ 光滑. 因而零维有限型群概形的 Lie 代数为零当且仅当它 étale.
]

#proof[
  扩域到代数闭包不改变两边维数, 所以可设 $k$ 代数闭. 单位处的切空间维数不小于局部维数, 且相等当且仅当该局部环正则. 左平移将单位送到每个闭点, 因而 $G$ 各处的局部维数相同, 并且在单位处光滑就蕴含处处光滑. 域上有限型概形的光滑性可在扩域后检验, 所以结论也适用于原来的 $k$. 零维情形再使用光滑且相对维数零等价于 étale.
]

=== 正特征结构与泛包络代数

群概形在正特征下还给 Lie 代数额外的运算, 可以区分某些具有相同普通 Lie 括号的群.

#proposition(title: [典范的限制 Lie 结构])[
  设底环 $R$ 的特征为素数 $p$. 对 $x in op("Lie")(G)(R)$, 左不变导子的 $p$ 次复合 $D_x^p$ 仍是左不变导子. 定义
  $ D_(x^([p]))=D_x^p $
  就得到 Lie 代数的典范 *$p$-运算*, 也称限制 Lie 结构. 它继承自导子所在结合代数的 $p$ 次幂, 特别满足
  $ (a x)^([p])=a^p x^([p]), quad
    op("ad")(x^([p]))=op("ad")(x)^p $
  加法相容性由 $(D_x+D_y)^p$ 的展开给出; 对交换的 $x,y$, 有 $(x+y)^([p])=x^([p])+y^([p])$. 群概形同态的微分也保持这个运算.
]

#proof[
  反复使用 Leibniz 律得到
  $ D^p (a b)=sum_(j=0)^p binom(p,j) D^j (a) D^(p-j)(b)
    =D^p (a)b+a D^p (b) $
  因为中间二项式系数在特征 $p$ 下全为零. 左不变性对复合保持, 所以 $D_x^p$ 对应唯一切向量. 标量公式直接来自 $R$-线性, 伴随公式来自结合代数中的恒等式 $[D^p,-]=[D,-]^p$. 加法关系同样从结合代数继承.

  若 $f^*:B->A$ 是 Hopf 代数态射, 则 $D_x compose f^*=f^* compose D_(d f_e (x))$. 将此等式迭代 $p$ 次, 再在单位求值, 就证明微分保持 $p$-运算. 非仿射情形用相对导子的层作相同计算. 参见 @Mil17AG[第 11 章 h 节].
]

#example(title: [相同括号下的不同 $p$-运算])[
  在特征 $p$ 的域上, $bb(G)_a$ 的标准左不变导子为 $partial_t$, 而 $bb(G)_m$ 的标准左不变导子为 $t partial_t$. 它们满足
  $ partial_t^p=0, quad (t partial_t)^p=t partial_t $
  第一式可在单项式上检查, 连续 $p$ 个整数的积被 $p$ 整除; 第二式来自 $m^p=m$ 对整数在特征 $p$ 中的像成立. 因而对标准基元 $x$,
  $ op("Lie")(bb(G)_a): x^([p])=0, quad
    op("Lie")(bb(G)_m): x^([p])=x $
  同样, $alpha_p$ 继承前一种运算, $mu_p$ 继承后一种运算. 它们作为一维普通 Lie 代数相同, 但作为限制 Lie 代数不同. 对 $GL_n$, 这个运算就是矩阵的 $p$ 次幂 $X^([p])=X^p$: 若 $Z$ 为坐标函数组成的矩阵, 则 $D_X (Z)=Z X$, 迭代给出 $D_X^p (Z)=Z X^p$.
]

最后, 左不变导子也把本节接回 #chapter-ref(<chap-lie-algebras>) 的泛包络代数. 对仿射 $R$-群概形 $G=Spec A$, 写 $frak(g)=op("Lie")(G)(R)$. 由 $x mapsto D_x$ 及普通泛包络代数的泛性质, 得到
$ U_R^"cl" (frak(g))->End_R (A) $
其像由左不变的一阶导子及其复合生成, 因而作用为左不变微分算子. 每个群表示 $rho$ 的微分也唯一地延拓为 $U_R^"cl" (frak(g))$ 的模结构. 这里采用普通包络代数, 与一般底环上的导出包络代数作区分.

这个过程通常丢失群的整体信息. 例如特征零域上 $bb(G)_a$ 与 $bb(G)_m$ 都给出一维交换 Lie 代数, 但前者的有限维代数表示微分为幂零算子, 后者的表示按整数权重分解. 对前者, 设表示矩阵为 $A(t)$, 从 $A(t+u)=A(t)A(u)$ 得到 $A'(t)=A(t)N$, 其中 $N=A'(0)$. 比较系数得
$ A(t)=sum_(j>=0) frac(t^j N^j,j!) $
而 $A(t)$ 是多项式, 所以 $N$ 幂零. 对后者, 坐标环的 Laurent 单项式 $t^m$ 给出整数分次的余模, 在权重 $m$ 上微分作用为 $m$. 因而从群表示取微分可以得到 Lie 表示, 反向恢复群表示还需要额外条件.

== 有限群概形

有限群概形把普通有限群与无穷小群放在同一框架中. 有限性指结构态射有限, 既保留各个点, 也保留这些点上的非约化结构. 一般底概形上先讨论有限局部自由群概形; 连通分解和高度理论则放在域上陈述.

=== 有限性与阶数

#definition(title: [有限群概形与阶数])[
  一个 $S$-群概形 $pi:G->S$ 若结构态射有限, 就称为*有限群概形*. 若 $pi_* cal(O)_G$ 还是有限局部自由的 $cal(O)_S$-模, 则称 $G$ 为*有限局部自由群概形*. 其*阶数*是局部常值函数
  $ op("ord")_s (G):=op("rank")_s (pi_* cal(O)_G), quad s in S $
  阶数恒为 $n$ 时, 简记 $op("ord")(G)=n$.

  在 $S=Spec R$ 上, 有限局部自由群概形恰对应于底层 $R$-模有限投射的交换 Hopf 代数 $A$. 特别地, 域 $k$ 上的有限群概形自动有限局部自由, 且
  $ op("ord")(G)=dim_k cal(O)(G) $
] <def-finite-group-scheme>

有限局部自由等价于有限, 平坦且局部有限表示. 在局部 Noetherian 底上, 它也等价于有限平坦, 见 @Stacks26[Tag 02K9]. 这些条件对任意底变换稳定, 阶数随底变换拉回. 单位截面的存在保证阶数处处为正.

#example(title: [有限但不平坦])[
  在 $ZZ$ 上取
  $ G=Spec(ZZ[t] \/ (2t,t^2)), quad
    Delta(t)=t times.o 1+1 times.o t $
  关系 $2t=0$ 与 $t^2=0$ 被余乘法保持, 因而它是加法群的有限闭子群. 坐标环作为模为 $ZZ plus.o (ZZ\/2ZZ)t$, 不是平坦模. 它在 $QQ$ 上为平凡群, 在 $bb(F)_2$ 上却是 $alpha_2$. 所以一般底上必须区分有限与有限局部自由.
]

#proposition(title: [有限商与 Lagrange 公式])[
  设 $G$ 是有限局部自由 $S$-群概形, $H subset.eq G$ 是有限局部自由闭子群. 则商 $Q=G\/H$ 由有限局部自由 $S$-概形表示, 且
  $ op("ord")(G)=op("ord")(H) dot deg(Q\/S) $
  阶数在 $S$ 上逐点计算. 若 $H$ 正规, $Q$ 也是有限局部自由群概形, 此时右侧可写为 $op("ord")(H)op("ord")(Q)$.

  特别地, 域上有限群概形的每个闭子群的阶都整除原群的阶.
] <prop-finite-group-lagrange>

#proof[
  由 @thm-group-quotient-representability, $Q->S$ 仿射, 且 $q:G->Q$ 是有限局部自由的 $H$-挠子. 因为 $q$ 有限满射且 $G->S$ 有限, $Q->S$ 仿射且普遍闭; 其有限表示性与平坦性可以沿 $q$ 作 fppf 下降. 因而 $Q->S$ 有限局部自由.

  挠子局部同构于 $H times_S Q->Q$, 所以 $q$ 的秩是 $op("ord")(H)$. 对复合 $G->Q->S$ 使用有限局部自由模的秩乘法公式, 即得结论. 域上闭子群自动有限局部自由, 所以最后一条无需额外平坦性假设.
]

#example(title: [常值群与单位根群])[
  对有限抽象群 $Gamma$, 常值群概形为
  $ underline(Gamma)_S:=coprod_(gamma in Gamma) S $
  群运算由 $Gamma$ 的乘法给出. 它总是有限 étale, 阶为 $abs(Gamma)$. 在 $Spec R$ 上, 坐标环是函数代数 $R^Gamma$, 并满足
  $ Delta(f)(g,h)=f(g h) $
  所以即使坐标环交换, 群 $Gamma$ 也可以不交换.

  单位根群 $mu_n$ 在任意底环上有限局部自由, 阶为 $n$. 对几何点 $overline(s)$, 若其特征不整除 $n$, 就有 $n$ 个互异几何点; 若特征为 $p$ 且 $n=p^r$, 则相应几何纤维为
  $ mu_(p^r)=Spec(k[t]\/((t-1)^(p^r))) $
  只有一个几何点, 阶仍为 $p^r$. 这里 $k$ 是该几何点的代数闭剩余域. 因而阶数计算的是概形的长度, 不是几何点的个数.
]

#corollary(title: [域上的 Abelian 范畴])[
  域 $k$ 上的有限交换群概形构成 Abelian 范畴, 其正合列正是相应的 fppf 群层正合列.
]

#proof[
  同态可逐点相加, 有限直积同时是直和. 核仍有限, 余核由目标除以概形论像得到, 也仍有限. 第一同构定理将余像与像识别, 从而满足 Abelian 范畴的判据. 参见 @Snow13GS1.
]

这个结论依赖于底是域. 在 $ZZ$ 上, 同态 $underline(ZZ\/2ZZ)->mu_2$ 将非零元素送到 $-1$. 其核在特征零纤维上阶为 $1$, 在特征 $2$ 纤维上阶为 $2$, 所以不是有限局部自由群概形.

=== 连通与 étale 部分

下面固定底域 $k$. 有限 $k$-代数是 Artin 代数, 所以有限概形是有限多个单点局部概形的不交并.

#theorem(title: [连通–étale 正合列])[
  设 $G$ 是有限 $k$-群概形, $G^0$ 为包含单位的连通分支. 则 $G^0$ 是几何连通的开闭正规子群, 并有自然的 fppf 正合列
  $ 1->G^0->G->G^"ét"->1, quad G^"ét":=G\/G^0 $
  其中 $G^"ét"$ 有限 étale. 它是 $G$ 的最大 étale 商, 即从 $G$ 到任意有限 étale 群概形的同态都唯一地经过 $G^"ét"$.

  这个正合列与扩域相容, 且 $op("Lie")(G^0)=op("Lie")(G)$.
] <thm-finite-connected-etale>

#proof[
  单位所在的 Artin 局部因子通过余单位映到 $k$, 所以剩余域恰为 $k$, 其极大理想幂零. 因而 $G^0$ 在任意扩域后仍连通. 乘法和取逆保持单位分支; 扩域到代数闭包后, 共轭也保持这个分支, 所以它是正规子群.

  由 @prop-finite-group-lagrange, 商 $Q=G\/G^0$ 有限局部自由. 在代数闭包上, 每个分支都由一个几何点平移 $G^0$ 得到, 因而各分支长度相同. 秩乘法公式说明 $Q$ 的阶恰为分支数, 也就是它的几何点数. 所以 $Q$ 几何约化, 从而有限 étale.

  从几何连通的 $G^0$ 到有限 étale 群的同态只能取单位值, 故商的泛性质给出最大性. 单位分支的构造与扩域相容, 商也与底变换相容. 最后, 一阶单位点只落在单位分支, 所以两者的 Lie 代数相同.
]

#corollary(title: [完美域上的分裂])[
  若 $k$ 完美, 则约化子概形 $G_"red"$ 是有限 étale 子群, 且 $G_"red"->G^"ét"$ 是同构. 于是有典范半直积分解
  $ G tilde.eq G^0 semidirect G_"red" $
  作用由共轭给出. 若 $G$ 交换, 这个半直积就是直积.
]

#proof[
  完美域上的有限约化代数是有限 étale 代数, 其张量积仍约化. 因而乘法限制到 $G_"red" times_k G_"red"->G_"red"$, 单位和逆元也限制到其中, 给出子群. 到 $G^"ét"$ 的映射在几何点上双射, 因而是有限 étale 概形的同构. 它的逆给出正合列的截面, 从而得到半直积. 这也是 @Mil17AG[命题 11.3] 的分解.
]

这里的域与完美性假设不能直接去掉. 例如 $mu_p$ 在 $ZZ$ 上的几何泛纤维是 étale 的, 单位分支阶为 $1$, 而特征 $p$ 的纤维连通, 单位分支阶为 $p$. 这些分支不能组成阶数局部常值的有限局部自由子群.

#proposition(title: [特征零的有限群概形])[
  若 $k$ 的特征为零, 则每个有限 $k$-群概形都有限 étale. 若 $k$ 代数闭, 它就是某个有限抽象群的常值群概形.
]

#proof[
  由连通–étale 正合列, 只需证明有限连通群必平凡. 写其坐标环为 Artin 局部代数 $A$, 增广理想为 $I$. 若 $I!=0$, Nakayama 引理给出 $I\/I^2!=0$. 选 $t in I$ 及单位导子 $x$ 使 $x(t)=1$, 再用 @prop-group-left-invariant-derivation 将它延拓为 $D_x$.

  $epsilon_A (D_x (t))=1$, 所以 $D_x (t)$ 是 $A$ 的单位. 取最小的 $m>=2$ 使 $t^m=0$, 对此关系求导得
  $ 0=m t^(m-1)D_x (t) $
  特征零使 $m$ 可逆, 从而 $t^(m-1)=0$, 矛盾. 故 $A=k$. 代数闭域上的有限 étale 概形是不交的有理点, 群结构遂恢复为普通有限群.
]

对一般域, 有限 étale 群概形由有限群 $G(k^"sep")$ 及其连续 $op("Gal")(k^"sep"\/k)$-作用描述, Galois 作用须保持群运算. 这是有限 étale 概形的 Galois 下降对群对象的应用. 例如 $mu_3$ 在 $QQ$ 上 étale, 但不是常值群: $mu_3 (QQ)$ 只有单位, 其几何点群却有三个元素.

=== Cartier 对偶

有限局部自由性使坐标环可以取线性对偶, 并且把所有 Hopf 结构完整地转到对偶上.

#proposition(title: [有限 Hopf 对偶与表示])[
  设 $G=Spec A$ 是有限局部自由 $R$-群概形. 则
  $ A^or:=Hom_R (A,R) $
  自然是余交换 Hopf 代数, 其乘法为卷积
  $ (phi psi)(a)=(phi times.o psi)Delta_A (a) $
  余乘法为 $A$ 的乘法的对偶. 普通 $G$-表示等价于 $A^or$-模: 对余作用 $rho:V->V times.o_R A$, 相应作用为
  $ phi dot v=(id_V times.o phi)rho(v) $
  不要求 $G$ 交换. 对常值有限群 $underline(Gamma)_R$, $A^or=R[Gamma]$, 因而这恢复了普通有限群的群代数表示.
]

#proof[
  有限投射性给出 $(A times.o_R A)^or tilde.eq A^or times.o_R A^or$, 所以可以逐一对偶化 Hopf 结构及恒等式. $A$ 的交换性转为对偶的余交换性. 余模公理恰好转为所写模作用的结合律与单位律; 反方向局部取一组对偶基恢复余作用, 并由其与基无关粘合. 对函数代数 $R^Gamma$, 点值泛函的卷积满足 $delta_g delta_h=delta_(g h)$, 正是群代数乘法.
]

#definition(title: [Cartier 对偶群])[
  若 $G$ 还是交换群概形, 则 $A$ 的余乘法也交换, 从而 $A^or$ 是交换代数. 定义
  $ G^D:=Spec(A^or) $
  称为 $G$ 的*Cartier 对偶*. 这个构造在一般底 $S$ 上可以局部作出再粘合.

  它在点上有内蕴描述
  $ G^D (T)=Hom_(cat("GrpSch")_T) (G_T,bb(G)_(m,T)) $
  即 $G^D$ 表示 $G$ 的乘法特征. 求值给出典范双乘性配对
  $ G times_S G^D->bb(G)_m, quad (g,chi) mapsto chi(g) $
] <def-cartier-dual>

#proof[
  一个代数态射 $A^or->B$ 对偶地对应于 $u in A times.o_R B$, 并满足
  $ Delta(u)=u times.o u, quad epsilon(u)=1 $
  这样的群状元自动可逆, 逆元由对极给出, 因而恰对应于 Hopf 代数态射 $B[t,t^(-1)]->A times.o_R B$, $t mapsto u$. 取 $Spec$ 即得到 $G_B->bb(G)_(m,B)$, 从而证明点函子的描述. 参见 @Mil17AG[第 11 章 c 节].
]

#theorem(title: [Cartier 对偶的性质])[
  Cartier 对偶给出有限局部自由交换 $S$-群概形范畴的反变自等价. 它保持阶数, 与任意底变换相容, 且自然求值映射给出
  $ G tilde.eq (G^D)^D $
  对有限局部自由交换群概形的 fppf 短正合列, 它反转方向:
  $ 1->H->G->Q->1 quad ==> quad 1->Q^D->G^D->H^D->1 $
]

#proof[
  前三条来自有限投射模的双对偶同构, 对偶与底变换的相容性, 以及对偶保持秩. 对正合性, 特征的商泛性质先给出 $ker(G^D->H^D)=Q^D$.

  在域上, 像分解与 Lagrange 公式说明 $G^D->H^D$ 的像阶为 $frac(op("ord")(G),op("ord")(Q))=op("ord")(H)$, 所以它有限忠实平坦. 在一般底上逐纤维应用这个结论; 源与目标都在 $S$ 上平坦且有限表示, 由纤维平坦性判据得到 $G^D->H^D$ 平坦. 它又有限表示且在每个纤维上满射, 因而是 fppf 满射. 这证明最后一项的正合性.
]

#example(title: [基本对偶])[
  对任意 $S$ 及 $n>=1$, 有
  $ (underline(ZZ\/n ZZ)_S)^D tilde.eq mu_n, quad
    mu_n^D tilde.eq underline(ZZ\/n ZZ)_S $
  配对为 $(a,zeta) mapsto zeta^a$. 特征由生成元的像决定, 而该像必须满足 $zeta^n=1$.

  在特征 $p$ 的域上还有 $alpha_p^D tilde.eq alpha_p$. 确实, 对 $A=k[t]\/(t^p)$ 的对偶基 $lambda_i (t^j)=delta_(i j)$, 卷积满足
  $ lambda_i lambda_j=binom(i+j,i)lambda_(i+j) $
  其中指标 $>=p$ 的项为零. 因而 $u=lambda_1$ 满足 $u^m=m!lambda_m$ 对 $m<p$ 成立, 并有 $u^p=0$. 同时 $u$ 是原始元, 所以 $A^or tilde.eq k[u]\/(u^p)$ 为 Hopf 代数同构.

  特别地, $mu_p$ 与 $alpha_p$ 都连通, 但前者的对偶 étale, 后者的对偶仍连通. 对偶因此提供了普通点集看不到的区分.
]

若 $G$ 不交换, 上面的 $A^or$ 通常不再是交换代数, 因而只得到对偶 Hopf 代数与其模范畴, 不能直接把 $Spec(A^or)$ 称作普通群概形.

#theorem(title: [Deligne 的阶数消去定理])[
  任意底 $S$ 上, 阶为 $n$ 的有限局部自由交换群概形满足
  $ [n]_G=0 $
  即对每个 $T->S$ 和 $g in G(T)$, 都有 $g^n=e$. 这里 $0$ 表示平凡群同态, 不要求 $n$ 在底上可逆.
]

#proof[
  可以在测试概形上局部计算, 设 $T=Spec B$, $G_T=Spec C$, 其中 $C$ 是秩 $n$ 的有限局部自由 $B$-代数. 取 $g in G(B)$ 及特征 $chi in G^D (B)$, 后者对应群状单位 $u in C^times$. 平移 $L_g$ 满足
  $ L_g^* (u)=chi(g)u $
  记 $N_(C\/B) (u)$ 为乘法算子 $c mapsto u c$ 的行列式, 即代数范数. 代数自同构保持范数, 因而
  $ N_(C\/B) (u)=N_(C\/B) (L_g^*u)=chi(g)^n N_(C\/B) (u) $
  因为 $u$ 可逆, 其范数也可逆, 所以 $chi(g)^n=1$. 此论证在任意进一步底变换后成立, 故 $g^n$ 被所有特征取为 $1$. 利用 Cartier 双对偶 $G tilde.eq (G^D)^D$, 得到 $g^n=e$. 这是 Deligne 的定理, 原证明见 @TO70[第 4--5 页].
]

=== Frobenius 与高度

#definition(title: [相对 Frobenius 与高度])[
  设 $k$ 的特征为 $p>0$, 记 $op("Frob")_k:k->k$, $a mapsto a^p$. 定义 Frobenius 扭曲及相对 Frobenius
  $ G^(p):=G times_(Spec k,op("Frob")_k) Spec k, quad op("Frob")_(G\/k):G->G^(p) $
  对 $G=Spec A$, 坐标环映射为
  $ A times.o_(k,op("Frob")_k) k->A, quad a times.o c mapsto c a^p $
  群运算与 Frobenius 相容, 所以这是群概形同态. 用 $op("Frob")^r_(G\/k):G->G^(p^r)$ 表示迭代的相对 Frobenius.

  对有限群概形 $G$, 若存在 $r>=0$ 使这个迭代经过单位截面, 则称 $G$ 的*高度至多为 $r$*. 最小的这样的 $r$ 称为高度. 特别地, 高度至多 $1$ 在仿射坐标上等价于
  $ a^p=0 quad "对所有" a in I_G $
  高度 $0$ 只对应平凡群. 这里的高度专指有限无穷小群的 Frobenius 高度.
] <def-finite-group-height>

#proposition(title: [Frobenius 区分两类有限群])[
  对有限 $k$-群概形 $G$,
  $ G "连通" quad <==> quad op("Frob")^r_(G\/k) "对某个" r "为平凡同态" $
  $ G "étale" quad <==> quad op("Frob")_(G\/k) "为同构" $
  因而有限连通群也称为*有限无穷小群概形*.
]

#proof[
  连通时, $cal(O)(G)$ 是剩余域为 $k$ 的 Artin 局部代数, 增广理想幂零. 取充分大的 $r$, 其中所有元素的 $p^r$ 次幂都为零, 所以 $op("Frob")^r$ 平凡. 反过来, Frobenius 在几何点上为双射; 若其迭代平凡, $G$ 只能有单位这一个几何点, 从而连通.

  有限 étale 情形可以在可分闭包上化为常值有限群, 其相对 Frobenius 为同构. 若有限群的 Frobenius 为同构, 则它在 $G^0$ 上也是同构; 但该限制的某个迭代又平凡, 所以 $G^0=1$, 即 $G$ étale.
]

#theorem(title: [高度至多一与限制 Lie 代数])[
  设 $k$ 的特征为 $p>0$. 有限高度至多 $1$ 的 $k$-群概形与有限维限制 $k$-Lie 代数等价. 一个方向是 $G mapsto op("Lie")(G)$, 另一个方向为
  $ frak(g) mapsto Spec(u(frak(g))^or), quad
    u(frak(g)):=U_k^"cl" (frak(g))\/chevron.l x^p-x^([p]) | x in frak(g) chevron.r $
  这里 $u(frak(g))$ 是*限制泛包络代数*, 带有使 $frak(g)$ 中元素原始的余交换 Hopf 结构. 若 $d=dim_k frak(g)$, 则对应群的阶为 $p^d$.
] <thm-height-one-restricted-lie>

#proof[
  限制 PBW 定理给出 $u(frak(g))$ 的基
  $ x_1^(a_1) dots x_d^(a_d), quad 0<=a_i<p $
  所以其维数为 $p^d$. 对偶 Hopf 代数是交换代数, 余乘法的展开说明它的增广理想中每个元素的 $p$ 次幂为零. 同一 PBW 计算将 $u(frak(g))$ 的原始元识别为 $frak(g)$, 因而构造出的群具有所需 Lie 代数.

  反过来, 设 $G=Spec A$ 高度至多 $1$, $I=ker(epsilon_A)$, $d=dim_k (I\/I^2)$. 单位导子是 $A^or$ 的原始元, 上一节的 $p$-运算给出 Hopf 代数态射 $u(op("Lie")(G))->A^or$. 取 $I\/I^2$ 的基的提升 $t_1,dots,t_d$. 由 Nakayama 引理与 $I$ 的幂零性, 这些元素生成 $A$ 作为 $k$-代数; 再用高度条件得到
  $ k[T_1,dots,T_d]\/(T_1^p,dots,T_d^p) ->> A $
  因而 $dim_k A<=p^d$. 对偶的单位导子记为 $x_i$. 总次数为 $m$ 的导子乘积消去 $I^(m+1)$; 与总次数同为 $m$ 的单项式配对时, 不同多重指标的配对为零, 而
  $ chevron.l x_1^(a_1) dots x_d^(a_d),t_1^(a_1) dots t_d^(a_d) chevron.r
    =product_i a_i! $
  当 $a_i<p$ 时这些系数非零. 按总次数排列, 配对矩阵因而为对角块可逆的三角矩阵, 所以这 $p^d$ 个导子乘积线性无关. 因而上述 Hopf 代数态射为同构.

  这些构造都与态射相容, 因此互为准逆. 这给出 @Mil17AG[命题 11.35--11.37] 的对应; 限制 PBW 定理见同书第 10 章 k 节.
]

#corollary(title: [连通有限群的阶])[
  特征 $p$ 的任意域上, 有限连通群概形的阶都是 $p$ 的幂. 因而阶与 $p$ 互素的有限群概形一定 étale.
]

#proof[
  对 Frobenius 高度归纳. $ker(op("Frob")_(G\/k))$ 高度至多 $1$, 所以其阶为 $p$ 的幂. $op("Frob")_(G\/k)$ 的像仍有限连通, 且高度降低. 应用像分解和 @prop-finite-group-lagrange, 原群的阶是核与像的阶之积. 最后一条再应用连通–étale 正合列.
]

这个推论没有说阶被 $p$ 整除就必须非约化: 常值群 $underline(ZZ\/p ZZ)_k$ 始终 étale.

进一步, 在任意底 $S$ 上, 若有限局部自由群概形的阶 $n$ 在 $S$ 上可逆, 则它有限 étale. 确实, 上述结论与特征零的结论说明所有几何纤维都 étale, 再结合平坦性与有限表示性即可.

=== 典型有限群

#example(title: [加法与乘法的 Frobenius 核])[
  在特征 $p$ 的域上, 对 $r>=1$, 用标准坐标识别加法群的 Frobenius 扭曲, 得到
  $ alpha_(p^r):=ker(op("Frob")^r:bb(G)_a->bb(G)_a)
    =Spec(k[t]\/(t^(p^r))) $
  这是阶为 $p^r$ 的连通群, 高度为 $r$. 乘法群的相应核是 $mu_(p^r)$, 同样具有阶 $p^r$ 与高度 $r$. 两者的 Lie 代数都是一维.

  令 $z=t-1$, $mu_(p^r)$ 的底层代数也变为 $k[z]\/(z^(p^r))$, 但余乘法为
  $ Delta(z)=z times.o 1+1 times.o z+z times.o z $
  而 $alpha_(p^r)$ 没有最后一项. 两者的限制 Lie 代数也不同: 前者有基元满足 $x^([p])=x$, 后者的 $p$-运算为零. 因而两者的底层概形同构, 群概形却不同构.
]

#proposition(title: [代数闭域上的阶 $p$ 群])[
  若 $k$ 代数闭且特征为 $p$, 则阶为 $p$ 的群概形恰有三种同构类型:
  $ underline(ZZ\/p ZZ)_k, quad mu_p, quad alpha_p $
  它们均交换.
]

#proof[
  连通–étale 分解与阶的乘法性说明, 这样的群或者 étale, 或者连通. 前一种只能是阶 $p$ 的常值循环群. 在连通情形, 若 Frobenius 的像非平凡, 其阶只能为 $p$, 从而 Frobenius 是同构, 矛盾. 所以群高度为 $1$, 其 Lie 代数一维.

  写 $x^([p])=a x$. 当 $a=0$ 时得到 $alpha_p$; 当 $a!=0$ 时, 代数闭性允许缩放基元使 $x^([p])=x$, 得到 $mu_p$. 最后用 @thm-height-one-restricted-lie 即得分类. 底域不代数闭时还会出现这些群的扭曲形式.
]

#align(center, table(
  columns: (auto, auto, auto, auto),
  column-gutter: 0pt,
  inset: (x: 8pt, y: 5pt),
  stroke: .4pt + gray,
  table.header([群], [几何形态], [$dim op("Lie")$], [Cartier 对偶]),
  [$underline(ZZ\/p ZZ)_k$], [$p$ 个点, étale], [$0$], [$mu_p$],
  [$mu_p$], [一个点, 非约化], [$1$], [$underline(ZZ\/p ZZ)_k$],
  [$alpha_p$], [一个点, 非约化], [$1$], [$alpha_p$],
))

#example(title: [光滑群的第一 Frobenius 核])[
  设 $G$ 是特征 $p$ 的域上的 $d$ 维光滑有限型群概形. 相对 Frobenius 有限局部自由, 秩为 $p^d$, 因而
  $ G_1:=ker(op("Frob")_(G\/k)), quad op("ord")(G_1)=p^d $
  且 $op("Lie")(G_1)=op("Lie")(G)$, 包括 $p$-运算. 秩的计算可在光滑的 étale 局部坐标中化为 $k[t_1^p,dots,t_d^p] subset k[t_1,dots,t_d]$, 其基为各指数小于 $p$ 的单项式; Lie 等式来自 Frobenius 的微分为零.

  例如 $(GL_n)_1$ 的点是满足 $g_(i j)^p=delta_(i j)$ 的可逆矩阵, 阶为 $p^(n^2)$, 对应限制 Lie 代数 $gl_n$ 及矩阵 $p$ 次幂. 当 $n>=2$ 时, 这给出非交换的有限无穷小群概形.
]

#example(title: [椭圆曲线的有限挠子群])[
  设 $E$ 是域 $k$ 上的椭圆曲线, $n>=1$. 乘 $n$ 映射的核
  $ E[n]:=ker([n]:E->E) $
  是阶为 $n^2$ 的有限群概形. 这里使用椭圆曲线的基本同源定理, 即 $[n]$ 有限平坦且次数为 $n^2$. 当 $n$ 与特征互素时, $E[n]$ étale, 并有
  $ E[n]_(overline(k)) tilde.eq underline((ZZ\/n ZZ)^2)_(overline(k)) $

  在代数闭的特征 $p$ 域上, 普通 (ordinary) 椭圆曲线满足
  $ E[p] tilde.eq mu_p times underline(ZZ\/p ZZ)_k $
  有 $p$ 个几何点. 超奇异 (supersingular) 情形的 $E[p]$ 则连通, 只有一个几何点, 但阶仍为 $p^2$. 两种情形都有 $dim_k op("Lie")(E[p])=1$, 因为 $d[p]=0$ 且 $dim_k op("Lie")(E)=1$. 特别地, 超奇异情形的 $E[p]$ 不是 $alpha_p times alpha_p$, 后者的 Lie 代数为二维. 这些标准结论见 @Snow13GS2.
]
