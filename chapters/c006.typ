#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= 拟凝聚 / Quasi-Coherent

== 拟凝聚模的定义

拟凝聚模是刻画几何对象上线性代数数据的工具. 本章允许这些数据携带各次同伦信息; 普通拟凝聚层是其中集中在零次的特殊情况.

=== Grothendieck 构造与拉直

一个函子 $F:C->Cat_oo$ 给每个 $c$ 指定一个范畴 $F(c)$. *Grothendieck 构造*把它们合成一个总范畴及投影:
$ E:=integral_C F, quad p:E->C $
对象是 $(c,x)$, 其中 $x in F(c)$; 态射是 $f:c->d$ 连同 $F(f)(x)->y$, 并保留全部相容同伦. 投影的纤维就是 $F(c)$. 总范畴也称为*元素的无穷范畴* (∞-category of elements).

从 $F$ 构造这样的投影叫*反拉直* (unstraightening); 反过来, 从投影读出纤维及沿箭头的运输, 叫*拉直* (straightening). 这里的投影是 coCartesian 纤维化, 两个过程互为等价. 若 $F$ 取值于 $Ani$, 对应的是左纤维化. 反变函子则对应 Cartesian 纤维化, 生象值时对应右纤维化. 参见 @Lur09[第 3.2 节], @Ker26[第 5.6 节].

后面只需记住两个事实: *换基* $u:D->C$ 对应预合成 $F compose u$; *取极限*对应相容地选择各层对象 $x_c in F(c)$, 连同等价 $F(f)(x_c) tilde.eq x_d$ 及其全部相容同伦. 参见 @Lur09[第 3.2.1 节, 第 3.3.3 节].

=== 一般定义

先使用 @def-ani-sheaf 中的预层概念. 现在固定一个交换环谱 $Lambda$, 定义*交换 $Lambda$-代数的 $oo$-范畴*
$ CAlg_Lambda tilde.eq CAlg(Sp)_(Lambda \/) $
也就是说, 一个 $Lambda$-代数是一个交换环谱 $A$ 连同一个环谱同态 $Lambda->A$. 我们把 $CAlg_Lambda^opp$ 看作仿射测试对象的范畴. 下面说的一个*预层*, 是指一个*可达* (@def-accessible-functor, 由于 $CAlg_Lambda, Ani$ 都可呈示, 这个定义是合理的) 的函子
$ cal(F): CAlg_Lambda->Ani $

#definition(title: [$Spec$ 作为可表函子])[
  对交换环谱 $R$, 定义
  $ Spec R:CAlg(Sp)->Ani, quad (Spec R)(A):=Map_(CAlg(Sp)) (R,A) $
  它是在 $CAlg(Sp)^opp$ 上由 $R$ 可表的预层. 沿 $A->B$ 的映射由后复合给出; 本章先把 $Spec$ 理解为这个点函子的记号. 参见 @Ker26[第 8.3 节].

  固定底环谱 $Lambda$ 后, 对 $R in CAlg_Lambda$, 后文的 $Spec R$ 使用相对版本:
  $ (Spec R)(A):=Map_(CAlg_Lambda) (R,A) $
  特别地, $Lambda$ 是 $CAlg_Lambda$ 的始对象, 所以
  $ (Spec Lambda)(A)=Map_(CAlg_Lambda) (Lambda,A) tilde.eq * $
  因而 $Spec Lambda$ 是相对预层范畴的终对象, 每个预层 $cal(F)$ 都有典范的*结构态射* $cal(F)->Spec Lambda$.
] <def-spec-representable-functor>

注意方向: 预层对仿射对象反变, 而环谱态射 $A->B$ 对应 $Spec B->Spec A$, 所以点函子给出 $cal(F)(A)->cal(F)(B)$. 此时还没有施加任何覆盖拓扑下的层条件.

#remark(title: "为什么要求可达")[
  $CAlg_Lambda$ 是大范畴. 要求可达, 是为了让 $cal(F)$ 仍能由*一小族测试代数上的数据恢复*, 从而控制后续构造的大小.

  具体地, 对某个小正则基数 $kappa$, $cal(F)$ 保持小 $kappa$-滤过余极限:
  $ colim_i cal(F)(A_i) tilde.eq cal(F)(colim_i A_i) $
  取 $kappa$ 足够大, 这族测试对象可选为 $kappa$-紧代数. 每个仿射点函子 $B mapsto Map_(CAlg_Lambda) (A,B)$ 都可达; 这里允许 $kappa$ 变大, 因而不要求 $A$ 有限呈示. 这是大小条件, 层条件另行施加. 参见 @Ker26[注 9.4.8.2, 例 9.4.8.16].
]

现在对预层 $cal(F)$ 作 Grothendieck 构造, 得到它的*元素的无穷范畴*
$ J_(cal(F)):=integral_(CAlg_Lambda) cal(F) -> CAlg_Lambda $
这是对应 $cal(F)$ 的左纤维化, 在 $A$ 上的纤维为 $cal(F)(A)$. 具体地, 对象是 $(A,x)$, 其中 $x in cal(F)(A)$; 态射 $(A,x)->(B,y)$ 是 $Lambda$-代数态射 $f:A->B$, 连同路径 $gamma:cal(F)(f)(x) tilde.eq y$. 因而可以直观地把 $J_(cal(F))$ 看成组织所有测试点及其基变换的范畴.

将 $(A,x)$ 送到 $Mod_A$, 将上述态射送到扩张标量函子
$ f^*:Mod_A->Mod_B, quad M mapsto B⊗_A M $
就得到图表 $J_(cal(F))->Cat_oo$.

#definition(title: "拟凝聚模")[
  预层 $cal(F):CAlg_Lambda->Ani$ 上的*拟凝聚模范畴*定义为
  $ QCoh(cal(F)):=varprojlim((A,x) in J_(cal(F))) Mod_A $
  这里在足够大宇宙的 $Cat_oo$ 中取极限. 它的对象称为 $cal(F)$ 上的*拟凝聚模* (quasi-coherent module). 参见 @Lur11DAG8[定义 2.7.8, 注 2.7.9].
] <def-qcoh-prestack>

#remark(title: "这个极限怎样取")[
  对 $M in QCoh(cal(F))$, 记号 $M_(A,x)$ 表示它在测试点 $(A,x)$ 上的取值. 这是极限自带的投影函子给出的:
  $ op("ev")_(A,x):QCoh(cal(F))->Mod_A, quad M mapsto M_(A,x) $
  下标 $A$ 指定系数环谱, $x in cal(F)(A)$ 指定一个 $A$-值点. 由 Yoneda 引理, $x$ 也就是态射 $x:Spec A->cal(F)$. 用后面拉回的记号说,
  $ M_(A,x) tilde.eq x^* M in QCoh(Spec A) tilde.eq Mod_A $
  所以, *$M$ 是整个拟凝聚模, $M_(A,x)$ 是把它拉到这个仿射测试对象上得到的 $A$-模*.

  一个对象 $M$ 由所有这些模 $M_(A,x)$, 连同对每个 $(f,gamma):(A,x)->(B,y)$ 指定的等价组成:
  $ theta_(f,gamma):B⊗_A M_(A,x) stretch(->)^tilde M_(B,y) $
  它们对恒等、复合及全部高阶同伦相容. 例如沿 $A->B->C$ 连做两次换系数, 应与直接沿 $A->C$ 换系数相容, 使用自然等价
  $ C⊗_B (B⊗_A M_(A,x)) tilde.eq C⊗_A M_(A,x) $
  态射则是一族相容的模映射, 同样带有相容同伦. 所以取这个极限, 就是在所有测试点上选择模, 并使它们随基变换一致. 参见 @Lur11DAG8[注 2.7.12].
]

#example(title: "仿射情形怎样计算")[
  若 $cal(F)=Spec R$, 则 $cal(F)(A)=Map_(CAlg_Lambda) (R,A)$. 此时 $J_(cal(F))$ 就是 $R$-代数范畴, 有始对象 $(R,id_R)$. 因而整个相容族由这里的一个 $R$-模 $M$ 决定:
  $ M_(A,x) tilde.eq A⊗_R M, quad x:R->A $
  在始对象处取值与上述扩张标量构造互逆, 从而
  $ QCoh(Spec R) tilde.eq Mod_R $
  例如 $M=R$ 时, 每个测试点上的值就是 $A$; 沿 $A->B$ 的相容等价为 $B⊗_A A tilde.eq B$.
]

#remark(title: "景与层从哪里开始用")[
  定义 $Spec A$ 和 $QCoh(cal(F))$ 时, 只需测试范畴与函子, 不必指定 Grothendieck 拓扑, 也不要求 $cal(F)$ 是层. 后面的拉回、右伴随前推以及用整体截面谱定义上同调, 同样适用于本章的可达预层.

  从下一小节的*沿覆盖粘合*开始, 才真正使用景与下降: 普通概形使用 Zariski 覆盖, 代数叠使用光滑图册及平坦下降. 要区分两件事: 几何点函子的层条件允许粘合局部几何数据; *模范畴的下降定理*则允许粘合模及其态射. 后者保证对这样的覆盖 $U->X$, 及其 Čech 神经 $U_bullet$, 有
  $ QCoh(X) tilde.eq varprojlim([n] in Delta) QCoh(U_n) $
  因而可以用一个覆盖及其各重交集, 代替定义中的所有测试点. 这一步用到了下降定理, 并非仅由取极限的定义直接得到. 参见 @Lur11DAG8[命题 2.7.14, 注 2.7.15].

  后面用 Čech 复形或图册计算上同调, 以及把这些定义与经典层论比较, 都依赖这一步. 所以这里的拟凝聚模先由相容模族定义, 再借助下降与熟悉的层联系起来.
] <rem-qcoh-site-descent>

=== 概形上的拟凝聚模

下面取普通域 $K$, 令 $Lambda=H K$. 将普通仿射 $K$-概形 $Spec R$ 看作由 $H R$ 表示的函子 $Spec(H R)$, 再沿覆盖粘合, 就能把普通 $K$-概形放入上述框架. 本章的 $QCoh$ 包含导出信息; 普通拟凝聚层范畴记为 $QCoh^"ord"$.

#example(title: "仿射概形: 模与模复形")[
  对 $X=Spec R$, 前面的计算给出
  $ QCoh(X) tilde.eq Mod_(H R) tilde.eq Dcat(R), quad QCoh(X)^suit.heart tilde.eq Mod_R^"ord" $
  因此这里的对象可以理解为模复形, 而普通 $R$-模 $V$ 对应集中在零次的拟凝聚模, 也就是普通拟凝聚层 $tilde(V)$. 在主开集上, 它就是熟悉的局部化:
  $ H^0 (D(f),tilde(V)) tilde.eq V_f $
  参见 @Stacks26[Tag 01I6].
]

#example(title: "用仿射开覆盖计算")[
  设 $X=U ∪ V$, 其中 $U=Spec R$, $V=Spec S$, 并假设交集 $W=U ∩ V=Spec T$ 也仿射. 则
  $ QCoh(X) tilde.eq Mod_(H R) times_(Mod_(H T)) Mod_(H S) $
  右边是在 $Cat_oo$ 中取纤维积, 两条箭头都是扩张标量. 一个对象就是两个模 $M_U,M_V$, 连同交集上的等价
  $ H T⊗_(H R) M_U tilde.eq H T⊗_(H S) M_V $
  所以, *先在各块上给模, 再把交集上的限制认作同一个*. 多块覆盖时还要加入三重交集及更高重交集上的相容数据. 这里的张量积和拉回都按导出意义理解. 参见 @Lur11DAG8[命题 2.7.14, 2.7.18].

  例如 $PP_K^1$ 由 $U=Spec K[t]$ 与 $V=Spec K[s]$ 粘合, 交集上 $s=t^(-1)$. 在两块上各取一个自由秩一模, 以
  $ e_V=t^d e_U $
  粘合, 就得到 $cal(O)_(PP_K^1) (d)$. 每块上都是平凡线丛, 不同的粘合方式产生了不同的全局线丛.
]

#definition(title: "上同调层与拟凝聚复形")[
  设 $X$ 为普通概形. 一个 $cal(O)_X$-模层的上链复形写作
  $ E^bullet=(dots -> E^(i-1) stretch(->)^(d^(i-1)) E^i stretch(->)^(d^i) E^(i+1) -> dots), quad d^i compose d^(i-1)=0 $
  它的第 $i$ 个*上同调层* (cohomology sheaf) 定义为
  $ cal(H)^i (E^bullet):=op("ker")(d^i) slash op("im")(d^(i-1)) $
  核、像和商都在 $cal(O)_X$-模层的范畴中取. 直观上, 它保留第 $i$ 次中被下一步送到零、又尚未被上一步解释掉的局部数据.

  这里称 $E^bullet$ 为*拟凝聚复形* (quasi-coherent complex), 若每个 $cal(H)^i (E^bullet)$ 都是普通拟凝聚层. 拟凝聚性要求放在上同调层上; 逐项拟凝聚的复形自动满足这一条件. 将这些复形的准同构视为等价, 就得到普通概形上 $QCoh(X)$ 的经典复形描述. 因而对它所表示的拟凝聚模 $M$, 也记
  $ cal(H)^i (M):=cal(H)^i (E^bullet) $
  这个记号不依赖复形代表的选择, 因为准同构正是在所有上同调层上给出同构的映射. 参见 @Stacks26[Tag 06YZ].

  在仿射开集 $U=Spec R$ 上, 若 $M|_U$ 对应 $R$-模复形 $N^bullet$, 则
  $ cal(H)^i (M)|_U tilde.eq tilde(H^i (N^bullet)) $
  右边先在普通模中取上同调, 再变成层. 例如, 在 $X=Spec K[t]$ 上, 两项复形 $cal(O)_X stretch(->)^t cal(O)_X$ 放在第 $-1,0$ 次, 则 $cal(H)^(-1)=0$, $cal(H)^0 tilde.eq tilde(K[t] slash (t))$.

  *$cal(H)^i (M)$ 是 $X$ 上的层; $H^i (X,M)$ 则是先取整体截面模谱, 再读出次数得到的模.* 后者还会记录局部数据的粘合, 两者需要区分.
] <def-qcoh-complex-cohomology-sheaf>

#definition(title: "拟凝聚层: 集中在零次的特殊情况")[
  设 $X$ 为普通概形. 一个普通 $cal(O)_X$-模层称为*拟凝聚层* (quasi-coherent sheaf), 若局部在仿射开集 $U=Spec R$ 上形如 $tilde(V)$, 其中 $V$ 是普通 $R$-模.

  按仿射开集上的标准 $t$-结构粘合, 得到 $QCoh(X)$ 的标准 $t$-结构. 上述普通拟凝聚层恰好组成它的心:
  $ QCoh(X)^suit.heart tilde.eq QCoh^"ord" (X) $
  也就是说, 拟凝聚模 $M$ 对应普通拟凝聚层, 当且仅当
  $ cal(H)^i (M)=0 quad (i != 0) $
  这里 $cal(H)^i$ 是第 $i$ 个*上同调层*. 等价地, 在每个普通仿射开集 $Spec R subset.eq X$ 上, $M$ 对应某个普通 $R$-模 $V$ 的模谱 $H V$. 参见 @Stacks26[Tag 01I6], @Lur11DAG8[例 2.7.25].

  例如, $K[t] slash (t)$ 给出仿射直线上支撑在原点的拟凝聚层; 而 $Spec K$ 上的 $H K[1]$ 是拟凝聚模, 有非零的 $cal(H)^(-1)$, 因而不属于心. *集中在零次说的是上同调层, 不要求整体上同调 $H^i (X,M)$ 在高次消失.*
] <def-qcoh-ordinary-sheaf>

=== 叠上的拟凝聚模

对 $K$ 上的 Artin 叠 $cal(X)$, 选一个光滑满射图册 $U->cal(X)$, 记 $U_n$ 为 $n+1$ 个 $U$ 在 $cal(X)$ 上的纤维积. 平坦下降给出
$ QCoh(cal(X)) tilde.eq varprojlim([n] in Delta) QCoh(U_n) $
图表中的函子由拉回给出. 各层若是代数空间, 可以继续取平展仿射覆盖计算. 这就是把定义中“所有测试点上的相容数据”, 换成*一个图册及其重叠上的相容数据*. 参见 @Lur11DAG8[命题 2.7.14].

对于普通拟凝聚层, 只需在 $U$ 上给出 $V$, 再在 $U_1$ 上给出同构
$ theta:p_1^* V stretch(->)^tilde p_2^* V $
它沿对角线为恒等, 并在 $U_2$ 上满足余循环条件. 一般拟凝聚模还保留全部高阶相容同伦. 对普通 Artin 叠, 同样在光滑图册上检验集中在零次的条件, 得到
$ QCoh(cal(X))^suit.heart tilde.eq QCoh^"ord" (cal(X)) $
参见 @Stacks26[Tags 06WU, 06WS], @Lur11DAG8[例 2.7.25].

#example(title: "商叠: 拟凝聚模带有等变结构")[
  设光滑仿射群概形 $G slash K$ 作用于 $K$-概形 $X$. 图册 $X->[X slash G]$ 的各重叠是 $G times X,G times G times X,dots$, 因此
  $ QCoh([X slash G]) tilde.eq QCoh^G (X) $
  右边表示带相容 $G$-等变结构的拟凝聚模: 群作用移动底空间上的点, 同时给出模在这些点之间的识别. 等变性针对整个群概形的作用, 包括随基底变化的群元素. 参见 @Stacks26[Tags 043S, 06WS].

  特别地, $B G=[Spec K slash G]$ 上的普通拟凝聚层就是 $G$ 的代数表示:
  $ QCoh(B G)^suit.heart tilde.eq cat("Rep")_K (G) $
  表示允许无限维; 有限维表示对应向量丛. 两个具体例子是:
  - 若 $G$ 是有限常群 $Gamma$, 就得到普通群代数 $K[Gamma]$ 的模.
  - 若 $G=bb(G)_m$, 就得到 $ZZ$-分次向量空间 $V=⊕_(d in ZZ) V_d$: 在权 $d$ 的部分, $t$ 作用为乘以 $t^d$. 权 $d$ 的一维表示给出 $B bb(G)_m$ 上的线丛.

  这也说明叠上的拟凝聚模多记录了什么: 在每个几何点处, *该点的自同构群会作用在模的纤维上*.
]

== 导出拉回与导出前推

回到一般的交换环谱 $Lambda$. 本节直接在稳定无穷范畴 $QCoh$ 之间定义拉回与前推. *这里的导出信息已经包含在模谱、映射生象与无穷范畴的极限中.* 本章统一使用 $f^*,f_*,Gamma$, 均按内蕴的导出意义理解.

设 $f:cal(F)->cal(G)$ 是两个可达预层之间的态射, 即自然变换. 它把 $cal(F)$ 的测试点送到 $cal(G)$ 的测试点:
$ J_(cal(F))->J_(cal(G)), quad (A,x) mapsto (A,f_A (x)) $

#definition(title: "导出拉回")[
  沿上述函子限制相容模族, 得到*导出拉回* (derived pullback) 函子
  $ f^*:QCoh(cal(G))->QCoh(cal(F)) $
  具体地, 对 $M in QCoh(cal(G))$, 定义
  $ (f^* M)_(A,x):=M_(A,f_A (x)) $
  沿测试点态射的相容等价也直接从 $M$ 继承. 换句话说, *在 $cal(F)$ 的点 $x$ 上, 读取 $M$ 在 $f(x)$ 上的数据*. 参见 @Lur11DAG8[记号 2.7.11, 注 2.7.12].
] <def-qcoh-pullback>

前推的定义需要一个存在性事实: *这两个拟凝聚模范畴都可呈示, 而 $f^*$ 保持所有小余极限*.

#proofsketch[
  可达性使预层能写成仿射点函子的小余极限. 因而它的 $QCoh$ 是模范畴组成的小极限, 过渡函子都是保持余极限的扩张标量; 可呈示范畴的极限定理给出可呈示性. 余极限可以在每个测试点的模范畴中计算, 所以限制相容族的 $f^*$ 也保持余极限. 参见 @Lur09[命题 5.5.3.13], @Lur11DAG8[注 2.7.9, 命题 2.7.17].
]

#definition(title: "导出前推")[
  由伴随函子定理, $f^*$ 在无穷范畴意义下存在右伴随, 称为沿 $f$ 的*导出前推* (derived pushforward):
  $ f_*:QCoh(cal(F))->QCoh(cal(G)), quad f^* tack.l f_* $
  它由下列对 $M,N$ 自然的等价刻画:
  $ Map_(QCoh(cal(F))) (f^* M,N) tilde.eq Map_(QCoh(cal(G))) (M,f_* N) $
  也就是说, 从 $M$ 映入 $f_* N$, 就等于先把 $M$ 拉到 $cal(F)$ 上, 再映入 $N$. 这里要求的是整个映射生象的自然等价, 连同全部高阶同伦. 这个泛性质把 $f_*$ 确定到典范等价. 参见 @Lur09[推论 5.5.2.9].
] <def-qcoh-pushforward>

#remark(title: "导出已经内蕴")[
  定义中的 $Mod_A$ 是模谱的稳定无穷范畴, 张量积是模谱的相对张量积, 而 $QCoh$ 的极限保留全部相容同伦. 拉回在这样的相容族上定义, 前推则由这些无穷范畴中的伴随关系确定.

  用普通环上的复形描述时, 准同构已经成为等价; 分解是计算这些函子的一种方法, 导出信息在上述定义时就已经存在. 参见 @Lur11DAG8[定义 2.7.8, 注 2.7.9--2.7.12].
] <rem-qcoh-intrinsic-derived>

#remark(title: "张量–Hom 伴随在说什么")[
  对普通交换环 $R$ 及 $R$-模 $M,N,P$, 有自然同构
  $ Hom_R (M⊗_R N,P) tilde.eq Hom_R (M,Hom_R (N,P)) $
  左边的映射同时接收两个输入. 固定第一个输入, 就得到关于第二个输入的线性映射:
  $ phi mapsto (u mapsto (v mapsto phi(u⊗v))) $
  反过来, 给定 $psi:M->Hom_R (N,P)$, 令 $phi(u⊗v)=psi(u)(v)$ 即可. *同一份双线性数据, 可以先合并输入, 也可以分两次输入.* 这就是 *tensor–Hom adjunction*, 即*张量–Hom 伴随*. 参见 @Stacks26[Tag 00CV].
]

#definition(title: "拟凝聚模的内部 Hom")[
  在 $C=QCoh(cal(F))$ 中, 张量积逐测试点定义:
  $ (M⊗N)_(A,x):=M_(A,x)⊗_A N_(A,x) $
  固定 $N$, 函子 $-⊗N:C->C$ 保持小余极限, 因而有右伴随, 记为 $underline(Hom)_(cal(F)) (N,-)$. 其值称为*内部 Hom* (internal Hom), 由自然等价刻画:
  $ Map_C (M⊗N,P) tilde.eq Map_C (M,underline(Hom)_(cal(F)) (N,P)) $
  这里的 $Map_C$ 是生象, 而 $underline(Hom)_(cal(F)) (N,P)$ 是 $cal(F)$ 上的拟凝聚模. 取 $cal(F)=Spec A$, 它就是内部 $A$-模 $underline(Hom)_A (N,P)$, 底层谱是上一章的 $A$-线性映射谱 $underline(Map)_A (N,P)$. 参见 @Lur11DAG8[第 2.7 节], @Lur09[推论 5.5.2.9].
] <def-qcoh-internal-hom>

张量积可以逐测试点计算; 内部 Hom 则使用上述伴随性质定义. 一般不能直接把各点的内部 Hom 拼起来, 因为内部 Hom 未必与扩张标量交换.

#example(title: "仿射情形: 换系数与限制系数")[
  对环谱态射 $A->B$ 及对应的 $f:Spec B->Spec A$, 有
  $ f^* M tilde.eq B⊗_A M, quad f_* N tilde.eq op("Res")_A^B N $
  左边把 $A$-模扩张为 $B$-模; 右边保持 $N$ 的底层谱, 只沿 $A->B$ 将它看作 $A$-模. 这正是上一章的扩张标量与限制标量伴随.

  这也解释了为什么“限制相容族”会给出换系数: 在 $B$ 这个测试点, 原来的相容族就已经取值为 $B⊗_A M$.

  这也是换底环的张量–Hom 伴随:
  $ Map_(Mod_B) (B⊗_A M,N) tilde.eq Map_(Mod_A) (M,op("Res")_A^B N) $
  右边成为限制标量, 是因为正则 $B$-模满足 $underline(Hom)_B (B,N) tilde.eq N$, 再沿 $A->B$ 看成 $A$-模即可. 普通环时, 两个方向写出来就是
  $ phi mapsto (u mapsto phi(1⊗u)), quad psi mapsto (b⊗u mapsto b psi(u)) $
  $A$-线性保证后式尊重张量积的关系, 两个过程互逆. 环谱时, 这一对应保留全部相容同伦, 给出映射生象的等价. 参见 @Lur17[命题 4.6.2.17].

  对普通环态射 $R->S$ 及普通 $R$-模 $V$, 拉回对应 $H S⊗_(H R) H V$, 并且
  $ pi_i (H S⊗_(H R) H V) tilde.eq Tor_i^R (S,V) quad (i>=0) $
  例如 $R=K[t]$, $S=V=K$, 用分解 $K[t] stretch(->)^t K[t]$ 计算, 得到 $pi_0 tilde.eq K$, $pi_1 tilde.eq K$. 所以公式中的张量积本身就记录了 Tor.
]

#remark(title: "几个直接得到的性质")[
  $f^*$ 保持小余极限, $f_*$ 保持小极限; 两者都保持零对象和有限正合序列. 这里的正合是在稳定无穷范畴中理解的.

  特别地, 两者与移位交换, 上面的伴随也给出映射谱的等价
  $ underline(Map)_(QCoh(cal(F))) (f^* M,N) tilde.eq underline(Map)_(QCoh(cal(G))) (M,f_* N) $
  因而各个次数的导出态射信息都包含在这对伴随中.

  对 $cal(F) stretch(->)^f cal(G) stretch(->)^g cal(H)$, 有自然等价
  $ (g compose f)^* tilde.eq f^* g^*, quad (g compose f)_* tilde.eq g_* f_* $
  恒等态射的拉回与前推都是恒等函子. 第一式来自限制相容族, 第二式来自右伴随的唯一性.
]

#remark(title: "与普通层的关系")[
  对普通概形之间的拟紧拟分离态射 $f:X->Y$, 上述函子与经典的导出拉回、导出前推在拟凝聚复形上的作用一致. 这里的复形与上同调层 $cal(H)^i$ 按 @def-qcoh-complex-cohomology-sheaf 理解. 若 $V,W$ 分别是 $Y,X$ 上的普通拟凝聚层, 则 $cal(H)^0 (f^* V)$ 是 $V$ 的普通拉回, $cal(H)^0 (f_* W)$ 是 $W$ 的普通前推. 经典的高阶前推正是
  $ R^i f_* W:=cal(H)^i (f_* W) quad (i>=0) $
  所以 $f^* V,f_* W$ 一般会离开心; 它们保留整个导出对象, 取 $cal(H)^0$ 才回到普通层的运算. 仿射上, 拉回的零次恢复普通张量积, 负次上同调层记录 Tor; 前推的正次上同调层则记录高阶前推. 参见 @Stacks26[Tags 06YI, 079V, 08DY].
]

=== 结构态射的拉回与整体截面

#remark(title: [$p^*$ 怎样把系数放到几何对象上])[
  设 $p:cal(F)->Spec Lambda$ 是结构态射. 一个 $Lambda$-模 $L$ 在 $Spec Lambda$ 的测试点 $Lambda->A$ 上取值为 $A⊗_Lambda L$. 因此, 沿 $p$ 限制这族数据, 就得到
  $ p^*:Mod_Lambda->QCoh(cal(F)), quad (p^* L)_(A,x) tilde.eq A⊗_Lambda L $
  沿 $A->B$ 的相容等价来自 $B⊗_A (A⊗_Lambda L) tilde.eq B⊗_Lambda L$. 所以 $p^*$ 做的是: *把同一个系数模 $L$, 随各个测试点扩张标量*.

  记张量积的单位对象为 $cal(O)_(cal(F)):=p^* Lambda$, 它在 $(A,x)$ 处取值为 $A$. 我们也把上述构造记作
  $ p^* L tilde.eq cal(O)_(cal(F))⊗_Lambda L $
  对普通概形 $X$, $cal(O)_X$ 就是通常的结构层. 例如, 对 $r>=0$ 与 $d in ZZ$, 有
  $ p^* (Lambda^(⊕r)) tilde.eq cal(O)_(cal(F))^(⊕r), quad p^* (Lambda[d]) tilde.eq cal(O)_(cal(F))[d] $
  第一式把自由模变成平凡模, 第二式保留移位. 参见 @Lur11DAG8[记号 2.7.11, 注 2.7.12, 记号 2.7.27].
] <rem-qcoh-structure-pullback>

#definition(title: [整体截面函子 $Gamma$])[
  设 $cal(F):CAlg_Lambda->Ani$ 是可达预层, $p:cal(F)->Spec Lambda$ 是结构态射. 定义*整体截面函子* (global sections functor)
  $ Gamma(cal(F),-):=p_*:QCoh(cal(F))->Mod_Lambda, quad Gamma(cal(F),M):=p_* M $
  它是 $p^*:Mod_Lambda->QCoh(cal(F))$ 的右伴随. 因而对每个 $L in Mod_Lambda$ 和 $M in QCoh(cal(F))$, 有自然等价
  $ Map_(Mod_Lambda) (L,Gamma(cal(F),M)) tilde.eq Map_(QCoh(cal(F))) (p^* L,M) $
  这就是 $Gamma$ 的泛性质: *从 $L$ 映到整体截面, 等于把 $L$ 拉到 $cal(F)$ 上, 再映到 $M$*. 它的取值是 $Lambda$-模谱, 导出信息已经内蕴.
] <def-qcoh-global-sections>

#remark(title: "从单位对象到相容截面")[
  取系数模 $L=Lambda$, 并使用上一章的映射谱, 伴随关系给出
  $ U_Lambda Gamma(cal(F),M) tilde.eq underline(Map)_(QCoh(cal(F))) (cal(O)_(cal(F)),M) $
  这里 $U_Lambda:Mod_Lambda->Sp$ 忘掉系数. 所以整体截面的底层谱, 就是*从单位对象到 $M$ 的映射谱*. 特别地, 一个 $s in pi_0 Gamma(cal(F),M)$ 对应一个态射 $cal(O)_(cal(F))->M$ 的同伦类.

  用定义中的相容模族, 还可以直接计算
  $ Gamma(cal(F),M) tilde.eq varprojlim((A,x) in J_(cal(F))) op("Res")_Lambda^A M_(A,x) $
  这里在 $Mod_Lambda$ 中取极限. 沿 $(A,x)->(B,y)$ 的箭头由 $M_(A,x)->B⊗_A M_(A,x) tilde.eq M_(B,y)$ 给出, 再限制系数到 $Lambda$. 因为从 $cal(O)_(cal(F))$ 到 $M$ 的映射就是相容的 $A$-模映射 $A->M_(A,x)$, 对各次移位也如此, 所以得到上述公式. 直观地说, *整体截面是各测试点上的截面及其全部相容同伦*.
]

#example(title: "仿射与普通层的整体截面")[
  对 $cal(F)=Spec A$ 和 $A$-模 $M$, 整体截面就是 $M$ 本身, 仅限制系数:
  $ Gamma(Spec A,M) tilde.eq op("Res")_Lambda^A M $
  对普通概形 $X$ 上的普通拟凝聚层 $V$, 通常的截面群是
  $ H^0 (X,V) tilde.eq pi_0 Gamma(X,V) $
  $Gamma(X,V)$ 还保留全部高阶上同调; 下一节按次数读出这些信息.
]

#proposition(title: "单位与求值映射")[
  伴随 $p^* tack.l Gamma(cal(F),-)$ 给出两条自然映射:
  $ eta_L:L->Gamma(cal(F),p^* L), quad epsilon_M:p^* Gamma(cal(F),M)->M $
  它们分别称为*单位*与*余单位*. 在伴随等价下, 前者对应 $id_(p^* L)$, 后者对应 $id_(Gamma(cal(F),M))$, 并满足三角恒等式.

  $eta_L$ 把原来的系数变成整体截面. $epsilon_M$ 则是*求值映射*: 在测试点 $(A,x)$ 上, 它是
  $ A⊗_Lambda Gamma(cal(F),M)->M_(A,x) $
  先把整体截面限制到这个点, 再用 $A$ 的作用扩张为 $A$-线性映射. 在 $cal(F)=Spec A$ 时, 它就是作用映射 $A⊗_Lambda op("Res")_Lambda^A M->M$.
] <prop-qcoh-global-unit-counit>

#proposition(title: "基本运算与整体函数环谱")[
  $p^*$ 保持小余极限, $Gamma(cal(F),-)$ 保持小极限; 两者都保持纤维序列、余纤维序列与移位. 因而它们也保持有限直和. 这些是前面一般拉回与前推性质的直接应用.

  $p^*$ 还保持张量积及单位, 即它是*对称幺半函子*:
  $ p^* (L⊗_Lambda N) tilde.eq p^* L⊗p^* N, quad p^* Lambda tilde.eq cal(O)_(cal(F)) $
  逐测试点使用扩张标量与张量积的结合律, 就能验证第一式.

  右伴随 $Gamma$ 因而带有*松对称幺半结构* (lax symmetric monoidal structure): 有自然映射
  $ Gamma(cal(F),M)⊗_Lambda Gamma(cal(F),N)->Gamma(cal(F),M⊗N) $
  以及单位映射 $Lambda->Gamma(cal(F),cal(O)_(cal(F)))$. 这些映射与结合、交换、单位及全部高阶同伦相容, 但不要求为等价. 参见 @Lur17[推论 7.3.2.7].

  特别地, *整体函数环谱*
  $ B:=Gamma(cal(F),cal(O)_(cal(F))) in CAlg_Lambda $
  是交换 $Lambda$-代数, 而每个 $Gamma(cal(F),M)$ 都自然是 $B$-模. 直观上, 整体函数可以乘整体截面; 下一节的杯积就是按次数读出这份乘法.
] <prop-qcoh-global-monoidal>

#proofsketch[
  对张量积映射, 先拉回左边, 用 $p^*$ 的张量相容性得到 $p^* Gamma(cal(F),M)⊗p^* Gamma(cal(F),N)$, 再把两条求值映射张量起来, 映到 $M⊗N$. 沿伴随转回去, 就是所需映射. 单位来自 $eta_Lambda$; 相容性由对称幺半伴随保证.
]

#example(title: "伴随一般不互逆")[
  当 $cal(F)=Spec Lambda$ 时, $p^*$ 与 $Gamma$ 都是恒等函子. 对一般的 $Spec A$, 它们则是沿 $Lambda->A$ 的扩张标量与限制标量.

  在非仿射情形, 整体截面甚至可能看不出一个非零拟凝聚模. 例如, 后面#link(<ex-qcoh-projective-line>)[射影直线上的计算]给出
  $ Gamma(PP_K^1,cal(O)(-1)) tilde.eq 0, quad cal(O)(-1) != 0 $
  因而此时求值映射是 $0->cal(O)(-1)$, 并非等价. 要恢复整个拟凝聚模, 仍需它在各块上的数据及粘合方式.
]

== 拟凝聚模的上同调

上一节的整体截面已经是一个模谱. 上同调就是把它按次数读出来. 对普通层, 第零次给出通常的截面, 更高次数还记录粘合、提升与扩张中的信息.

=== 定义与基本性质

#definition(title: "上同调群")[
  设 $cal(F)$ 是可达预层. 沿用 @def-qcoh-global-sections 的整体截面 $Gamma(cal(F),M)$. 对 $M in QCoh(cal(F))$ 与 $i in ZZ$, 定义
  $ H^i (cal(F),M):=pi_(-i) Gamma(cal(F),M) $
  这是一个 $pi_0 Lambda$-模. 负号来自上同调次数约定: 复形的第 $i$ 次上同调对应谱的第 $-i$ 次同伦群, 因而
  $ H^i (cal(F),M[r]) tilde.eq H^(i+r) (cal(F),M) $
  对普通概形及普通拟凝聚层, 它恢复通常的层上同调; 对模复形, 则是通常所说的*超上同调* (hypercohomology).
] <def-qcoh-cohomology>

由整体截面的映射谱描述, 上同调类也可以看成从单位对象出发的移位映射:
$ H^i (cal(F),M) tilde.eq Hom_("h"QCoh(cal(F))) (cal(O)_(cal(F)),M[i]) $

#proposition(title: "长正合列与提升障碍")[
  若 $M'->M->M''$ 是 $QCoh(cal(F))$ 中的纤维序列, 则有长正合列
  $ dots -> H^i (cal(F),M') -> H^i (cal(F),M) -> H^i (cal(F),M'') stretch(->)^delta H^(i+1) (cal(F),M') -> dots $
  这是因为 $p_*$ 保持纤维序列, 再取同伦群即可.

  对普通概形或代数叠上的短正合列 $0->V'->V->V''->0$, 截面 $s in H^0 (cal(F),V'')$ 能提升为 $V$ 的整体截面, 当且仅当 $delta(s)=0$. 所以这里的 $H^1$ 具体承载了*局部能提升, 整体能否提升*的障碍.
]

#remark(title: "Ext 与杯积")[
  记 $Ext_(cal(F))^i (M,N):=Hom_("h"QCoh(cal(F))) (M,N[i])$. 张量–Hom 伴随给出
  $ Ext_(cal(F))^i (M,N) tilde.eq H^i (cal(F),underline(Hom)_(cal(F)) (M,N)) $
  例如, 当 $cal(F)$ 是普通概形或代数叠, $V$ 是普通拟凝聚层时, $H^1 (cal(F),V)$ 可用扩张 $0->V->E->cal(O)_(cal(F))->0$ 的等价类描述.

  把两个从单位对象出发的映射张量起来, 还得到*杯积*
  $ H^a (cal(F),M) ⊗_(pi_0 Lambda) H^b (cal(F),N) -> H^(a+b) (cal(F),M⊗N) $
  特别地, $H^* (cal(F),cal(O)_(cal(F)))$ 是分次交换环, 交换次数 $a,b$ 的元素时出现符号 $(-1)^(a b)$.
]

=== 仿射与开覆盖计算

#proposition(title: "仿射上的计算与消失")[
  对 $X=Spec A$ 和 $A$-模谱 $M$, 整体截面就是 $M$ 本身, 仅限制其系数到 $Lambda$. 因而
  $ H^i (Spec A,M) tilde.eq pi_(-i) M $
  特别地, 若 $X=Spec R$ 是普通仿射概形, $tilde(V)$ 来自普通 $R$-模 $V$, 则
  $ H^0 (X,tilde(V)) tilde.eq V, quad H^i (X,tilde(V))=0 quad (i != 0) $
  这恢复了普通拟凝聚层的仿射消失定理, 见 @Stacks26[Tag 01XB]. 一般拟凝聚模在仿射上仍可有非零的其他次数.
]

#proposition(title: "Čech 复形计算上同调")[
  设 $X$ 是普通拟紧分离概形, 取有限仿射开覆盖 $cal(U)={U_0,dots,U_(r-1)}$. 对普通拟凝聚层 $V$, 所有有限交集仍仿射, 所以 $Gamma(X,V)$ 可用 *Čech 复形*表示:
  $ C^a (cal(U),V):=product_(0<=i_0<dots<i_a<r) H^0 (U_(i_0) ∩ dots ∩ U_(i_a),V) $
  微分是各限制映射的交错和, 第 $j$ 个面带符号 $(-1)^j$. 于是
  $ H^i (X,V) tilde.eq H^i (C^bullet (cal(U),V)) $
  这个复形只在 $0,dots,r-1$ 次有项, 因而 $H^i (X,V)=0$ 对 $i>=r$ 成立. 参见 @Stacks26[Tag 01X8, 引理 30.2.6].
]

#proofsketch[
  先用覆盖及其各重交集组织下降数据, 再取整体截面. 由于这些交集仿射, 普通拟凝聚层在每一块上都没有高阶上同调, 所以只需上述普通 Čech 复形. 更换这样的覆盖得到相同的上同调.
]

对任意概形的两个开集 $X=U ∪ V$, 更一般的 $M in QCoh(X)$ 满足 *Mayer–Vietoris 纤维序列*
$ Gamma(X,M) -> Gamma(U,M) ⊕ Gamma(V,M) -> Gamma(U ∩ V,M) $
这里省略了 $M$ 的限制记号, 第二条箭头是两个限制映射之差. 对普通层 $M$, 取长正合列便知: 交集上的截面给出 $H^1 (X,M)$ 中的一类; 该类为零, 当且仅当这个截面是两边截面之差.

#example(title: "实际计算: 射影直线上的线丛")[
  沿用前面 $PP_K^1$ 的两块覆盖, 线丛 $cal(O)(d)$ 的转移关系为 $e_V=t^d e_U$. 它的整体截面由以下两项复形表示, 两项分别在第 $0,1$ 次:
  $ K[t] ⊕ K[t^(-1)] stretch(->)^((a,b) mapsto a-t^d b) K[t,t^(-1)] $
  所以零次上同调是核, 第一次是余核:
  $ H^1 (PP_K^1,cal(O)(d)) tilde.eq K[t,t^(-1)] slash (K[t]+t^d K[t^(-1)]) $
  右边是向量空间的商, 剩下的单项式满足 $d<j<0$. 零次的核则由 $0<=j<=d$ 的单项式给出, 因而
  $ dim_K H^0 (PP_K^1,cal(O)(d))=max(d+1,0), quad dim_K H^1 (PP_K^1,cal(O)(d))=max(-d-1,0) $
  例如 $H^1 (PP_K^1,cal(O)(-2)) tilde.eq K$, 可由 $t^(-1)$ 的类生成; 所有 $i>=2$ 的上同调都为零.
] <ex-qcoh-projective-line>

=== 叠上的下降与群上同调

对代数叠 $cal(X)$ 取光滑满射图册 $U->cal(X)$, 令 $U_a$ 为其 Čech 神经, $M_a$ 为 $M$ 在 $U_a$ 上的拉回. 拟凝聚模的下降及单位对象的相容性给出
$ Gamma(cal(X),M) tilde.eq varprojlim([a] in Delta) Gamma(U_a,M_a) $
右边也称为*全体化* (totalization), 记作 $op("Tot")$. 这里在模谱中取极限, 因而保留了各层间全部相容同伦. 各层若为代数空间, 可再用平展仿射覆盖计算. 参见 @Lur11DAG8[命题 2.7.14].

对普通拟凝聚层 $V$, 这给出第一象限的下降谱序列
$ E_1^(a,b)=H^b (U_a,V_a) ==> H^(a+b) (cal(X),V) $
第一条微分仍是面映射的交错和. 谱序列的极限页给出目标上同调的一个滤过及其相邻商. 若每个 $U_a$ 都仿射, 就只需计算 $H^0 (U_bullet,V_bullet)$ 的上链复形. 参见 @Stacks26[Tag 0784].

#example(title: "分类叠: 取不变量也有上同调")[
  设 $G$ 是域 $K$ 上的光滑仿射群, $V$ 是代数表示, 也视作 $B G$ 上的普通拟凝聚层. 则
  $ H^0 (B G,V)=V^G $
  高阶上同调计算取不变量的右导出函子. 图册 $Spec K->B G$ 的各层是 $G^a$, 因而得到通常的代数群上同调复形.

  - 对有限常群 $G$, 这就是群上同调 $H^i (B G,V) tilde.eq Ext_(K[G])^i (K,V)$. 若 $|G|$ 在 $K$ 中可逆, 用平均算子可知取不变量正合, 所以 $i>0$ 时全部消失.
  - 若 $"char" K=p>0$, $G=C_p$, 则对平凡表示 $K$, 有 $H^1 (B C_p,K) tilde.eq Hom(C_p,K^+) tilde.eq K$. 这里一余循环就是到加法群的同态, 一余边界为零.
  - 对 $G=bb(G)_m$, 表示写成 $V=⊕_(d in ZZ) V_d$, 取不变量就是取 $V_0$. 这也是正合函子, 因而 $H^i (B bb(G)_m,V)=0$ 对 $i>0$ 成立.

  所以, 叠的上同调还会记录*自同构群作用带来的高阶信息*. 上述计算都使用拟凝聚系数.
]

=== 前推、Leray 谱序列与有限性

由前推的复合性, 对任意可达预层态射 $f:cal(F)->cal(G)$ 都有
$ Gamma(cal(G),f_* M) tilde.eq Gamma(cal(F),M) $
伴随的单位 $N->f_* f^* N$ 则给出自然拉回映射
$ H^i (cal(G),N) -> H^i (cal(F),f^* N) $

#proposition(title: "高阶前推与 Leray 谱序列")[
  设 $f:X->Y$ 是普通概形之间的拟紧拟分离态射, $V$ 是普通拟凝聚层. 记 $cal(H)^b$ 为标准 $t$-结构的第 $b$ 个上同调层, 即 $pi_(-b)^t$, 定义
  $ R^b f_* V:=cal(H)^b (f_* V) $
  它们是 $Y$ 上的普通拟凝聚层, 并有第一象限的 *Leray 谱序列*
  $ E_2^(a,b)=H^a (Y,R^b f_* V) ==> H^(a+b) (X,V) $
  可以把它理解为先算沿 $f$ 的上同调, 再在 $Y$ 上算上同调. 若 $f$ 仿射, 则 $R^b f_* V=0$ 对 $b>0$ 成立, 从而 $H^i (Y,R^0 f_* V) tilde.eq H^i (X,V)$. 参见 @Stacks26[Tags 01XH, 01XC, 0782].
]

#remark(title: "上同调层与上同调群")[
  $cal(H)^b (M)$ 仍是底空间上的层, $H^b (X,M)$ 则是整体得到的模. 对普通概形 $X$ 上的上同调次数有下界的复形 $M$, 两者通过超上同调谱序列联系:
  $ E_2^(a,b)=H^a (X,cal(H)^b (M)) ==> H^(a+b) (X,M) $
  Leray 谱序列就是把这一过程用于 $f_* V$, 再使用整体截面与前推的复合公式.
]

#proposition(title: "经典情形中的三个常用工具")[
  以下结论针对普通概形.
  - *有限性.* 若 $R$ Noetherian, $X->Spec R$ 紧合, $V$ 凝聚, 则每个 $H^i (X,V)$ 都是有限生成 $R$-模. 特别地, 域上的紧合概形给出有限维上同调. 参见 @Stacks26[Tag 02O3].
  - *Serre 消失.* 若上述 $X slash R$ 射影, 选定相对极丰沛线丛 $cal(L)$, 则存在依赖于 $V$ 的 $d_0$, 使
    $ H^i (X,V⊗cal(L)^(⊗d))=0 quad (i>0, d>=d_0) $
    参见 @Stacks26[Tag 01XO].
  - *平坦换系数.* 若 $X slash R$ 拟紧分离, $R->R'$ 平坦, $V$ 拟凝聚, 则
    $ H^i (X,V)⊗_R R' tilde.eq H^i (X_(R'),V_(R')) $
    用有限仿射覆盖的 Čech 复形计算即可: 各项随平坦换系数拉回, 平坦张量积又与取上同调交换.
]

实际计算时, 先选方便的仿射覆盖或图册, 写出限制映射, 再计算相应复形的核与像. 遇到短正合列就用长正合列, 遇到态射就用前推和 Leray 谱序列; 紧合性与 Serre 消失则控制答案的有限性和可能出现的次数.

== 向量丛与线丛

向量丛是局部最简单的拟凝聚模: 选好局部基以后, 它就是若干份单位模. 线丛则只需一个基向量. 以下仍对一般的可达预层 $cal(F):CAlg_Lambda->Ani$ 讨论, 并沿用测试点上的记号 $E_(A,x) tilde.eq x^* E$.

=== 局部自由条件

#definition(title: "环谱上的局部自由模")[
  (回顾 @def-spectral-localization) 称 $A$-模 $P$ *局部自由, 秩为 $r$*, 若有有限多个 $f_j in pi_0 A$ 生成单位理想, 使
  $ A[f_j^(-1)]⊗_A P tilde.eq A[f_j^(-1)]^(⊕r) $
  这里 $r>=0$. 这些局部化对应普通概形 $Spec(pi_0 A)$ 的主开覆盖. 换句话说, *局部选基以后, $P$ 就是 $r$ 份 $A$*. 这个定义直接使用环谱局部化, 也适用于本章的非连通测试代数. 连通情形参见 @Lur11DAG8[定义 2.7.29, 注 2.7.30].
] <def-locally-free-spectral-module>

#definition(title: "向量丛与线丛")[
  称 $E in QCoh(cal(F))$ 为*秩 $r$ 的向量丛* (vector bundle), 若对每个测试点 $(A,x)$, $E_(A,x)$ 都是秩 $r$ 的局部自由 $A$-模. 秩 $1$ 的向量丛称为*线丛* (line bundle).

  本节先固定秩; 不固定秩时, 允许秩在局部常值地变化. 将秩 $r$ 的向量丛及其等价组成的生象记为 $cat("Vect")_r (cal(F))$. 它保留自同构及其高阶同伦. 参见 @Lur11DAG8[第 2.7 节末].
] <def-qcoh-vector-line-bundles>

#remark(title: "怎样回到普通向量丛")[
  若 $A=H R$ 来自普通环, 上述模恰好是 $H P_0$, 其中 $P_0$ 是秩 $r$ 的有限投射 $R$-模. 因而在普通概形 $X$ 上, 向量丛就是普通的有限局部自由 $cal(O)_X$-模层, 属于 $QCoh(X)$ 的心; 普通 Artin 叠上可在光滑图册上检验这一点.

  对一般环谱, 局部平凡模 $A^(⊕r)$ 自身就可能有高阶同伦, 且 $pi_i (A^(⊕r)) tilde.eq (pi_i A)^(⊕r)$. 所以这里的秩数的是*单位模的份数*. 在普通几何点 $x:Spec K->X$ 上, 则恢复熟悉的 $r$ 维向量空间. 参见 @Stacks26[Tags 01I6, 00NX].
]

=== 拉回、下降与对偶

#proposition(title: "向量丛可以拉回和粘合")[
  任意预层态射 $f:cal(F)->cal(G)$ 的拉回保持向量丛及其秩, 特别保持线丛. 这是因为扩张标量把 $A^(⊕r)$ 送到 $B^(⊕r)$, 并把主开覆盖拉成主开覆盖.

  向量丛满足 Zariski 下降. 若 $cal(F)$ 是 Zariski 层, $U->cal(F)$ 是 Zariski 覆盖, $U_bullet$ 是其 Čech 神经, 则在生象中有
  $ cat("Vect")_r (cal(F)) tilde.eq varprojlim([n] in Delta) cat("Vect")_r (U_n) $
  在连通环谱的测试范畴中, 同样有 fpqc 下降. 因而对普通 Artin 叠, 可以沿光滑图册粘合向量丛. 证明就是先下降拟凝聚模, 再用局部自由性可平坦局部检验. 参见 @Lur11DAG8[命题 2.7.14, 2.7.31].
] <prop-vector-bundle-descent>

#proposition(title: "有限维线性代数仍然成立")[
  若 $E,F$ 分别是秩 $r,s$ 的向量丛, 则 $E⊕F$ 与 $E⊗F$ 仍是向量丛, 秩分别为 $r+s$ 与 $r s$. 定义*对偶向量丛*
  $ E^or:=underline(Hom)_(cal(F)) (E,cal(O)_(cal(F))) $
  它仍有秩 $r$, 并且对每个 $M in QCoh(cal(F))$ 有
  $ E^(or or) tilde.eq E, quad underline(Hom)_(cal(F)) (E,M) tilde.eq E^or⊗M $
  这些构造与任意拉回相容. 特别地,
  $ f^* (E^or) tilde.eq (f^* E)^or, quad Ext_(cal(F))^i (E,M) tilde.eq H^i (cal(F),E^or⊗M) $
  所以从向量丛出发的映射与扩张, 可以转成张量后取上同调.
] <prop-vector-bundle-duality>

#proofsketch[
  局部把 $E$ 写成 $A^(⊕r)$, 内部 Hom 就是 $r$ 份目标模, 因而上述公式都是有限自由模的计算. 对偶与求值映射在换基下相容, 所以能粘合. 这也说明向量丛是可对偶对象. 参见 @Lur11DAG8[命题 2.7.28].
]

=== 线丛、扭曲与自同构

#proposition(title: "线丛可以张量相消")[
  对线丛 $L$, 求值映射给出等价
  $ L^or⊗L tilde.eq cal(O)_(cal(F)) $
  因而 $M mapsto M⊗L$ 是 $QCoh(cal(F))$ 的自等价, 逆为张量 $L^or$. 这个操作称为用 $L$ *扭曲* $M$. 对 $n<0$, 约定 $L^(⊗n):=(L^or)^(⊗(-n))$, 而 $L^(⊗0):=cal(O)_(cal(F))$.

  记线丛及其等价组成的 Picard 生象为
  $ underline(Pic)(cal(F)):=cat("Vect")_1 (cal(F)), quad Pic(cal(F)):=pi_0 underline(Pic)(cal(F)) $
  张量积、单位线丛和对偶使它成为 Picard 无穷群胚; 取连通分支后, $Pic(cal(F))$ 是 Abel群. 普通概形上, 这就是前面的 Picard 群. 参见 @Stacks26[Tag 01CR].
] <prop-qcoh-lines-picard>

#remark(title: "线丛与一般可逆对象")[
  在稳定范畴中, 称 $M$ *张量可逆*, 是指存在 $N$ 使 $M⊗N tilde.eq cal(O)_(cal(F))$. 线丛都可逆, 但这个条件允许更多对象: 对非空普通概形 $X$,
  $ cal(O)_X [1]⊗cal(O)_X [-1] tilde.eq cal(O)_X $
  而 $cal(O)_X [1]$ 不在心中, 所以不是这里定义的线丛. 因此本节的 $underline(Pic)$ 专指秩一向量丛; 若研究全部张量可逆对象, 会得到更大的 Picard 生象.
]

#proposition(title: "线丛的自同构是可逆整体函数")[
  对交换环谱 $B$, 定义 $GL_1(B)$ 为 $Omega^oo B$ 中对应于 $(pi_0 B)^times$ 的那些连通分支; 乘法使它成为群生象. 对任意线丛 $L$, 有
  $ Aut_(QCoh(cal(F))) (L) tilde.eq GL_1(Gamma(cal(F),cal(O)_(cal(F)))) $
  这是因为 $underline(Hom)_(cal(F)) (L,L) tilde.eq cal(O)_(cal(F))$, 而自同构正是其中可逆的映射. 取连通分支, 得到 $(H^0 (cal(F),cal(O)_(cal(F))))^times$.

  特别地, 普通概形上线丛的自同构就是乘以可逆整体函数. 一般环谱则还保留高阶自同伦: 在单位元处, $pi_i GL_1(B) tilde.eq pi_i B$ 对 $i>0$ 成立.
] <prop-line-bundle-automorphisms>

=== 标架与分类预层

对环谱 $A$, 定义 $GL_r (A):=Aut_(Mod_A) (A^(⊕r))$. 它由可逆的 $A$-线性换基组成; $pi_0 GL_r (A) tilde.eq GL_r (pi_0 A)$, 但整个 $GL_r (A)$ 可以有高阶同伦. 普通环 $R$ 则给出离散群 $GL_r (H R) tilde.eq GL_r (R)$.

#definition(title: "向量丛的分类预层")[
  定义
  $ (B GL_r)(A):=cat("Vect")_r (Spec A) $
  沿 $A->B$ 的映射由扩张标量给出. 由下降, 这是 Zariski 层. 它也可以从只有对象 $A^(⊕r)$、自同构为 $GL_r (A)$ 的无穷群胚出发, 对所得预层作 Zariski 层化得到: 层化加入了局部自由模的各种粘合.

  对任意可达预层 $cal(F)$, 有自然等价
  $ cat("Vect")_r (cal(F)) tilde.eq Map_(PSh) (cal(F),B GL_r) $
  右边表示预层之间自然变换的生象. 秩一时记 $bb(G)_m:=GL_1$, 从而 $underline(Pic)(cal(F)) tilde.eq Map_(PSh) (cal(F),B bb(G)_m)$. 限制到普通环, 就恢复前面的分类叠.
] <def-spectral-bundle-classifier>

#proofsketch[
  给定 $E$, 在每个 $(A,x)$ 处送出 $E_(A,x)$, 就得到 $cal(F)->B GL_r$. 反过来, 一个这样的自然变换给出各测试点上的局部自由模及其全部换基相容性, 正好组成 $E$.

  更直观地说, $E$ 在 $(A,x)$ 上的*标架*是等价 $A^(⊕r) stretch(->)^tilde E_(A,x)$. 换基群 $GL_r (A)$ 通过预合成作用于标架. 当 $cal(F)$ 是层时, 这些标架组成 $cal(F)$ 上 Zariski 局部平凡的 $GL_r$-挠子. 因而向量丛的分类记录了*局部基怎样粘合*, 也保留换基产生的自同构.
]

=== 几何图像与普通情形的行列式

#remark(title: "把模看成一族向量")[
  若希望看到向量丛的总空间, 可以直接定义预层 $bb(V)(E)->cal(F)$: 它在 $A$ 上的对象是一个 $x in cal(F)(A)$, 连同一个 $A$-模映射 $s:A->E_(A,x)$, 并保留全部同伦. 在 $E$ 平凡的地方, 每条纤维就是 $(Omega^oo A)^r$; 普通环上恢复 $A^r$.

  一个截面就是在所有测试点上相容地选择向量. 因而其截面生象为
  $ Map_(slash cal(F)) (cal(F),bb(V)(E)) tilde.eq Omega^oo U_Lambda Gamma(cal(F),E) $
  左边是在 $cal(F)$ 上取态射, $U_Lambda$ 忘却模的系数. 当 $cal(F)=X$ 是普通概形, 并限制到普通环测试时, 这恢复经典的总空间 $Spec_X (op("Sym")_(cal(O)_X) (E^or))$, 普通截面组成 $H^0 (X,E)$.
]

#proposition(title: "普通向量丛的行列式")[
  设 $X$ 是普通概形或普通 Artin 叠, $E$ 是秩 $r$ 的向量丛. 用普通局部自由模的外幂定义*行列式线丛*
  $ det E:=and.big^r E $
  若 $E$ 的转移矩阵是 $g_(i j)$, 则 $det E$ 的转移函数就是 $det(g_(i j))$. 因而行列式与拉回相容, 并有
  $ det(E⊕F) tilde.eq det E⊗det F, quad det(E^or) tilde.eq (det E)^or $
  对普通向量丛的短正合列 $0->E'->E->E''->0$, 还有 $det E tilde.eq det E'⊗det E''$. 这些公式都可局部选基验证, 再由下降粘合. 参见 @Stacks26[Tag 0B37].
] <prop-classical-vector-determinant>

#example(title: "两个熟悉的用法")[
  - 在 $PP_K^1$ 上, $cal(O)(d)$ 的转移函数是 $t^d$. 张量积使转移函数相乘, 所以 $cal(O)(a)⊗cal(O)(b) tilde.eq cal(O)(a+b)$, 对偶则为 $cal(O)(-d)$.
  - 设 $G$ 是域 $K$ 上的光滑仿射群概形. 在普通分类叠 $B G$ 上, 向量丛就是 $G$ 的有限维代数表示. 直和、张量积、对偶与行列式分别成为表示的同名运算; 线丛则是一维表示, 即特征标 $G->bb(G)_m$.
]

实际使用时, 先在覆盖上把向量丛写成自由模, 把问题变成矩阵计算; 换基相容性负责粘合. 要算映射就用对偶与整体截面, 要改变系数或参数就拉回, 要记录线丛的扭曲就使用张量积与 Picard 群.
