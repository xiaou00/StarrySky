#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *

#show: doc => conf(easy: true, doc,)

= Lie 代数 / Lie Algebras <chap-lie-algebras>

Lie 代数描述无穷小对称性. 本章先用算筹组织括号及其高阶相容性, 再研究表示与扩张, 最后用泛包络代数把它们接到结合代数与 Hopf 代数上.

一般定义取在交换环谱 $R in CAlg(Sp)$ 的模范畴中. 普通交换环记作 $A$, 并记 $cal(D)(A)=Mod_(H A)$. 张量积默认是导出的; 写成复形时使用上同调次数, $d$ 的次数为 $1$. 域上的理论作为特例处理, 所需的特征与维数假设另行说明.

== Lie 算筹与 Lie 代数

=== 算筹的定义

Lie 括号的公理含有运算的和与负号, 所以需要模值或谱值的算筹. 先定义算筹的 Koszul 对偶, 再用它构造 Lie 算筹.

#definition(title: [算筹的杠构造])[
  设 $R$ 是交换环谱. 一个 $R$-模值算筹 $cal(O)$ 称为*约化的*, 若 $cal(O)(0)=0$, 且单位 $R->cal(O)(1)$ 是等价. 令 $bold(1)_R$ 为恒等算筹, 只有一输入分量 $R$ 非零. 约化算筹有典范增广
  $ epsilon:cal(O)->bold(1)_R $
  它在一输入部分为恒等, 在其余部分为零.

  记 $compose$ 为对称序列的代入复合, 即把内层运算代入外层运算. 定义单纯对象
  $ cat("Bar")_q (bold(1)_R,cal(O),bold(1)_R)
    :=bold(1)_R compose cal(O)^(compose q) compose bold(1)_R $
  其中零重代入为 $bold(1)_R$. 面映射复合相邻两层运算, 两端使用增广; 退化映射插入单位运算. 其几何实现称为*算筹的杠构造*:
  $ B_R (cal(O)):=varinjlim([q] in Delta^op)
    cat("Bar")_q (bold(1)_R,cal(O),bold(1)_R) $
  也记作 $cat("Bar")(bold(1)_R,cal(O),bold(1)_R)$. 余极限逐元数计算, 所有构造均按导出意义理解.
]

单纯次数记录运算的层数. 将这些层看成一棵运算树, 切开树就把一个整体分解为外层运算与若干内层运算. 这些分解使 $B_R (cal(O))$ 成为余算筹, 带有相容的余复合
$ B_R (cal(O))(n_1+ dots+n_r)
  ->B_R (cal(O))(r) times.o_R B_R (cal(O))(n_1)
    times.o_R dots times.o_R B_R (cal(O))(n_r) $

#definition(title: [算筹的 Koszul 对偶])[
  对约化 $R$-模值算筹 $cal(O)$, 定义其*导出 Koszul 对偶*为
  $ op("K")_R (cal(O)):=B_R (cal(O))^or, quad
    op("K")_R (cal(O))(n)
      :=op("Hom")_R (B_R (cal(O))(n),R) $
  上标 $or$ 表示逐元数取内部 $R$-模对偶. 余复合的对偶给出 $op("K")_R (cal(O))$ 的算筹复合. 在谱中取 $R=bb(S)$, 简记为 $op("K")(cal(O))$.
] <def-operadic-koszul-dual>

具体地, 对偶总有自然映射 $M^or times.o_R N^or->(M times.o_R N)^or$. 把它与余复合的对偶相接, 就得到
$ op("K")_R (cal(O))(r) times.o_R op("K")_R (cal(O))(n_1)
  times.o_R dots times.o_R op("K")_R (cal(O))(n_r)
  ->op("K")_R (cal(O))(n_1+ dots+n_r) $
因此这个定义不要求各分量完美. 当 $B_R (cal(O))$ 的各分量完美时, 对偶与有限张量积之间的自然映射进一步成为等价.

Koszul 对偶反转态射方向: $cal(O)->cal(P)$ 诱导 $op("K")_R (cal(P))->op("K")_R (cal(O))$. 这里的 $op("K")$ 专指这一对偶构造, 与代数 $K$-理论无关. 谱中的定义见 @Chi12Bar[定义 4.2--4.3].

#definition(title: [Lie 算筹])[
  令 $Comm^"nu"$ 为没有零输入运算的交换谱算筹, 即零输入分量为 $0$, 每个正输入分量为球谱 $bb(S)$. 它是约化算筹. 依照 @def-operadic-koszul-dual, 取其 Koszul 对偶
  $ cal(L):=op("K")(Comm^"nu")
    =cat("Bar")(bold(1),Comm^"nu",bold(1))^or $
  这里 $bold(1)=bold(1)_(bb(S))$,杠构造的各分量都是有限谱.

  本章采用括号次数为零的规范, 定义
  $ Lie^times.o:=op("s") cal(L), quad
    Lie(n):=op("End")_(Sp) (bb(S)^(-1))(n) smash cal(L)(n) $
  其中 $op("s")$ 是算筹悬挂, 自同态算筹的分量为
  $ op("End")_(Sp) (bb(S)^(-1))(n)
    =op("Hom")_(Sp) ((bb(S)^(-1))^(smash n),bb(S)^(-1)) $
  它的底层谱是 $bb(S)^(n-1)$, 置换作用由输入的置换给出. 上标 $times.o$ 表示整个算筹结构.

  对任意交换环谱 $R$, 沿 $Sp->Mod_R$ 扩张标量, 得到
  $ Lie_R^times.o:=R smash Lie^times.o, quad Lie_R (n)=R smash Lie(n) $
  特别有 $Lie_R (0)=0$ 与 $Lie_R (1)=R$.
] <def-lie-operad>

谱中通常也把 $cal(L)$ 本身称作谱 Lie 算筹; 它与这里的规范相差一次算筹悬挂. 明确这个约定, 是为了让普通环上的二元括号仍然具有次数零. 该谱算筹的构造与规范见 @ABH25[第 1--2 节].

在普通交换环 $A$ 上, $H A smash Lie^times.o$ 恢复经典的线性 Lie 算筹. 其 $n$ 元运算模 $Lie_A (n)$ 由每个输入恰好出现一次的形式括号表达式生成, 模去
$ [x,y]+[y,x]=0, quad
  [x,[y,z]]+[y,[z,x]]+[z,[x,y]]=0 $
及其代入. 置换重标输入, 复合则把表达式代入表达式. 例如二元部分由 $[x_1,x_2]$ 生成, 换位作用为 $-1$. 这也解释了 #chapter-ref(<chap-hopf-algebras>) 的算筹语言如何记录线性关系.

#definition(title: [高阶 Lie 代数])[
  设 $cal(C)$ 是可呈示的稳定 $R$-线性对称幺半无穷范畴, 张量积分别保持余极限. 一个 *Lie 代数*是 $Lie_R^times.o$ 在 $cal(C)$ 中的代数, 记其无穷范畴为
  $ LieAlg(cal(C)):=Alg_(Lie_R^times.o) (cal(C)) $
  具体地, 它由对象 $frak(g)$ 及相容的运算
  $ Lie_R (n) times.o_R frak(g)^(times.o n)->frak(g) $
  给出, 其中第一项通过 $cal(C)$ 的 $R$-线性结构作用. 相容性包含代入, 置换, 单位和全部高阶同伦.

  等价地, 这是从 $Lie_R^times.o$ 到 $frak(g)$ 的 $R$-线性自同态算筹的态射. *Lie 态射*保持这些运算及其全部相容性; 它们组成映射生象
  $ Map_(LieAlg(cal(C))) (frak(g),frak(h)) $
  特别记 $LieAlg_R:=LieAlg(Mod_R)$; 对普通环 $A$, 简记 $LieAlg_A:=LieAlg(cal(D)(A))$.
] <def-higher-lie-algebra>

例如 $R=bb(S)$ 给出谱中的 Lie 对象, $R=H ZZ$ 给出整数复形中的 Lie 对象, $R=H(QQ[t])$ 给出随参数变化的 Lie 对象. 这些定义均不要求底环是域.

普通 $A$-Lie 代数则是带 $A$-双线性括号的 $A$-模, 满足 $[x,x]=0$ 与 Jacobi 恒等式. 当 $2$ 可逆时, 这恰好是 $LieAlg_A$ 的零次对象. 在 $2$ 不可逆时, 交替性不能由 $[x,y]+[y,x]=0$ 推出, 须保留这个额外要求; 不能把所有正特征的 Lie 型结构混同.

=== dg 模型与自由对象

#proposition(title: [dg Lie 模型])[
  设 $A$ 是交换 $QQ$-代数, 不要求是域. $LieAlg_A$ 可以由 dg Lie 代数及其拟同构的无穷局部化计算. 对齐次元素 $x,y,z$, 一个严格 dg Lie 模型满足
  $ [x,y]=-(-1)^(abs(x) abs(y)) [y,x] $
  $ [x,[y,z]]=[[x,y],z]+(-1)^(abs(x) abs(y)) [y,[x,z]] $
  $ d[x,y]=[d x,y]+(-1)^(abs(x)) [x,d y] $
  这里 $abs(x)$ 表示次数. 算筹的余纤维替换也给出 $L_oo$ 模型: 其运算 $ell_n$ 的次数为 $2-n$, $ell_1=d$, $ell_2$ 是括号, $ell_3$ 给出 Jacobi 恒等式的同伦, 更高运算记录随后的相容性.
]

#proof[
  在 $QQ$-代数上, 有限对称群的平均算子存在, 取余不变量正合. 因而可以沿 dg 算筹的余纤维替换作整化. 将拟同构取逆后, 严格模型与 $L_oo$ 模型给出同一个无穷范畴. 域上的构造参见 @LurDAGX[第 2.1 节]; 同一论证使用 $A$ 上的投射模型, 并不需要所有 $A$-模都是自由模.
]

这里要求的是 $QQ$-线性, 不是仅仅要求环的特征为零. 例如 $ZZ$ 中不能除以 $n!$, 所以一般底环仍以算筹的同伦定义为准. 以后在特征零域 $k$ 上, 将集中在零次的对象组成的普通范畴记作 $LieAlg_k^"disc"$.

#proposition(title: [自由 Lie 代数与极限])[
  对任意交换环谱 $R$, 忘却函子 $op("oblv"):LieAlg_R->Mod_R$ 有左伴随
  $ op("Free")_Lie (V)
    =plus.o.big_(n>=1) (Lie_R (n) times.o_R V^(times.o_R n))_(h Sigma_n) $
  其中 $h Sigma_n$ 表示同伦余不变量. 因而
  $ Map_(LieAlg_R) (op("Free")_Lie (V),frak(g))
    tilde.eq Map_(Mod_R) (V,op("oblv")(frak(g))) $
  此外, $op("oblv")$ 创造极限, 检测等价, 并保持筛余极限.
]

#proof[
  自由对象的每一项收集 $n$ 个输入上的 Lie 运算, 取同伦余不变量将输入的不同标号相容地识别. 代入给出它的 Lie 结构; 向 $frak(g)$ 的映射由生成元上的映射唯一地同伦确定.

  对一个 Lie 对象图式, 底层极限的投影把各个多元运算拉回到极限上, 给出极限 Lie 结构. 等价由底层对象检测. 筛余极限则与有限张量积相容, 因而也在底层计算.
]

例如 $fib(frak(g)->frak(h))$ 应当在 Lie 无穷范畴中取, 其底层是对应模的同伦纤维. 余极限一般不是底层模的余极限. 对 $R->S$, 对称幺半函子 $S times.o_R-$ 还给出标量扩张
$ LieAlg_R->LieAlg_S, quad frak(g) mapsto S times.o_R frak(g) $
它与自由 Lie 构造相容, 因为上述张量积, 直和与同伦余不变量都可与标量扩张交换.

=== 括号与自同态

#proposition(title: [交换子与自同态])[
  结合算筹与 Lie 算筹之间有态射
  $ Lie^times.o->Assoc^times.o, quad [-,-] mapsto mu-mu compose tau $
  这里 $Assoc^times.o$ 表示含幺结合谱算筹. 扩张标量后, 每个 $B in Alg(cal(C))$ 都给出 Lie 对象 $B^"Lie"$.

  特别地, 内部自同态对象的复合给出
  $ gl(V):=op("End")_(cal(C)) (V)^"Lie" $
  这包括任意 $R$-模上的自同态, 不要求它有限自由.
]

#proof[
  谱算筹态射由 $Assoc^"nu"->Comm^"nu"$ 的 Koszul 对偶及悬挂得到, 再包含到含幺结合算筹, 见 @ABH25[定义 5.7]. 扩张标量保留这个态射. 在 $QQ$-线性的严格 dg 模型中, 它给出的交换子为
  $ [a,b]=a b-(-1)^(abs(a) abs(b)) b a $
  展开三重括号, 每个三重乘积出现两次且符号相反, 所以满足分次 Jacobi 恒等式. 谱算筹态射保留了元素公式之外的全部高阶相容性.
]

在普通 $A$-Lie 代数中, 括号给出伴随表示 $ad:frak(g)->gl_A (frak(g))$, 并满足
$ ad_x [y,z]=[ad_x y,z]+[y,ad_x z], quad
  [ad_x,ad_y]=ad_([x,y]) $
例如 $A^n$ 给出矩阵 Lie 代数 $gl_n (A)$. 取 $A=ZZ$, 得到整数矩阵的交换子 Lie 代数; 取 $A=QQ[t]$, 得到一个非域上的例子.

== 表示与扩张

=== 表示的无穷范畴

#definition(title: [Lie 模])[
  给 $Lie_R^times.o$ 增加一个模颜色 $m$, 原来的 Lie 颜色记为 $l$. 输出为 $l$ 的运算只有全部输入为 $l$ 时才非零; 输出为 $m$ 的运算只有恰好一个输入为 $m$ 时才非零. 两种情况下的运算模均由相应的 $Lie_R (n)$ 给出, 代入沿用 Lie 算筹的代入. 记这个双色算筹为 $cat("LieMod")_R^times.o$.

  固定 Lie 对象 $frak(g)$ 后, 其*表示无穷范畴*定义为
  $ Rep_R (frak(g)):=Alg_(cat("LieMod")_R^times.o) (Mod_R)
    times_(LieAlg_R) {frak(g)} $
  底环明确时简记 $Rep(frak(g))$. Lie 颜色已经取值为 $frak(g)$, 只让模颜色及其作用变化. 取模对象也为 $frak(g)$, 并沿用原有运算, 就得到伴随模.
] <def-lie-representation>

在交换 $QQ$-代数 $A$ 上的严格 dg 模型中, 作用 $frak(g) times.o_A V->V$ 满足
$ [x,y] v=x(y v)-(-1)^(abs(x) abs(y)) y(x v) $
并与微分相容. 此时, 表示结构等价于 Lie 态射 $frak(g)->gl(V)$, 伴随模对应于 $ad:frak(g)->gl(frak(g))$. 对一般环谱, 以上述双色算筹的定义为准.

#proposition(title: [表示的稳定性与张量积])[
  对任意交换环谱 $R$, $Rep_R (frak(g))$ 是可呈示的稳定无穷范畴, 纤维与余纤维在底层 $Mod_R$ 中计算.

  在 $QQ$-线性语境中, 它还有通常的对称幺半结构, 张量积的底层是 $V times.o_R W$, 单位为平凡表示 $R$. 对普通交换 $QQ$-代数的 dg 模型,
  $ x(v times.o w)=(x v) times.o w
    +(-1)^(abs(x) abs(v)) v times.o (x w) $
  底层完美的表示可对偶, 对偶的作用满足
  $ (x f)(v)=-(-1)^(abs(x) abs(f)) f(x v) $
]

#proof[
  算筹中的模运算对模变量线性, 所以在底层取纤维或余纤维后仍有诱导作用. 模的自由构造与忘却函子给出可呈示性. $QQ$-线性时, 也可使用 @prop-lie-modules-enveloping 的包络代数模描述.

  将张量积上的作用写作 $rho_V (x) times.o id+id times.o rho_W (x)$, 中间移动齐次元素时出现所写符号. 两个因子的交叉交换子相消, 剩下各自的表示恒等式. 这与 @prop-enveloping-hopf 的余交换 Hopf 结构给出的全部相容性一致. 对偶公式则恰好使求值与余求值保持作用.
]

特别地, 对特征零域 $k$ 上的离散 $frak(g)$, $Rep(frak(g))$ 的标准 $t$-结构的心是普通 $frak(g)$-模范畴. 子表示与商表示在这个心中定义; 不可约表示指非零且没有非平凡子对象的离散表示. 有限维时, 对 $W subset V$ 有正合列
$ 0->(V/W)^or->V^or->W^or->0 $
所以商表示的对偶成为子表示. 这不表示任意无限维表示都在幺半意义下可对偶.

在一般普通环上, 对应的有限性条件是有限投射性, 但子模与商模未必仍有限投射. 因而不能照搬域上的对偶正合列.

=== 理想与商

下面的子对象与商先在普通交换环 $A$ 上的经典 Lie 代数范畴中定义. 这些构造不需要域的假设.

#definition(title: [子代数与理想])[
  $A$-子模 $frak(h) subset frak(g)$ 若对括号封闭, 就是子 Lie 代数. $A$-子模 $frak(i) subset frak(g)$ 若满足
  $ [frak(g),frak(i)] subset frak(i) $
  就是理想. 等价地, 理想是伴随表示的子表示. 一个子集生成的子代数是包含它且对所有 Lie 运算封闭的最小 $A$-子模.

  对理想 $frak(i)$, 定义商 Lie 代数
  $ [x+frak(i),y+frak(i)]=[x,y]+frak(i) $
  它使所有将 $frak(i)$ 送到零的 Lie 态射唯一地经过 $frak(g)\/frak(i)$.
]

#proposition(title: [核与第一同构定理])[
  对离散 Lie 态射 $f:frak(g)->frak(h)$, $ker(f)$ 是理想, $im(f)$ 是子代数, 并且
  $ frak(g)\/ker(f) tilde.eq im(f) $
  每个理想都是相应商映射的核, 但一般子代数未必是核.
]

#proof[
  $f([x,u])=[f(x),f(u)]$ 说明核对伴随作用稳定, 像对括号封闭. $A$-模同构 $x+ker(f) mapsto f(x)$ 保持括号, 所以是 Lie 同构. 核必为理想, 而例如 $QQ E_(12) subset sl_2(QQ)$ 是子代数却不是理想.
]

在高阶语境中, 核由同伦纤维代替, 商则用相应的同伦泛性质定义. 尤其不能把 $frak(g) coprod_(frak(i)) 0$ 的底层对象直接认作普通商复形; 离散理想的普通商是在离散范畴中作的商.

#proposition(title: [理想的运算])[
  若 $frak(i),frak(j)$ 是理想, 则和, 交及括号像 $[frak(i),frak(j)]$ 都是理想, 且
  $ [frak(i),frak(j)] subset frak(i) inter frak(j) subset frak(i)+frak(j) $
]

#proof[
  和与交对伴随作用稳定. 对括号像, Jacobi 恒等式给出
  $ [x,[u,v]]=[[x,u],v]+[u,[x,v]] in [frak(i),frak(j)] $
  包含关系则由两个理想各自的稳定性得到.
]

#definition(title: [中心与 Abel 化])[
  对离散 Lie 对象, 定义
  $ Z(frak(g))=ker(ad)= {x in frak(g) | [x,frak(g)]=0} $
  及
  $ frak(g)^"ab":=frak(g)/[frak(g),frak(g)] $
  后者是括号为零的 Lie 代数, 并满足到任意交换 Lie 代数的映射泛性质. 因而它是普通 Lie 范畴中平凡括号函子的左伴随.

  对子集 $S$ 和子代数 $frak(h)$, 中心化子与正规化子分别为
  $ C_(frak(g)) (S)={x | [x,S]=0}, quad
    N_(frak(g)) (frak(h))={x | [x,frak(h)] subset frak(h)} $
  Jacobi 恒等式说明两者都是子代数, 且 $frak(h)$ 为理想当且仅当 $N_(frak(g)) (frak(h))=frak(g)$.
]

中心解释了伴随表示的局限:
$ frak(g)\/Z(frak(g)) tilde.eq ad(frak(g)) $
所以伴随表示忠实当且仅当中心为零. Ado 定理需要另外构造能够检测中心的有限维表示.

在 $LieAlg_R$ 中, 沿算筹增广定义的平凡结构函子 $op("triv"):Mod_R->LieAlg_R$ 也有左伴随 $op("Ab")^bb(L)$, 由映射生象的伴随关系定义. 对一般对象必须使用这个导出函子, 不能只取普通括号像的商. 在 $QQ$-线性情形, 中心的导出版本可用 @def-lie-cohomology 的伴随表示上同调描述.

=== 导子与分裂扩张

#definition(title: [导子与半直积])[
  在离散情形, 导子是满足
  $ D[x,y]=[D x,y]+[x,D y] $
  的 $A$-线性映射. 它们组成 Lie 代数 $Der_A (frak(g))$, 底环明确时略去下标. 括号为交换子, 内导子组成理想 $op("Inn")(frak(g))=ad(frak(g))$, 外导子为其商.

  若 $rho:frak(g)->Der(frak(h))$ 是 Lie 态射, 半直积 $frak(g) times.l_rho frak(h)$ 的底层为 $frak(g) plus.o frak(h)$, 括号是
  $ [(x,u),(y,v)]=([x,y],[u,v]+rho(x)v-rho(y)u) $
]

#proof[
  展开 $[D,E][x,y]$ 即得导子恒等式, 且
  $ [D,ad_x]=ad_(D x) $
  给出内导子的理想性. 半直积中只需检查混合输入的 Jacobi 恒等式: 一个 $frak(g)$ 输入要求 $rho(x)$ 是导子, 两个 $frak(g)$ 输入要求 $rho$ 保持 Lie 括号.
]

#proposition(title: [分裂扩张与作用])[
  普通 $A$-Lie 代数的带 Lie 截面的短正合列
  $ 0->frak(h)->frak(e)->frak(g)->0 $
  等价于 $frak(g)$ 对 $frak(h)$ 的导子作用. 在给定截面 $s$ 后, 对应等价为
  $ frak(g) times.l_rho frak(h)->frak(e), quad (x,u) mapsto s(x)+u $
  其中 $rho(x)u=[s(x),u]$.
]

#proof[
  Jacobi 恒等式说明 $rho(x)$ 是导子, $s$ 保括号说明 $rho$ 保括号. 上面的线性同构展开括号后就是 Lie 同构. 反过来, 半直积的投影与 $x mapsto (x,0)$ 给出所需截面.
]

这一描述有直接的高阶版本. 对 $M in Rep(frak(g))$, 令模方向的括号为零, 得到平方零扩张 $frak(g) times.l M->frak(g)$. 向这个扩张的同伦截面组成导子生象
$ op("Der")(frak(g),M)
  :=Map_((LieAlg_R)_(\\/frak(g))) (frak(g),frak(g) times.l M) $
这里的映射位于 $frak(g)$ 之上. 它是关于 $M$ 的线性函子, 由 Lie 余切复形 $bb(L)_(frak(g)) in Rep(frak(g))$ 表示:
$ op("Der")(frak(g),M)
  tilde.eq Map_(Rep(frak(g))) (bb(L)_(frak(g)),M) $
因此导子与扩张也能用表示的稳定无穷范畴研究. 这一定义保留了导子的同伦, 在离散对象上恢复通常的导子.

== 离散对象的可解性与幂零性

从本节到 Levi 分解, 专门研究特征零域 $k$ 上的有限维离散 Lie 代数与表示; 需要代数闭时再注明. 这是一般理论的域上特例. 导出列与下中心列的定义本身适用于普通交换环, 但随后使用维数与三角化的证明是在域上进行的. Lie 无穷范畴不是稳定范畴, 这里的短正合列在离散范畴中理解.

#definition(title: [导出列与下中心列])[
  对离散 Lie 对象 $frak(g)$, 反复取括号像得到
  $ frak(g)^((0))=frak(g), quad
    frak(g)^((n+1))=[frak(g)^((n)),frak(g)^((n))] $
  若某项为零, 称 $frak(g)$ *可解*. 另一种迭代是
  $ gamma_1(frak(g))=frak(g), quad
    gamma_(n+1)(frak(g))=[frak(g),gamma_n (frak(g))] $
  若某项为零, 称 $frak(g)$ *幂零*. 两个过滤中的各项都是理想.
]

这两种过滤使用不同的 Lie 运算树: 导出列同时对两个分支迭代, 下中心列则每次只增加一个输入. 对一般高阶对象, 相应的过滤需要使用导出的算筹构造, 不能只把普通像换一个名字.

#proposition(title: [可解性对扩张封闭])[
  若 $0->frak(i)->frak(g)->frak(q)->0$ 正合, 且 $frak(i),frak(q)$ 可解, 则 $frak(g)$ 可解. 可解性与幂零性也分别对取子代数和商代数保持.
]

#proof[
  若 $frak(q)^((a))=0$, 则 $frak(g)^((a)) subset frak(i)$. 再若 $frak(i)^((b))=0$, 则 $frak(g)^((a+b))=0$. 子代数的两种列包含在原列中, 商代数的列则是原列的像.
]


#proposition[
  幂零一定可解.
]

#proof[
  只需归纳 $frak(g)^((n)) subset gamma_(n+1)(frak(g))$.
]

我们可以用另一种方法刻画幂零 Lie 代数:

#definition(title: [上中心列])[
  定义 $Z_0 (frak(g)) =0$, 并令
  $ Z_(i+1)(frak(g))\/Z_i (frak(g)) = Z(frak(g)\/Z_i (frak(g))) $
  于是 $0 subset Z_1 subset Z_2 subset ...$ 其中 $Z_1 = Z(frak(g))$ 称之为 Lie 代数的*上中心列*.
]

这个递归通过取原像实现. 若已经定义 $Z_i$, 取商映射 $q_i:frak(g)->frak(g)\/Z_i$, 再令
$ Z_(i+1)=q_i^(-1) (Z(frak(g)\/Z_i)) $
中心是理想, 所以其原像也是理想, 且包含 $ker(q_i)=Z_i$. 第一同构定理便给出定义中的商同构.

#proposition[
  $frak(g)$ 是幂零 Lie 代数当且仅当存在 $n$ 使得 $Z_n (frak(g)) = frak(g)$.
]

#proof[
  由定义
  $ Z_(i+1) = {x in frak(g) : [frak(g),x] subset Z_i}, quad Z_0 = 0 $
  归纳可得
  $ x in Z_i <=> [frak(g),[frak(g),[...,[frak(g),x]...]]] = 0 $
  其中有 $i$ 次括号.
]

#example(title: [Heisenberg Lie 代数])[
  最基本的非交换幂零 Lie 代数例子之一是*Heisenberg Lie 代数*, 定义为
  $ frak(h)_3 = k x plus.o k y plus.o k z $
  其中 $[x,y]=z,[x,z]=[y,z]=0$. 于是
  $ [frak(h)_3,frak(h)_3]=k z $
  而
  $ [frak(h)_3,k z] = 0 $
  于是其二步幂零.
]

=== Engel 定理

#theorem(title: [Engel 定理])[
  设 $frak(g)$ 是有限维 Lie 代数. 若每个 $ad_x$ 都幂零, 则 $frak(g)$ 幂零.
] <thm-engel>

#proof[
  先证引理.

  #lemma(title: [Engel引理])[
    设 $V != 0$, $frak(l) subset gl(V)$ 是有限维 Lie 代数. 若每个 $A in frak(l)$ 都幂零, 则存在 $0!=v in V$ 满足
    $ A v = 0, forall A in frak(l) $
  ]

  #proof[
    对 $dim frak(l)$ 归纳, 零维显然. 固定 $A in frak(l)$, 定义左, 右乘算子 $L_A,R_A:gl(V)->gl(V)$:
    $ L_A (B)=A B, quad R_A (B)=B A $
    其中 $B in gl(V)$, 乘法为算子复合. 于是 $ad_A=L_A-R_A$, 且
    $ L_A R_A (B)=A B A=R_A L_A (B) $
    故 $L_A,R_A$ 交换. 若 $A^m=0$, 则 $L_A^m=R_A^m=0$, 二项式展开得 $(ad_A)^(2m-1)=0$.

    取极大真子代数 $frak(h) subset frak(l)$. 其在 $frak(l)\/frak(h)$ 上的伴随算子皆幂零, 且像的维数 $< dim frak(l)$. 归纳得 $x in frak(l) minus frak(h)$ 满足
    $ [frak(h),x] subset frak(h) $
    故 $frak(h) plus.o k x$ 是子代数. 由极大性, $frak(l)=frak(h) plus.o k x$, 且 $frak(h) ideal frak(l)$.

    归纳得 $W := {v in V : frak(h)v=0} != 0$. 对 $B in frak(h), w in W$,
    $ B(x w)=x(B w)+[B,x]w=0 $
    故 $x W subset W$. 由 $x$ 幂零, 可取 $0!=v in W$ 使 $x v=0$, 从而 $frak(l)v=0$.
  ]

  再对 $dim frak(g)$ 归纳. 零维显然; 否则对 $ad(frak(g))$ 用引理, 得 $Z(frak(g)) != 0$. 商代数 $frak(g)\/Z(frak(g))$ 的伴随算子仍幂零, 故由归纳假设, 商代数幂零. 于是存在 $r$ 满足
  $ gamma_r (frak(g)) subset Z(frak(g)), quad gamma_(r+1)(frak(g))=[frak(g),gamma_r (frak(g))]=0 $
  故 $frak(g)$ 幂零.
]

=== Lie 定理

#theorem(title: [Lie 定理])[
  设 $k$ 代数闭, $char k=0$, $frak(g)$ 有限维可解. 对任意非零有限维表示 $rho:frak(g)->gl(V)$, 存在 $0!=v in V$ 和 $lambda in frak(g)^*$ 满足
  $ rho(x)v=lambda(x)v, quad forall x in frak(g) $
  等价地, 可选取一组基, 使所有 $rho(x)$ 同时上三角化.
] <thm-lie-triangularization>

#proof[
  对 $dim frak(g)$ 归纳, 零维显然. 由可解性, $[frak(g),frak(g)] != frak(g)$, 故可取包含它的余维一理想 $frak(h)$, 写成 $frak(g)=frak(h) plus.o k x$. 归纳得 $0!=v_0 in V$ 和 $mu in frak(h)^*$ 满足
  $ rho(y)v_0=mu(y)v_0, quad forall y in frak(h) $

  令 $X=rho(x)$, $U_j="span"{v_0,X v_0,dots,X^j v_0}$, $U_(-1)=0$. 由 $[y,x] in frak(h)$ 及
  $ rho(y)X=X rho(y)+rho([y,x]) $
  对 $j$ 归纳得 $(rho(y)-mu(y)id)X^j v_0 in U_(j-1)$. 故 $U="span"{X^j v_0:j>=0}$ 对 $frak(g)$ 稳定. 记 $d=dim U$; 在基 $v_0,dots,X^(d-1)v_0$ 下, $rho(y)|_U$ 上三角, 对角元均为 $mu(y)$. 于是
  $ 0="tr"([X|_U,rho(y)|_U])=d mu([x,y]) $
  由 $char k=0$, 得 $mu([x,frak(h)])=0$.

  令 $W={w in V:rho(y)w=mu(y)w, forall y in frak(h)}$. 因 $v_0 in W$, $W!=0$. 对 $w in W, y in frak(h)$,
  $ rho(y)X w=X rho(y)w+rho([y,x])w=mu(y)X w $
  故 $X W subset W$. 由 $k$ 代数闭, 可在 $W$ 中取 $X$ 的非零特征向量, 即为 $frak(g)$ 的公共特征向量.

  对商表示 $V\/k v$ 反复应用此结论, 得不变完全旗, 即同时上三角化; 反向取第一个基向量即可.
]

#corollary[
  在上述条件下, $frak(g)$ 的不可约有限维表示均为一维.
]

#proof[
  公共特征向量 $v$ 张成非零子表示 $k v$, 不可约性给出 $V=k v$.
]

=== 导出代数幂零

#corollary[
  设 $k$ 代数闭, $char k=0$. 若 $frak(g)$ 有限维可解, 则 $[frak(g),frak(g)]$ 幂零.
]

#proof[
  对伴随表示用 Lie 定理, 使所有 $ad_x$ 同时上三角化. 上三角矩阵的交换子严格上三角, 故
  $ ad([frak(g),frak(g)])=[ad(frak(g)),ad(frak(g))] $
  中的算子皆严格上三角, 从而幂零. 限制到 $[frak(g),frak(g)]$ 后仍幂零, 由 Engel 定理得证.
]


== Killing 形式

=== 可解根

#definition(title: [可解根])[
  有限维 Lie 代数 $frak(g)$ 有唯一最大可解理想 $rad(frak(g))$ 称之为*可解根*.
]

#proof[
  若 $frak(i),frak(j) ideal frak(g)$ 可解, 由短正合列
  $ 0 -> frak(j) -> frak(i) + frak(j) -> (frak(i)+frak(j))\/frak(j) -> 0 $
  并且有
  $ (frak(i)+frak(j))\/frak(j) tilde.eq frak(i)\/(frak(i) inter frak(j)) $
  是可解 Lie 代数的商, 由于可解性对扩张封闭, 所以 $frak(i)+frak(j)$ 可解. 只需定义
  $ rad(frak(g)) = sum_(frak(i) ideal frak(g) \ frak(i) "可解") frak(i) $
  即可.
]

#proposition[
  $frak(g)\/rad(frak(g))$ 没有非平凡可解理想.
]

#proof[
  商中可解理想的原像是可解理想被可解理想的扩张, 所以仍可解. 最大性迫使它等于 $rad(frak(g))$, 故商中的理想为零.
]

=== 半单 Lie 代数与单 Lie 代数

#definition(title: [半单 Lie 代数])[
  若 $rad(frak(g)) = 0$, 则称 $frak(g)$ 为*半单 Lie 代数*, 在有限维特征0的情况这等价于 $frak(g)$ 没有非零交换理想.
]

#definition(title: [单 Lie 代数])[
  若 $frak(g)$ 非交换且理想只有 $0$ 和 $frak(g)$, 则称 $frak(g)$ 为*单 Lie 代数*.
]

显然单 Lie 代数是半单 Lie 代数, 但半单 Lie 代数不一定是单 Lie 代数.

#definition(title: [完美对象的迹])[
  对任意交换环谱 $R$ 及 $Mod_R$ 中的完美对象 $V$, 对偶性给出迹态射
  $ tr:op("End")_R (V) tilde.eq V^or times.o_R V stretch(->)^ev R $
  普通环上的有限投射模由此得到通常的迹. 在域 $k$ 上, 这恢复有限维矩阵的迹; 对完美 $k$-复形, 零次自同态的迹是各次上同调上迹的交错和.
]

=== 矩阵 Lie 对象

#definition(title: [Lie 代数 $sl_n (k)$])[
  Lie 代数 $sl_n (k)$ 就是从 $gl_n (k)$ 中取迹为零的部分, 即
  $ sl_n (k) = ker (tr:gl_n (k) -> k) = {a in gl_n (k) | tr(a) = 0} $
  显然对 Lie括号封闭, 所以 $sl_n (k)$ 是 Lie 代数.
]

#proposition(title: [矩阵 Lie 代数的导出代数])[
  对 $n>=2$, 有
  $ [gl_n (k),gl_n (k)]=sl_n (k), quad gl_n (k)^"ab" tilde.eq k $
  第二个同构由迹给出. 此外, $sl_n (k)$ 是单 Lie 代数.
]

#proof[
  交换子的迹为零. 反过来, 非对角矩阵单位和对角差都由交换子给出:
  $ [E_(i i),E_(i j)]=E_(i j), quad
    [E_(i j),E_(j i)]=E_(i i)-E_(j j) $
  它们张成 $sl_n (k)$, 而迹满射到 $k$, 所以得到前两个结论.

  对单性, 取非零理想 $frak(i) subset sl_n (k)$ 及 $0!=A in frak(i)$. 可选迹为零的对角阵 $H$, 使所有有向差 $h_i-h_j$ 非零且两两不同. 因为 $k$ 无限, 只需避开有限多个真超平面. 若 $A$ 有非零非对角项, 对 $ad_H$ 作多项式投影就从 $A$ 分离出某个非零的 $E_(i j)$ 分量, 所以 $E_(i j) in frak(i)$.

  若 $A$ 为对角阵, 特征零保证非零的迹零对角阵不能是标量阵. 于是某个 $[A,E_(i j)]$ 是非零的 $E_(i j)$ 倍数. 两种情形都得到一个矩阵单位. 再取括号得到 $E_(i i)-E_(j j)$ 和 $E_(j i)$, 并利用 $[E_(i j),E_(j l)]=E_(i l)$ 逐步得到所有矩阵单位与对角差. 因而 $frak(i)=sl_n (k)$.
]

=== Killing 形式

#definition(title: [Killing 形式])[
  设 $R$ 是交换 $H QQ$-代数, $frak(g) in LieAlg_R$ 的底层完美. 伴随作用, 自同态复合与迹给出
  $ kappa:frak(g) times.o_R frak(g)
    stretch(->)^(ad times.o ad)
    op("End")_R (frak(g)) times.o_R op("End")_R (frak(g))
    ->R $
  即 $kappa(x,y)=tr(ad_x ad_y)$. 它是对称且不变的配对, 这里的对称性包含复形的 Koszul 符号. 称它*非退化*, 若伴随映射 $frak(g)->frak(g)^or$ 是等价.
]

#proof[
  迹的循环性给出对称性, 伴随作用的表示恒等式给出不变性. 在离散情形, 所需计算为
  $ tr([ad_x,ad_y]ad_z)=tr(ad_x[ad_y,ad_z]) $
  所以 $kappa([x,y],z)=kappa(x,[y,z])$. 一般情形使用同一条对称幺半迹恒等式, 移动齐次输入时带相应符号.
]

普通交换环上底层有限投射的经典 Lie 代数也可用同一迹公式定义 Killing 形式. 下面的根与 Cartan 判据重新限制在特征零域 $k$ 上的有限维离散对象中. 完美性使迹有定义, 并不自动给出这些域上的结构判据.

#definition(title: [双线性形式的根])[
  设 $frak(g)$ 是 Lie 代数, $B: frak(g) times.o frak(g) -> k$ 是双线性形式, 定义其*根*为
  $ rad(B) = {x in frak(g) | forall y in frak(g), B(x,y) = 0} $
]

#proposition[
  $rad(kappa) ideal frak(g)$ 是 Lie理想.
]

#proof[
  取 $x in rad(kappa), y in frak(g)$, 对任意 $z in frak(g)$ 利用 Killing 形式的不变性有
  $ kappa([x,y],z) = kappa(x,[y,z]) = 0 $
  所以 $[x,y] in rad(kappa)$, 从而 $rad(kappa) ideal frak(g)$.
]

=== Cartan的系列结论

#theorem(title: [Cartan可解判据])[
  设 $frak(g)$ 是有限维特征 $0$ Lie 代数, 那么 $frak(g)$ 可解当且仅当 Killing 形式 $kappa(frak(g),[frak(g),frak(g)])=0$.
] <thm-cartan-solvability>

#proof[
  先考虑复情形. 对一般特征零域, 所涉及的有限多个结构常数定义在一个有限生成的 $QQ$-子域上, 它可嵌入 $CC$; 迹等式与导出列的消失均可由忠实标量扩张检测, 因而可以这样归约. 设 $frak(l) subset gl(V)$ 是有限维线性 Lie 代数, 若
  $ tr(X Y) = 0, quad forall X in frak(l), Y in [frak(l),frak(l)] $
  则 $frak(l)$ 可解. 只需说明 $[frak(l),frak(l)]$ 是幂零 Lie 代数即可. 任取
  $ X in [frak(l),frak(l)] $
  将 $V$ 按 $X$ 的广义特征子空间分解为
  $ V = plus.o.big_(lambda) V_lambda $
  定义 $Y in End(V)$ 为 $Y|_(V_lambda) = overline(lambda)id$, 对
  $ T in Hom(V_mu,V_lambda) $
  $ad X$ 的广义特征值为 $lambda-mu$, 而
  $ ad Y(T) = (overline(lambda)-overline(mu))T = overline(lambda-mu)T $
  因此由多项式插值, 可以找 $p(t)in CC[t]$ 且 $p(0)=0$ 使得
  $ ad Y = p(ad X) $
  因为 $X in [frak(l),frak(l)]$, 且 $p(0)=0$. 故
  $ [Y,frak(l)] = p(ad X)(frak(l)) subset [frak(l),frak(l)] $
  另一方面, 把
  $ X = sum_i [A_i,B_i], quad A_i, B_i in frak(l) $
  由迹的循环性
  $ tr(X Y) = sum_i tr([A_i,B_i]Y) = sum_i tr(A_i [B_i,Y]) $
  而 $[B_i, Y]in[frak(l),frak(l)]$, 由假设 $tr(X Y) = 0$, 但在 $V_lambda$ 上
  $ X = lambda I + N, quad Y = overline(lambda) I $
  其中 $N$ 是幂零的, 所以
  $ tr(X Y) = sum_(lambda) (dim V_lambda) abs(lambda)^2 $
  等于零, 所以 $lambda=0$ 对所有 $lambda$ 成立, 从而 $X$ 是幂零的. 由 Engel 定理可得 $[frak(l),frak(l)]$ 是幂零 Lie 代数.

  下面证明原结论, 若 $frak(g)$ 可解, 可以选取基使所有
  $ ad x, quad x in frak(g) $
  都是上三角的, 而
  $ ad([frak(g),frak(g)]) = [ad frak(g),ad frak(g)] $
  都是严格上三角, 因此若 $x in frak(g)$ 且 $y in [frak(g),frak(g)]$, 则乘积 $ad_x ad_y$ 严格上三角, 于是 $kappa(x,y)=0$. 反之, 设 $kappa(frak(g),[frak(g),frak(g)])=0$. 令 $frak(l)=ad frak(g) subset gl(frak(g))$, 则
  $ [frak(l),frak(l)] = ad [frak(g),frak(g)] $
  所以假设恰好意味着
  $ tr(X Y) = 0, quad forall X in frak(l), Y in [frak(l),frak(l)] $
  由上面的结论可得 $frak(l)$ 可解, 而
  $ frak(g)\/Z(frak(g)) tilde.eq ad frak(g) = frak(l) $
  故 $frak(g)\/Z(frak(g))$ 可解, 由 $Z(frak(g))$ 是交换 Lie 代数, 所以 $frak(g)$ 可解.
]

#theorem(title: [Cartan半单判据])[
  有限维特征 $0$ Lie 代数 $frak(g)$ 是半单 Lie 代数当且仅当其 Killing 形式非退化, 即 $rad(kappa) = 0$, 或者说
  $ kappa(x,y) = 0 "对任意" y in frak(g) "成立" => x=0 $
]

#proof[
  先记录理想上迹的限制. 若 $frak(i) ideal frak(g)$ 且 $x in frak(i)$, $ad_x$ 在 $frak(g)/frak(i)$ 上为零. 因而对 $x,y in frak(i)$ 有
  $ kappa_(frak(i)) (x,y)=kappa_(frak(g)) (x,y) $
  若 $frak(g)$ 半单, 取 $frak(i)=rad(kappa)$. 它是理想, 上式说明其自身的 Killing 形式为零. Cartan 可解判据给出 $frak(i)$ 可解, 半单性迫使 $frak(i)=0$.

  反过来, 若可解根非零, 取其导出列的最后一个非零项 $frak(a)$. 这是非零交换理想. 对 $x in frak(a)$, $ad_x$ 将 $frak(g)$ 送入 $frak(a)$ 并在 $frak(a)$ 上为零; 对任意 $y in frak(g)$, $ad_y$ 保持 $frak(a)$. 所以 $ad_x ad_y$ 的所有对角块都为零, 从而 $kappa(x,y)=0$. 这使非零的 $frak(a)$ 落入 $rad(kappa)$, 与非退化矛盾.
]

== 半单 Lie 代数的分解

=== 理想的正交补

#lemma[
  若 $frak(a) ideal frak(g)$, 则
  $ kappa_(frak(a)) (x,y)=kappa_(frak(g)) (x,y), quad x,y in frak(a) $
]

#proof[
  取适配 $frak(a)$ 的基. 对 $x in frak(a)$, $ad_x$ 在 $frak(g) slash frak(a)$ 上为零, 故其分块矩阵为
  $ ad_x = mat(ad_x|_(frak(a)), *; 0, 0) $
  对 $ad_x ad_y$ 取迹即得.
]

#lemma(title: [理想的正交分解])[
  设 $frak(g)$ 半单, $frak(a) ideal frak(g)$. 对 Killing 形式取正交补, 则
  $ frak(g)=frak(a) plus.o frak(a)^perp, quad [frak(a),frak(a)^perp]=0 $
  且两项均为半单理想.
]

#proof[
  对 $x in frak(g), y in frak(a)^perp, z in frak(a)$,
  $ kappa([x,y],z)=-kappa(y,[x,z])=0 $
  故 $frak(a)^perp$ 是理想. 令 $frak(b)=frak(a) inter frak(a)^perp$, 也是理想. 上一引理给出 $kappa_(frak(b))=kappa_(frak(g))|_(frak(b) times.o frak(b))=0$. 由 Cartan可解判据, $frak(b)$ 可解; 半单性给出 $frak(b)=0$.

  由 $kappa_(frak(g))$ 非退化, $dim frak(a)^perp=dim frak(g)-dim frak(a)$, 故得直和. 两项均为理想, 从而
  $ [frak(a),frak(a)^perp] subset frak(a) inter frak(a)^perp=0 $
  $kappa_(frak(g))$ 在两项上的限制均非退化, 又分别等于其 Killing 形式, 故两项均半单.
]

=== 分解定理

#theorem(title: [半单 Lie 代数分解])[
  $frak(g)$ 半单当且仅当它是有限个单 Lie 代数的直和:
  $ frak(g)=frak(g)_1 plus.o dots plus.o frak(g)_r $
  各项是 $frak(g)$ 的单理想, 不同项彼此交换. 此分解除排列次序外唯一, 且每个理想都是其中若干项的直和. 零代数对应空直和.
]

#proof[
  先设 $frak(g)!=0$ 半单, 对维数归纳. 取极小非零理想 $frak(a)$, 由正交分解引理,
  $ frak(g)=frak(a) plus.o frak(a)^perp $
  若 $frak(b) ideal frak(a)$, 因 $[frak(a)^perp,frak(a)]=0$, $frak(b)$ 也是 $frak(g)$ 的理想. 极小性给出 $frak(b)=0$ 或 $frak(a)$. 又 $frak(a)$ 非交换, 否则它是非零可解理想. 故 $frak(a)$ 单. 对半单代数 $frak(a)^perp$ 用归纳假设, 得所需分解.

  对任意单 Lie 代数 $frak(s)$, $[frak(s),frak(s)]$ 是非零理想, 故等于 $frak(s)$. 现设 $frak(g)$ 是上述单代数直和, $frak(b) ideal frak(g)$, 记投影为 $pi_i:frak(g)->frak(g)_i$. 若 $pi_i (frak(b))!=0$, 它是 $frak(g)_i$ 的非零理想, 故
  $ [frak(g)_i,frak(b)]=[frak(g)_i,pi_i (frak(b))]=frak(g)_i subset frak(b) $
  因而 $frak(b)$ 恰为这些 $frak(g)_i$ 的直和. 若 $frak(b)$ 可解, 每个 $pi_i (frak(b))$ 也可解, 不可能等于单代数 $frak(g)_i$, 故 $frak(b)=0$. 这证明反向.

  上述理想描述还说明, $frak(g)_i$ 恰为 $frak(g)$ 的全部极小非零理想, 故分解除次序外唯一.
]

#corollary[
  若 $frak(g)$ 半单, 则其理想与商代数均半单, 且
  $ [frak(g),frak(g)]=frak(g), quad Z(frak(g))=0 $
]

#proof[
  理想与商代数均由部分单因子组成. 单代数的导出代数是自身, 中心为零; 对直和逐项应用即可.
]

== 表示的分裂与上同调

=== 导出不变元与上同调

#definition(title: [Lie 上同调])[
  对任意交换环谱 $R$, $frak(g) in LieAlg_R$ 与 $M in Rep_R (frak(g))$, 用平凡模 $R$ 定义导出不变元
  $ C^*(frak(g),M):=op("RHom")_(Rep_R (frak(g))) (R,M) in Mod_R $
  这里取 $R$-线性的内部映射对象. 对普通环 $A$, 它是 $cal(D)(A)$ 中的复形, 定义 $H^n (frak(g),M):=H^n (C^*(frak(g),M))$.

  特别地, 伴随模给出 $C^*(frak(g),frak(g))$. 在特征零域上, 当 $frak(g)$ 离散时,
  $ H^0(frak(g),frak(g))=Z(frak(g)), quad
    H^1(frak(g),frak(g))=Der(frak(g))\/op("Inn")(frak(g)) $
  因而普通中心只是这一导出对象的零次部分.
] <def-lie-cohomology>

#proposition(title: [Chevalley--Eilenberg 计算])[
  回到特征零域 $k$. 若 $frak(g),M$ 离散, 上述对象由 Chevalley--Eilenberg 上链复形计算:
  $ C^q (frak(g),M)=Hom_k (and^q frak(g),M) $
  微分为
  $ (d f)(x_0,dots,x_q)
    &=sum_i (-1)^i x_i f(x_0,dots,hat(x_i),dots,x_q) \
    &quad +sum_(i<j) (-1)^(i+j)
      f([x_i,x_j],x_0,dots,hat(x_i),dots,hat(x_j),dots,x_q) $
  帽号表示删去该输入. 例如
  $ (d m)(x)=x m, quad
    (d f)(x,y)=x f(y)-y f(x)-f([x,y]) $
] <prop-ce-computation>

#proof[
  用后面的 @prop-lie-modules-enveloping 将表示认作 $U(frak(g))$-模. 考虑增广复形
  $ dots->U(frak(g)) times.o_k and^2 frak(g)
    ->U(frak(g)) times.o_k frak(g)->U(frak(g))->k $
  微分由左乘与 Lie 括号给出; $d^2=0$ 中的两类抵消正是表示恒等式与 Jacobi 恒等式.

  按 PBW 次数加上外幂次数过滤. @thm-derived-pbw 将相伴分次识别为 $op("Sym")(frak(g))$ 的 Koszul 分解, 它在增广后正合. 每个元素的过滤次数有限, 逐次消去最高项便得原复形也正合. 若 $frak(g)$ 无限维, 对有限个生成元的 Koszul 复形取筛余极限即可. 因而这是 $k$ 的自由模分解, 对它取 $Hom_(U(frak(g))) (-,M)$ 就得到所写微分.
]

于是 $H^1(frak(g),M)$ 描述 $k$ 被 $M$ 扩张的障碍, $H^2(frak(g),M)$ 描述带指定作用的交换 Lie 扩张. 后面两个 Whitehead 引理说明, 对半单的离散有限维 Lie 对象和离散有限维系数, 这两个障碍都消失.


=== Casimir 算子与第一 Whitehead 引理

#lemma(title: [Casimir 算子])[
  设 $B$ 是 $frak(g)$ 上的非退化不变对称双线性形式, $e_i,e^i$ 是对偶基, 即 $B(e_i,e^j)=delta_i^j$. 对表示 $(M,rho)$, 定义
  $ C_M = sum_i rho(e_i)rho(e^i) $
  则 $C_M$ 与所有 $rho(x)$ 交换.
]

#proof[
  先证不变张量恒等式
  $ sum_i ([x,e_i] times.o e^i + e_i times.o [x,e^i])=0 $
  将左端与 $u times.o v$ 按 $B times.o B$ 配对, 得
  $ B([x,v],u)+B([x,u],v)=0 $
  由 $B$ 非退化, 张量恒等式成立. 对其应用 $a times.o b |-> rho(a)rho(b)$, 得
  $ [rho(x),C_M]=sum_i (rho([x,e_i])rho(e^i)+rho(e_i)rho([x,e^i]))=0 $
]

#lemma(title: [非平凡不可约表示上的 Casimir 算子])[
  设 $frak(g)$ 半单, $M$ 是非平凡不可约表示. 可选取上述形式 $B$, 使 $C_M$ 可逆.
]

#proof[
  令 $frak(n)=ker rho$. 由半单分解, 可取半单理想 $frak(t)$ 使 $frak(g)=frak(t) plus.o frak(n)$. $frak(t)$ 在 $M$ 上忠实作用. 定义
  $ B_M (x,y)=tr_M (rho(x)rho(y)), quad x,y in frak(t) $
  迹的循环性使 $B_M$ 对称且不变, 故其根 $frak(j)$ 是 $frak(t)$ 的理想. 对 $x,y in frak(j)$, $tr_M (rho(x)rho(y))=0$. 由@thm-cartan-solvability 证明中的线性判据, $rho(frak(j))$ 可解; 忠实性给出 $frak(j)$ 可解, 故 $frak(j)=0$.

  在 $frak(g)=frak(t) plus.o frak(n)$ 上取 $B=B_M plus.o kappa_(frak(n))$, 并取适配此直和的对偶基. $frak(n)$ 在 $M$ 上作用为零, 故
  $ tr_M (C_M)=sum_(e_i in frak(t)) B_M (e_i,e^i)=dim frak(t)!=0 $
  最后一个不等式用了 $char k=0$ 及 $M$ 非平凡. 故 $C_M!=0$. 由交换性, $ker C_M$ 是子表示; 不可约性给出 $ker C_M=0$, 从而 $C_M$ 可逆. 其逆也与 $frak(g)$ 的作用交换.
]

#lemma(title: [第一 Whitehead 引理])[
  设 $frak(g)$ 是离散有限维半单 Lie 代数, $M$ 是离散有限维 $frak(g)$-模. 若线性映射 $f:frak(g)->M$ 满足
  $ f([x,y])=x f(y)-y f(x) $
  则存在 $m in M$ 使 $f(x)=x m$ 对所有 $x$ 成立. 这也记作 $H^1 (frak(g),M)=0$.
]

#proof[
  先设 $M$ 不可约. 若作用平凡, 则由 $[frak(g),frak(g)]=frak(g)$ 得 $f=0$. 否则选取使 $C_M$ 可逆的形式 $B$, 并令
  $ m_0=sum_i e_i f(e^i) $
  由 $f$ 的条件及不变张量恒等式,
  $ x m_0 &= sum_i ([x,e_i] f(e^i)+e_i x f(e^i)) \
    &= sum_i ([x,e_i] f(e^i)+e_i f([x,e^i]))+sum_i e_i e^i f(x) \
    &= C_M f(x) $
  故取 $m=C_M^(-1) m_0$, 即有 $f(x)=x m$.

  一般情形对 $dim M$ 归纳, $M=0$ 显然. 若 $M$ 可约, 取非零真子模 $N$, 记 $q:M->M slash N$. 由归纳假设, $q f(x)=x overline(m)$; 取 $m_1 in M$ 提升 $overline(m)$. 则
  $ f_1 (x)=f(x)-x m_1 $
  取值于 $N$, 且仍满足同一条件. 再由归纳假设, $f_1 (x)=x n$ 对某个 $n in N$ 成立. 取 $m=m_1+n$ 即得.
]

#corollary[
  半单 Lie 代数的导子都是内导子, 即 $Der(frak(g))="Inn"(frak(g))$.
]

#proof[
  对伴随模应用第一引理. 导子条件给出 $D([x,y])=[x,D y]-[y,D x]$, 故 $D x=[x,a]=ad_(-a) (x)$.
]

=== 完全可约

#definition(title: [完全可约表示])[
  表示 $V$ 若是不可约子表示的直和, 则称为*完全可约表示*.
]

#theorem(title: [Weyl 完全可约定理])[
  离散有限维半单 Lie 代数的每个离散有限维表示都完全可约. 更具体地, 对任意子表示 $W subset V$, 存在子表示 $U$ 使
  $ V=W plus.o U $
]

#proof[
  设 $W subset V$ 是子表示, 令 $Q=V slash W$, $q:V->Q$. 先取线性截面 $s:Q->V$, 即 $q s=id_Q$. 在
  $ M=Hom_k (Q,W) $
  上定义作用 $x T=rho_W (x)T-T rho_Q (x)$. 展开得 $x(y T)-y(x T)=[x,y]T$, 故这是表示.

  截面的不变性偏差为
  $ f(x)=rho_V (x)s-s rho_Q (x) $
  因 $q f(x)=0$, $f(x)$ 取值于 $M$. 展开并用 $rho([x,y])=[rho(x),rho(y)]$, 得
  $ f([x,y])=x f(y)-y f(x) $
  第一引理给出 $T in M$ 使 $f(x)=x T$. 将 $T$ 视作到 $V$ 的映射, 令 $s'=s-T$, 则
  $ rho_V (x)s'-s' rho_Q (x)=0, quad q s'=id_Q $
  故 $U=im s'$ 是子表示, 且 $V=W plus.o U$.

  若 $V!=0$, 取极小非零子表示, 它不可约; 对其补空间按维数归纳, 即得不可约子表示的直和分解.
]

=== 第二 Whitehead 引理与交换扩张

#lemma(title: [第二 Whitehead 引理])[
  设 $frak(g)$ 是离散有限维半单 Lie 代数, $M$ 是离散有限维 $frak(g)$-模. 若交错双线性映射 $f:frak(g) times frak(g)->M$ 满足
  $ 0 &= x f(y,z)-y f(x,z)+z f(x,y) \
    &quad -f([x,y],z)+f([x,z],y)-f([y,z],x) $
  则存在 $b:frak(g)->M$ 线性, 使
  $ f(x,y)=(d b)(x,y):=x b(y)-y b(x)-b([x,y]) $
  这也记作 $H^2 (frak(g),M)=0$.
]

#proof[
  由 Weyl 定理, $M$ 是不可约模的直和. $f$ 与 $b$ 可逐分量处理, 故只需设 $M$ 不可约.

  先设作用非平凡. 取使 $C_M$ 可逆的形式 $B$, 令
  $ h(x)=sum_i e_i f(e^i,x) $
  引理中的六项等式可改写为
  $ x f(z,y)-y f(z,x)-f(z,[x,y]) &= z f(x,y) \
    &quad +f([x,z],y)-f([y,z],x) $
  因而
  $ (d h)(x,y) &= sum_i ([x,e_i] f(e^i,y)-[y,e_i] f(e^i,x)) \
    &quad +sum_i e_i (x f(e^i,y)-y f(e^i,x)-f(e^i,[x,y])) \
    &= sum_i e_i e^i f(x,y)=C_M f(x,y) $
  最后一步用不变张量恒等式, 将含 $[x,e_i]$ 和 $[y,e_i]$ 的项分别抵消. 因 $C_M^(-1)$ 与作用交换, 取 $b=C_M^(-1) compose h$, 即有 $d b=f$.

  再设作用平凡. 不可约性给出 $M tilde.eq k$. 由 Killing 形式非退化, 唯一确定线性映射 $D:frak(g)->frak(g)$ 使
  $ kappa(D x,y)=f(x,y) $
  此时六项等式与 $f$ 的交错性给出
  $ kappa(D[x,y],z) &= f([x,y],z) \
    &= f(x,[y,z])+f(y,[z,x]) \
    &= kappa([D x,y]+[x,D y],z) $
  故 $D$ 是导子. 由第一引理, 写 $D x=[x,a]$. 取 $b(x)=kappa(a,x)$, 则
  $ f(x,y)=kappa([x,a],y)=-kappa(a,[x,y])=-b([x,y])=(d b)(x,y) $
  两种情形均得证.
]

#lemma[
  若 Lie 代数短正合列
  $ 0 -> frak(a) -> frak(e) ->^p frak(s) -> 0 $
  中 $frak(a)$ 交换, $frak(s)$ 半单, 则存在 Lie 代数截面 $sigma:frak(s)->frak(e)$.
]

#proof[
  取线性截面 $t:frak(s)->frak(e)$, 定义
  $ x u=[t(x),u], quad alpha(x,y)=[t(x),t(y)]-t([x,y]) in frak(a) $
  由 $frak(a)$ 交换, $x u$ 与提升的选择无关, 且
  $ x(y u)-y(x u)-[x,y]u=[alpha(x,y),u]=0 $
  故 $frak(a)$ 是 $frak(s)$-模. 展开 $frak(e)$ 中的 Jacobi 恒等式, 并用 $frak(s)$ 中的 Jacobi 恒等式消去含 $t$ 的项, 得
  $ 0 &= x alpha(y,z)-y alpha(x,z)+z alpha(x,y) \
    &quad -alpha([x,y],z)+alpha([x,z],y)-alpha([y,z],x) $
  由第二引理, 存在线性映射 $b:frak(s)->frak(a)$ 使 $alpha=d b$. 令 $sigma=t-b$, 则 $p sigma=id_(frak(s))$, 且
  $ [sigma(x),sigma(y)]-sigma([x,y]) \
    = alpha(x,y)-x b(y)+y b(x)+b([x,y])=0 $
  这里用了 $[b(x),b(y)]=0$. 故 $sigma$ 是 Lie 代数截面.
]

=== Levi 分解

#theorem(title: [Levi 分解定理])[
  设 $frak(g)$ 是 Lie 代数, $frak(r)=rad(frak(g))$. 存在半单子代数 $frak(s) subset frak(g)$, 使
  $ frak(g)=frak(s) plus.o frak(r) $
  作为线性空间直和. 等价地, 商映射 $frak(g)->frak(g) slash frak(r)$ 有 Lie 代数截面, 且
  $ frak(g) tilde.eq frak(s) times.l_rho frak(r), quad rho(x)(u)=[x,u] $
  称 $frak(s)$ 为*Levi子代数*, 它同构于 $frak(g) slash frak(r)$.
]

#proof[
  对 $dim frak(r)$ 归纳. 若 $frak(r)=0$, 取 $frak(s)=frak(g)$.

  若 $frak(r)!=0$, 取其导出列的最后一个非零项 $frak(a)$. 由 Jacobi 恒等式, 理想的导出代数仍是理想, 故 $frak(a) ideal frak(g)$, 且 $[frak(a),frak(a)]=0$. 记
  $ p:frak(g)->overline(frak(g)):=frak(g) slash frak(a) $
  则 $rad(overline(frak(g)))=frak(r) slash frak(a)$: 右端是可解理想; 商代数中任一可解理想的原像 $frak(b)$ 满足 $frak(b) slash frak(a)$ 可解, 故某个导出项 $frak(b)^((m)) subset frak(a)$, 继而 $frak(b)^((m+1))=0$. 因而 $frak(b) subset frak(r)$.

  由归纳假设, 存在半单子代数 $overline(frak(s))$ 使
  $ overline(frak(g))=overline(frak(s)) plus.o (frak(r) slash frak(a)) $
  令 $frak(e)=p^(-1) (overline(frak(s)))$, 则有交换扩张
  $ 0 -> frak(a) -> frak(e) -> overline(frak(s)) -> 0 $
  由上一引理, 存在半单子代数 $frak(s) subset frak(e)$, 使 $p|_(frak(s))$ 同构到 $overline(frak(s))$.

  商中的分解给出 $frak(g)=frak(s)+frak(r)$. 若 $x in frak(s) inter frak(r)$, 则
  $ p(x) in overline(frak(s)) inter (frak(r) slash frak(a))=0 $
  由 $p|_(frak(s))$ 单射得 $x=0$, 故 $frak(g)=frak(s) plus.o frak(r)$ 作为线性空间. $frak(r)$ 是理想, 所以伴随作用 $rho(x)(u)=[x,u]$ 给出半直积结构, 即
  $ frak(s) times.l_rho frak(r) ->^~ frak(g), quad (x,u)|->x+u $
]

#example(title: [三个分解的例子])[
  $sl_2 (k) plus.o sl_3 (k)$ 是两个单理想的直和. 对 $n>=2$,
  $ gl_n (k)=sl_n (k) plus.o k I_n $
  其中 $rad(gl_n (k))=k I_n$, $sl_n (k)$ 是 Levi子代数: $k I_n$ 是交换理想, 商代数 $sl_n (k)$ 半单, 故可解根恰为 $k I_n$.

  Weyl 定理分解的是表示空间, 例如对 $sl_n (k)$ 的伴随作用,
  $ End_k (k^n)=sl_n (k) plus.o k I_n $
  两项分别是不可约的伴随表示与一维平凡表示. 第一项的不可约性来自 $sl_n (k)$ 的单性.
]

这些分裂发生在离散有限维表示或 Lie 对象中. 用高阶语言说, 第一 Whitehead 引理使相应的表示扩张类消失, 第二引理使交换 Lie 扩张的障碍消失. 它们没有断言整个 $Rep(frak(g))$ 的所有高次扩张都消失. 经典结构定理另见 @Eti24Lie[第 15--18 节].


== 泛包络代数与 PBW 定理

现在回到任意交换环谱 $R$ 及开头的 $R$-线性范畴 $cal(C)$. 沿交换子给出的算筹态射, 可以把 Lie 运算扩张为结合运算. 这一构造不需要域的假设.

=== 泛性质与构造

#definition(title: [泛包络代数])[
  算筹态射 $i:Lie_R^times.o->Assoc_R^times.o$ 诱导限制函子
  $ i^*:Alg(cal(C))->LieAlg(cal(C)), quad B mapsto B^"Lie" $
  它的左伴随称为*泛包络代数*函子, 记作 $U$. 它由映射生象的自然等价刻画
  $ Map_(Alg(cal(C))) (U(frak(g)),B)
    tilde.eq Map_(LieAlg(cal(C))) (frak(g),B^"Lie") $
  特别有典范 Lie 态射 $frak(g)->U(frak(g))^"Lie"$.
] <def-universal-enveloping>

#proposition(title: [导出构造与 dg 模型])[
  $U$ 存在, 可以用算筹的相对复合计算:
  $ U(frak(g))=Assoc_R compose_(Lie_R)^bb(L) frak(g) $
  右边是双边杠构造的几何实现, 包括零输入的单位项. 等价地, 先沿没有零输入运算的结合算筹构造 $U^"nu"$, 再添上单位:
  $ U(frak(g))=bold(1) plus.o U^"nu"(frak(g)) $

  若 $A$ 是交换 $QQ$-代数, 取 $frak(g)$ 的余纤维dg Lie 模型 $tilde(frak(g))$, 则可用下述 dg 代数计算导出包络代数:
  $ U(frak(g)) tilde.eq T(tilde(frak(g)))\/chevron.l
    x y-(-1)^(abs(x) abs(y)) y x-[x,y] chevron.r $
  其中 $T(tilde(frak(g)))=plus.o.big_(n>=0) tilde(frak(g))^(times.o_A n)$, 此处在 dg 模型中取普通张量代数与 dg 双边理想商.
]

#proof[
  在自由 Lie 分解上, 左伴随必须将自由 Lie 代数送到自由结合代数. 对这个分解作几何实现, 得到相对复合及其伴随泛性质.

  在 dg 模型中, 张量代数的态射由生成元上的链映射决定; 它经过所写商, 当且仅当该映射保持括号. 这给出严格伴随. 限制函子保持纤维化与平凡纤维化, 因而在余纤维替换后计算导出伴随. 域上的 PBW 证明还会说明, 特征零域上任意严格 dg 模型均可用于这一计算.
]

这里的 $U$ 是含幺结合代数, 并有由零 Lie 态射诱导的增广 $U(frak(g))->bold(1)$. 零 Lie 代数的包络代数是张量单位 $bold(1)$, 在 $Mod_R$ 中就是 $R$; 自由 Lie 对象的包络代数是张量代数. 标量扩张也与之相容:
$ S times.o_R U_R (frak(g)) tilde.eq U_S (S times.o_R frak(g)) $
因为杠构造中的张量积与几何实现都可与标量扩张交换.

=== PBW 过滤

#theorem(title: [PBW 定理])[
  泛包络代数有自然的穷尽乘法过滤
  $ F_0 U(frak(g))->F_1 U(frak(g))-> dots, quad
    varinjlim(n>=0) F_n U(frak(g)) tilde.eq U(frak(g)) $
  其中 $F_0 U=bold(1)$, 过滤来自生成元个数. 相伴分次定义为
  $ op("gr")_n U(frak(g))
    :=cofib(F_(n-1) U(frak(g))->F_n U(frak(g))), quad F_(-1) U=0 $
  则有自然等价
  $ op("gr") U(frak(g)) tilde.eq op("Sym")(frak(g)), quad
    op("Sym")^n (frak(g))=(frak(g)^(times.o n))_(h Sigma_n) $
  这里 $op("Sym")$ 是自由交换代数对象, 相伴分次的乘法是它的交换乘法. 结论适用于任意交换环谱 $R$.
] <thm-derived-pbw>

#proof[
  给 $frak(g)$ 加上过滤
  $ c_1(frak(g))=(0->frak(g) stretch(->)^id frak(g) stretch(->)^id dots) $
  所有生成元放在过滤次数 $1$. 在过滤对象的 Day 张量积下, 原有 Lie 运算给出这个过滤的 Lie 结构. 在过滤范畴中取包络代数, 定义
  $ F_bullet U(frak(g)):=U(c_1(frak(g))) $
  取过滤余极限是对称幺半的, 且与杠构造交换, 故
  $ varinjlim(n>=0) F_n U(frak(g))
    tilde.eq U(varinjlim(n>=0) c_1(frak(g))_n)
    tilde.eq U(frak(g)) $

  取相伴分次同样是对称幺半的, 并保持余极限. $op("gr")(c_1(frak(g)))$ 只在权重 $1$ 非零, 所以所有至少二元的 Lie 运算都为零. 因而它是底层对象的平凡 Lie 结构, 并有
  $ op("gr") U(frak(g)) tilde.eq U(op("triv")(frak(g))) $
  右边把底层 $frak(g)$ 放在权重 $1$.

  最后使用谱算筹的 PBW 恒等式
  $ Assoc^"nu" compose_Lie^bb(L) bold(1)
    tilde.eq Comm^"nu" $
  这是 @ABH25[定理 1.2] 的算筹输入, 并非算筹范畴中的推出等式. 对两侧作用于 $frak(g)$, 再添上单位, 得到
  $ U(op("triv")(frak(g))) tilde.eq op("Sym")(frak(g)) $
  这就给出所需相伴分次及其乘法. 整个推导只使用谱算筹作用与对称幺半的余极限构造, 所以同样适用于 $Mod_R$ 和所设的 $cal(C)$.
]

这个结论没有要求过滤自然分裂. 在一般底环上, 同伦余不变量也不能换成普通余不变量. 下面的对称化是 $QQ$-线性语境的额外结论.

#proposition(title: [有理对称化])[
  若 $cal(C)$ 是 $QQ$-线性的, 则有自然的过滤对象等价
  $ op("sym"):plus.o.big_(n>=0) op("Sym")^n (frak(g))->U(frak(g)) $
  左边按次数过滤. 这一般不是结合代数的等价. 例如该结论适用于任意交换 $H QQ$-代数 $R$ 的模范畴, 不要求 $R$ 来自域.
]

#proof[
  *先在特征零域 $k$ 上证明.* 对严格 dg 模型, 选取底层分次向量空间的齐次有序基 $e_i$. 利用关系
  $ e_j e_i=(-1)^(abs(e_i) abs(e_j)) e_i e_j+[e_j,e_i] quad (j>i) $
  可以交换逆序输入; 对奇次基元还使用
  $ e_i^2=frac(1,2)[e_i,e_i] $
  每次改写或者降低字长, 或者在同一字长下减少逆序数, 因而必然终止. 最终候选单项式是有序基元的乘积, 其中奇次基元最多出现一次.

  需要检查不同改写次序得到相同结果. 不相交的两次改写彼此交换. 重叠只可能发生在三个相邻输入上; 两种次序的差约化为
  $ [x,[y,z]]-[[x,y],z]-(-1)^(abs(x) abs(y)) [y,[x,z]] $
  所以由分次 Jacobi 恒等式消失. 重复的奇次输入给出同一恒等式的特例, 三个输入相同时还用到 $3[x,[x,x]]=0$. 特征零允许所需除法. 对终止的改写归纳, 每个元素于是有唯一正规形.

  这些有序单项式因此是 $U(frak(g))$ 的基. 取相伴分次后, 括号项的字长较低而消失, 剩下恰好是分次交换代数 $op("Sym")(frak(g))$ 的关系与基. 微分保持过滤, 在生成元上与 $op("Sym")$ 的微分一致, 因而得到复形及分次代数的同构.

  *再把它写成自然的构造.* 对称化为
  $ op("sym")(x_1 dots x_n)
    =frac(1,n!) sum_(sigma in Sigma_n) epsilon(sigma;x)
      x_(sigma(1)) dots x_(sigma(n)) $
  其中 $epsilon(sigma;x)$ 是置换齐次输入产生的 Koszul 符号. 它是链映射, 并且在相伴分次上为刚才的恒等映射. 各阶过滤有限, 归纳得每阶都是同构, 再取穷尽并得到 $op("sym")$. 特征零下 $op("Sym")$ 保持拟同构, 因而 $U$ 也保持拟同构, 所以上述计算下降到 $LieAlg_k$.

  *再推广到任意 $QQ$-线性的 $cal(C)$.* 在 $QQ$ 上, 对自由 Lie 代数应用刚才的自然对称化, 再取各输入恰出现一次的部分, 得到右 Lie 算筹模的同构
  $ Assoc tilde.eq Comm compose Lie $
  这里用的是对称序列的复合, $Comm$ 的零输入分量为 $QQ$. 相容性来自对称化对 Lie 态射的自然性. 对右侧与 $frak(g)$ 作导出相对复合, 得到 $op("Sym")(frak(g))$ 作为 $U(frak(g))$ 的底层对象, 且等价保持过滤. 这个论证只使用有理系数, 有限张量积, 同伦余不变量和余极限, 因而适用于所设的 $cal(C)$. 另见 @GR-DAG2[第 6 章, 第 5.2 节].
]

#theorem(title: [普通环上的 PBW 定理])[
  设 $A$ 是任意普通交换环, $frak(g)$ 是经典 $A$-Lie 代数. 在普通模范畴中定义
  $ U_A^"cl" (frak(g))
    :=T_A^"cl" (frak(g))\/chevron.l x y-y x-[x,y] chevron.r $
  它满足到含幺结合 $A$-代数的普通伴随泛性质.

  若 $frak(g)$ 是投射 $A$-模, 字长过滤给出
  $ op("Sym")_A^"cl" (frak(g)) tilde.eq op("gr") U_A^"cl" (frak(g)) $
  特别地, $frak(g)->U_A^"cl" (frak(g))$ 单射. 若 $frak(g)$ 自由且有序基为 $e_i$, 则所有单项式
  $ e_(i_1) dots e_(i_n), quad i_1<=dots<=i_n $
  连同 $1$, 构成 $U_A^"cl" (frak(g))$ 的 $A$-基.
]

#proof[
  自由情形仍使用有序改写 $e_j e_i=e_i e_j+[e_j,e_i]$. 没有奇次输入, 所以不需要除以 $2$ 或 $3$; 重叠关系的相容性就是交替性与 Jacobi 恒等式. 由终止与正规形的唯一性得到所述基, 再取相伴分次.

  对一般投射模, 取 $P$ 使 $frak(g) plus.o P$ 自由, 并令 $P$ 为中心的交换 Lie 代数. 于是 $frak(g)$ 是自由底层的 Lie 代数 $frak(g) plus.o P$ 的 Lie 收缩项. 由函子性, 它的 PBW 映射是自由情形 PBW 同构的收缩项, 因而也是同构. 过滤一次部分给出所需单射.
]

上标 $"cl"$ 强调这里使用普通张量与普通商. 一般底环上不能直接把它当成导出包络代数. 在特征零域上, 两者对离散对象一致, 所以上述有序单项式就是之前 $U(frak(g))$ 的 PBW 基.

#example(title: [交换代数与 Heisenberg 代数])[
  若 $frak(g)=op("triv")(V)$, 则
  $ U(frak(g)) tilde.eq op("Sym")(V) $
  作为结合代数成立, 右边取导出的自由交换代数. 在 $QQ$-代数 $A$ 上, $V=A$ 给出 $A[t]$, $V=A[1]$ 给出一个奇次生成元的外代数.

  在任意普通环 $A$ 上, 令 $frak(h)_3=A x plus.o A y plus.o A z$, $[x,y]=z$ 且 $z$ 中心. 经典包络代数由
  $ x y-y x=z, quad x z=z x, quad y z=z y $
  给出, PBW 基为 $x^a y^b z^c$. 例如 $A=ZZ$ 就给出整数上的 Heisenberg Lie 代数及其包络代数. 它的相伴分次是 $A[x,y,z]$, 自身的乘法则记住了非零括号.
]

=== 表示与 Hopf 结构

本小节在 $QQ$-线性的 $Mod_R$ 中比较算筹表示与包络代数的模. 普通交换环上的经典 Lie 代数与经典包络代数也有同样的普通范畴结论.

#proposition(title: [表示就是包络代数的模])[
  对交换 $H QQ$-代数 $R$ 与 $frak(g) in LieAlg_R$, 有与底层忘却函子相容的等价
  $ Rep_R (frak(g)) tilde.eq Mod_(U_R (frak(g))) $
]
<prop-lie-modules-enveloping>

#proof[
  在 $V$ 上给出右边的模结构, 等价于给出结合代数态射 $U(frak(g))->op("End")_R (V)$. 根据 $U$ 的伴随泛性质, 这等价于 Lie 态射 $frak(g)->gl(V)$, 即 $QQ$-线性语境下左边的结构. 这个伴随关系也适用于态射和全部高阶同伦, 所以得到无穷范畴等价.
]

#proposition(title: [包络代数的余交换 Hopf 结构])[
  在上述 $QQ$-线性假设下, $U_R (frak(g))$ 自然是余交换 Hopf 代数. 在 dg 模型的生成元上
  $ Delta(x)=x times.o 1+1 times.o x, quad epsilon(x)=0, quad S(x)=-x $
  因而上面的表示范畴等价也是对称幺半等价, 右边使用沿 $Delta$ 限制标量的底环张量积.
] <prop-enveloping-hopf>

#proof[
  映射 $x mapsto x times.o 1+1 times.o x$ 保持 Lie 括号, 所以由泛性质扩张为结合代数态射 $Delta$. 余结合与余交换的全部相容性可由下述自然等价统一给出:
  $ U(frak(g) plus.o frak(h)) tilde.eq U(frak(g)) times.o U(frak(h)) $
  两边的生成元满足各自的关系及两个因子间的分次交换关系; PBW 也直接验证这是等价. 因而 $U$ 把 Lie 对象的有限直积及其对角送到余交换余乘法.

  $x mapsto -x$ 给出到反代数的 Lie 态射, 扩张后得到反乘法的 $S$. 对极恒等式先在生成元上成立, 再由反乘法性与余乘法性推广到所有单项式. 在有理 dg 模型中这给出 Hopf 结构, 并通过自然的算筹构造传递到 $R$-模范畴. 最后的对称幺半结构由 @thm-hopf-module-symmetric-monoidal 给出.
]

这说明表示的 Leibniz 公式来自包络代数的原始元余乘法. 泛包络代数既把 Lie 运算转成结合运算, 又把表示的张量积接回 #chapter-ref(<chap-hopf-algebras>) 的 Hopf 理论.


== Ado 定理

本节回到特征零域 $k$. PBW 已经把离散 Lie 代数嵌入 $U(frak(g))$, 再通过左乘得到忠实表示. 但 $U(frak(g))$ 通常无限维. Ado 定理要把这个构造压缩到有限维, 同时保留对每个非零 Lie 元素的检测.

#theorem(title: [Ado 定理])[
  设 $k$ 是特征零域. 对任意离散有限维 $frak(g) in LieAlg_k$, 存在底层离散有限维的 $V in Rep(frak(g))$, 使
  $ rho:frak(g)->gl(V) $
  单射. 换言之, 每个这样的 Lie 对象都能忠实作用在 $cal(D)(k)$ 中的一个离散完美对象上.
] <thm-ado>

这里的单射是零次向量空间的单射. 这个定理没有断言任意高阶 Lie 对象都能嵌入某个完美对象的自同态 Lie 代数. 下面通过包络代数的有限维商证明它.

=== 幂零情形

#lemma(title: [按下中心列截断])[
  离散有限维幂零 Lie 代数 $frak(n)$ 有有限维忠实表示, 并且可以使 $frak(n)$ 的所有元素都作用为幂零算子.
]

#proof[
  若 $frak(n)=0$, 取平凡表示 $k$. 否则设 $gamma_(c+1)(frak(n))=0$. 选取适配下中心列的有序基 $e_i$, 令 $w_i$ 为 $e_i$ 所处的最大下中心列次数, 即
  $ gamma_j (frak(n))="span"{e_i | w_i>=j}, quad 1<=w_i<=c $
  Jacobi 恒等式归纳给出 $[gamma_a,gamma_b] subset gamma_(a+b)$, 所以把 $e_j e_i$ 改写为有序乘积加上括号时, 权重不会下降.

  给 PBW 单项式 $e_1^(a_1) dots e_d^(a_d)$ 赋权重 $sum_i a_i w_i$. 权重至少 $c+1$ 的单项式所张成的空间 $J$ 是双边理想, 因为乘法与改写均不降低总权重. 于是
  $ V=U(frak(n))\/J $
  有限维. 每个基元 $e_i$ 的权重至多为 $c$, PBW 给出 $J inter frak(n)=0$. 左乘作用若在 $V$ 上为零, 作用在 $1+J$ 上就说明该元素属于 $J$, 所以此表示忠实.

  每个 $frak(n)$ 元素的权重至少为 $1$, 故任意 $c+1$ 个元素的乘积作用为零. 特别地, 每个元素都作用为幂零算子.
]

=== 可解根上的有限维商

这一部分先设 $k$ 代数闭, 所有 Lie 代数和表示都有限维且离散.

#lemma(title: [可解 Lie 代数的幂零根])[
  若 $frak(a)$ 可解, 则
  $ frak(n):={x in frak(a) | ad_x " 在 " frak(a) " 上幂零"} $
  是其最大幂零理想, 称为*幂零根*. 它包含 $[frak(a),frak(a)]$ 与 $Z(frak(a))$, 并且任意导子 $D$ 满足
  $ D(frak(a)) subset frak(n) $
]

#proof[
  对伴随表示使用 Lie 定理, 将 $ad(frak(a))$ 同时上三角化. $frak(n)$ 是所有对角角色的核的交, 所以是理想; Engel 定理说明它幂零. 若 $frak(i)$ 是任意幂零理想, $x in frak(i)$ 的伴随作用先将 $frak(a)$ 送进 $frak(i)$, 随后在 $frak(i)$ 上迭代为零, 故 $x in frak(n)$. 这证明最大性.

  对导子 $D$, 构造可解的半直积 $k D times.l frak(a)$. 其伴随表示可同时上三角化, 因而导出代数的元素作用为严格上三角算子. 由于 $D(frak(a))=[D,frak(a)]$ 位于这个导出代数中, 限制作用到 $frak(a)$ 就得到所需包含. 特别地, 所有导子都保持 $frak(n)$. 这一观察也见 @Eti24Ado[命题 50.1].
]

#lemma(title: [把表示延伸到导子作用])[
  设 $frak(a)$ 可解, 幂零根为 $frak(n)$, 并已有有限维忠实表示 $rho_0$ 使 $frak(n)$ 作用为幂零算子. 若 $frak(b)$ 通过导子作用在 $frak(a)$ 上, 则 $frak(b) times.l frak(a)$ 有有限维表示, 它在 $frak(a)$ 上仍忠实, 在 $frak(n)$ 上仍为幂零作用.
]

#proof[
  延拓 $rho_0$ 为 $U(frak(a))->End_k (V_0)$, 记其核为 $K$, 并令
  $ I=K+U(frak(a)) frak(n) U(frak(a)) $
  由 Engel 定理, 存在 $q$ 使 $rho_0(frak(n))^q V_0=0$. 过滤
  $ V_0 supset rho_0(frak(n)) V_0 supset dots supset rho_0(frak(n))^q V_0=0 $
  对 $frak(a)$ 稳定, 因为 $frak(n)$ 是理想. $rho_0(I)$ 使过滤至少下降一阶, 所以
  $ I^q subset K, quad I^q inter frak(a)=0 $

  商 $V=U(frak(a))\/I^q$ 有限维. 确实, 对 $frak(a)$ 的每个基元 $e_i$, Cayley--Hamilton 定理给出首一多项式 $P_i$ 使 $P_i (e_i) in K subset I$, 因而 $P_i (e_i)^q in I^q$. 在 PBW 基中, 这些关系将各个 $e_i$ 的指数压到固定上界以下, 只剩有限多个单项式.

  将 $b in frak(b)$ 对 $frak(a)$ 的导子延拓为 $D_b:U(frak(a))->U(frak(a))$. 上一引理说明 $D_b (frak(a)) subset frak(n)$, 故 Leibniz 公式给出 $D_b (U(frak(a))) subset I$. 因而 $D_b$ 保持 $I$, 也保持 $I^q$.

  在 $V$ 上定义
  $ rho(b,a)(u)=D_b (u)+a u $
  导子恒等式给出 $[D_b,L_a]=L_(D_b a)$, 所以这是半直积的表示. 若 $a$ 的作用为零, 作用在 $1+I^q$ 上得到 $a in I^q inter frak(a)=0$, 因而它在 $frak(a)$ 上忠实. 又 $frak(n) subset I$, 所以任意 $q$ 个 $frak(n)$ 元素的乘积作用为零.
]

=== 一般情形的证明

#proof[
  *先处理可解 Lie 代数 $frak(a)$.* 我们同时证明, 忠实表示可使其幂零根 $frak(n)$ 作用为幂零算子. 对 $dim(frak(a)\/frak(n))$ 归纳. 维数为零时已经由幂零情形证明.

  否则, 因 $frak(a)\/frak(n)$ 交换, 可取包含 $frak(n)$ 的余维一理想 $frak(a)'$, 并写作 $frak(a)=k x times.l frak(a)'$. $frak(a)'$ 的幂零根对它的所有导子稳定, 所以也是 $frak(a)$ 的幂零理想; 由最大性, 它恰为 $frak(n)$. 归纳假设给出 $frak(a)'$ 的所需表示, 上一引理将其延伸到 $frak(a)$, 得到在 $frak(n)$ 上忠实且幂零的表示 $rho$.

  将它与伴随表示取直和. 因为
  $ ker(ad)=Z(frak(a)) subset frak(n), quad
    ker(rho) inter frak(n)=0 $
  所以 $rho plus.o ad$ 忠实. 对 $x in frak(n)$, $ad_x$ 也幂零, 因而归纳所需的附加性质得到保留.

  *再处理任意 $frak(g)$.* 由 Levi 分解,
  $ frak(g)=frak(s) times.l frak(r), quad frak(r)=rad(frak(g)) $
  对可解 Lie 代数 $frak(r)$ 取刚刚构造的表示. 再用延伸引理, 得到 $frak(g)$ 的有限维表示 $rho$, 它在 $frak(r)$ 上忠实. 中心是交换理想, 所以 $Z(frak(g)) subset frak(r)$. 于是
  $ ker(rho plus.o ad)=ker(rho) inter Z(frak(g))=0 $
  这就得到代数闭域上的 Ado 定理. 这条通过有限维包络代数商延伸表示的路线可参见 @Tao11Ado.

  *最后回到任意特征零域 $k$.* 在代数闭包 $overline(k)$ 上应用已证结论. 表示只有有限多个矩阵系数, 它们落在某个有限扩张 $K/k$ 中. 把所得有限维 $K$-表示限制标量为 $k$-表示, 维数仍有限, 且忠实性保持. 定理得证.
]

#example(title: [看见中心的表示])[
  以下两个经典表示在任意普通交换环 $A$ 上成立. 若 $frak(g)$ 交换且底层是有限投射 $A$-模, 则它在 $A plus.o frak(g)$ 上有忠实表示
  $ x dot (a,y)=(0,a x) $
  任意两个作用算子的复合都为零. 相比之下, 伴随表示在这里完全为零.

  Heisenberg Lie 代数 $frak(h)_3$ 在 $A^3$ 上有具体模型
  $ x mapsto E_(12), quad y mapsto E_(23), quad z mapsto E_(13) $
  因为 $[E_(12),E_(23)]=E_(13)$, 且后者与两者都交换. 三个矩阵单位 $A$-线性无关, 所以该表示忠实, 并检测到中心 $A z$.
]
