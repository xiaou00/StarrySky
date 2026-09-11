#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= $K_0$ 群 / The Group $K_0$ <chap-k0>

建议在阅读本章之前先阅读@chap-retract 的内容.

== 环的Grothendieck群

=== 基本定义

我们先来看一个最简单的情形, 固定一个交换环 $R$, 记 $Proj^"fg" (R)$ 为其上全体有限生成投射模的同构类对直和
$ [P] + [Q] = [P plus.o Q] $
构成的交换幺半群, 下面我们定义其Grothendieck群.

#definition(title:[环的Grothendieck群])[
  固定 $R$, 定义*Grothendieck群* $K_0 (R)$ 为 $(Proj^"fd" (R))^"gp"$ 为其群化.
]

这里群化函子的定义是典范的, 由显然的自由--遗忘伴随
$ (-)^"gp" : cat("CMon") arrows.lr Ab : U $
给出. 当 $R$ 是交换环时, $K_0 (R)$ 是一个交换环, 乘法由 $times.o_R$ 给出, 乘法单位元显然是 $1 = [R]$.

#proposition[
  若 $k$ 是域, 我们有 $K_0 (k) tilde.eq ZZ$.
]

#proof[
  域上的有限生成模就是有限维向量空间, 都是自由模, 因而也都是投射模. 而有限维向量空间由维数确定同构类, 直和对应维数相加. 所以
  $ Proj^"fg" (k) tilde.eq NN, quad [V] |-> dim_k V $
  两边群化, 就得到
  $ K_0 (k) tilde.eq NN^"gp" tilde.eq ZZ $
  具体地, $[V]-[W]$ 对应 $dim_k V-dim_k W$, 整数 $n$ 对应 $n[k]$.

  最后, $dim_k (V times.o_k W)=dim_k V dot dim_k W$, 且 $dim_k k=1$, 所以这个同构也保持乘法与单位.
]

#proposition[
  $K_0$ 是以下意义下的函子:

  + 函子 $Ring->Ab$, 定义为 $R|-> K_0 (R)$.
  + 函子 $CRing -> CRing$, 定义为 $R|-> K_0 (R)$.
]

#proof[略]

=== $K_0$ 中的自由模

当然, 这里说的自由模是有限生成自由模, 而有限生成自由模全部形如 $R^n$, 在 $K_0$ 中, 我们有显然的
$ [R^(m+n)] = [R^m]+[R^n] $
因此 $[R^n] = n[R]$. 事实上, 这给出了一个显然的子环 $ZZ dot [R] subset K_0 (R)$.

#proposition[
  任何 $K_0 (R)$ 的元素可以写成 $[P]-[R^n]$ 的形式, 其中 $P$ 是有限生成投射模, $n$ 是正整数.
]

#proof[
  任取 $x=[A]-[B]$. 由 @thm-finite-projective-characterizations, 可取有限生成投射模 $C$, 使 $B plus.o C tilde.eq R^m$. 于是
  $ x=[A plus.o C]-[R^m] $
  若 $m=0$, 两项同时加上 $[R]$ 即可.
]

=== 相等的判据

#proposition[
  对有限生成投射模 $P,Q$, 有
  $ [P]=[Q] "于" K_0 (R) quad <==> quad P plus.o R^n tilde.eq Q plus.o R^n "对某个" n>=0 $
] <prop-k0-stable-isomorphism>

#proof[
  群化的定义说明, $[P]=[Q]$ 当且仅当存在有限生成投射模 $T$, 使 $P plus.o T tilde.eq Q plus.o T$. 由 @thm-finite-projective-characterizations, 给 $T$ 补一个直和项成为 $R^n$, 就得到右边. 反过来, 在群里消去 $[R^n]$ 即可.
]

所以 $K_0$ 中相等, 表示补上同一个有限自由模以后同构, 不必是原来的模已经同构.

=== 有限乘积与滤过余极限

下面的环仍取交换环, 因而比较映射都是交换环同态.

#proposition(title: [保持有限乘积])[
  环的投影诱导典范同构
  $ K_0 (R_1 times dots times R_r) tilde.eq K_0 (R_1) times dots times K_0 (R_r) $
  另外 $K_0 (0)=0$, 所以也保持空乘积.
] <prop-k0-finite-products>

#proof[
  只看两个因子即可. 令 $R=R_1 times R_2$, $e_1=(1,0)$, $e_2=(0,1)$. 每个 $R$-模都分解为
  $ P tilde.eq e_1 P plus.o e_2 P $
  有限生成投射模恰对应一对有限生成投射模, 直和和张量积都逐分量计算. 因而
  $ Proj^"fg" (R) tilde.eq Proj^"fg" (R_1) times Proj^"fg" (R_2) $
  群化后就得到所需的环同构. 零环只有零模, 故 $K_0 (0)=0$.
]

例如, 对有限多个域 $k_1,dots,k_r$, 有 $K_0 (k_1 times dots times k_r) tilde.eq ZZ^r$; 各坐标分别记录对应分量的维数.

#proposition(title: [保持滤过余极限])[
  若 $R=varinjlim(i in I) R_i$ 是交换环的滤过余极限, 则自然映射
  $ varinjlim(i in I) K_0 (R_i) -> K_0 (R) $
  是同构. 左边可以在 $Ab$ 中计算, 并带上自然的交换环结构.
] <prop-k0-filtered-colimits>

#proof[
  关键是*有限矩阵只用到有限多个系数和等式*. 由 @thm-finite-projective-characterizations, 每个有限投射 $R$-模都是某个幂等矩阵 $e$ 的像. 它的系数来自某个 $R_i$; 再往后走一步, 就能使有限多个关系 $e^2=e$ 已在该阶段成立. 所以这个模来自某一阶段的有限投射模.

  两个这样的模之间的同构及其逆, 也能写成有限矩阵. 因而如果它们在 $R$ 上同构, 这份同构和互逆关系就在某个共同的后续阶段成立. 于是直和幺半群满足
  $ Proj^"fg" (R) tilde.eq varinjlim(i) Proj^"fg" (R_i) $
  群化是左伴随, 保持余极限, 所以再群化即得结论. 张量积与扩张标量相容, 故该同构也保持乘法. 参见 @Wei13[II, 2.1.6].
]

=== 幂零不变性与完备情形

#lemma[
  设 $I$ 是环 $R$ 的双边理想. 若 $I$ 幂零, 或更一般地, $R$ 关于 $I$-进拓扑完备且分离, 即自然映射
  $ R -> varprojlim(n>=1) R\/I^n $
  是同构, 则商映射诱导同构
  $ K_0 (R) tilde.eq K_0 (R\/I), quad [P] |-> [P\/(I P)] $
  当 $R$ 交换时, 这也是交换环的同构. 这里的完备性也称 $I$ 是*完备理想*; 幂零理想自动满足此条件.
] <lem-k0-nilpotent-complete>

#proof[
  关键是: *有限生成投射模模掉 $I$ 后, 同构类既不增加, 也不合并*.

  先看每个模都能提升. 沿用 @thm-finite-projective-characterizations 的幂等矩阵刻画 (其证明不需要交换性), 只需把 $R\/I$ 上的幂等矩阵提升到 $R$ 上. 任取矩阵提升 $E$, 它的误差 $D=E^2-E$ 的系数落在 $I$ 中. 作修正
  $ E' = E+(1-2E)D $
  若原来的误差落在 $I^m$ 中, 新误差就落在 $I^(2m)$ 中. 反复修正, 幂零时有限步后误差消失; 完备时则收敛到真正的幂等矩阵. 取其像, 就得到了所需的投射模.

  再看同构类不会合并. 若 $P\/(I P) tilde.eq Q\/(I Q)$, 由投射性, 可将这个同构及其逆提升为 $u:P->Q$ 和 $v:Q->P$. 两个复合都形如 $1+H$, 其中 $H$ 模掉 $I$ 后为零. 把投射模看作有限自由模的直和项, 就能用几何级数 $1-H+H^2-dots$ 求逆: 幂零时它是有限和, 完备时它收敛. 因而 $v u$ 和 $u v$ 都可逆, 所以 $u$ 是同构.

  于是 $[P]|->[P\/(I P)]$ 是直和幺半群的同构, 群化即得结论. 交换情形下它还保持张量积和单位. 参见 @Wei13[I, 习题 2.2; II, 引理 2.2].
]

#corollary[
  对任意交换环 $R$, 记 $R_"red"=R\/sqrt((0))$, 则
  $ K_0 (R) tilde.eq K_0 (R_"red") $
]

#proof[
  幂零根 $sqrt((0))$ 是其中所有有限生成理想 $J$ 的滤过并, 而每个这样的 $J$ 都幂零: 有限多个幂零生成元的充分长乘积必为零. 因此
  $ R_"red" tilde.eq varinjlim(J) R\/J $
  由上面的引理, 每个 $K_0 (R)->K_0 (R\/J)$ 都是同构; 再用 @prop-k0-filtered-colimits 即可.
]

=== 零维的情形

#definition(title: [零维交换环])[
  设 $R$ 是非零交换环. 若 $R$ 的 Krull 维数为零, 即每个素理想都是极大理想, 则称 $R$ 为*零维环*. 等价地, 素理想之间不存在严格包含
  $ frak(p) subset.neq frak(q) $
  几何上, 这表示 $Spec R$ 的每个点都是闭点.
]

域, 非零交换 Artin 环都是零维环. 这里说的是素理想链的长度, 并不要求环约化, 也不要求谱只有有限多个点.

#lemma[
  若 $R$ 零维, 则 $X=Spec R$ 是紧 Hausdorff 空间, 且开闭子集构成一组拓扑基. 特别地, 任意有限开覆盖都可以细分为有限个两两不交的开闭子集.
] <lem-zero-dimensional-spectrum>

#proof[
  只需先说明每个主开集 $D(f)$ 都是闭的. 任取 $frak(p) in V(f)$. 局部环 $R_(frak(p))$ 只有一个素理想, 所以其中的 $f\/1$ 幂零. 于是存在 $s in R without frak(p)$ 和 $N>=1$, 使 $s f^N=0$. 这给出一个与 $D(f)$ 不交的邻域 $D(s)$, 故 $V(f)$ 是开的.

  不同的极大理想可以被某个 $D(f)$ 及其补集分开, 所以 $X$ 是 Hausdorff 的; 再用谱的拟紧性, 就得到紧性. 对任意开覆盖, 先取有限个开闭集组成的细分覆盖, 再依次减去前面的开闭集, 就得到两两不交的细分. 参见 @Stacks26[Tag 04MG].
]

回顾一个基本对应: $Spec R$ 的开闭子集恰好形如 $D(e)$, 其中 $e^2=e$, 且 $e$ 唯一. 此时
$ R tilde.eq e R times (1-e)R, quad R_e tilde.eq e R $
也就是说, 把谱切成开闭两块, 就是在把环拆成两个直积因子. 参见 @Stacks26[Tag 00EE].

#theorem(title: [Pierce 定理])[
  对零维交换环 $R$, 秩函数诱导自然的交换环同构
  $ K_0 (R) tilde.eq [Spec R,ZZ] $
  这里 $[X,ZZ]$ 表示到离散空间 $ZZ$ 的连续映射, 也就是局部常值整数函数, 运算逐点计算. 因为目标离散, 取同伦类也得到同一个集合.
] <thm-k0-zero-dimensional>

#proof[
  记 $X=Spec R$. 由 @prop-finite-projective-local, 每个有限投射模 $P$ 在某个有限开覆盖上自由. 用 @lem-zero-dimensional-spectrum 将覆盖细分成互不相交的开闭块 $D(e_1),dots,D(e_r)$, 就有
  $ P tilde.eq (e_1 R)^(n_1) plus.o dots plus.o (e_r R)^(n_r) $
  其中 $n_i$ 是对应块上的秩. 两个模可取共同的细分, 所以秩函数相同就同构.

  反过来, 连续函数 $n:X->NN$ 只有有限多个值, 它的各个非空纤维给出开闭分拆. 在每块上取相应秩的自由模, 就得到一个秩函数为 $n$ 的有限投射模. 因而
  $ Proj^"fg" (R) tilde.eq [X,NN] $
  直和对应秩相加, 张量积对应秩相乘. 每个局部常值整数函数都是两个非负局部常值函数之差, 所以群化后得到 $K_0 (R) tilde.eq [X,ZZ]$. 这个同构把 $[P]-[Q]$ 送到
  $ frak(p) |-> dim_(kappa(frak(p))) (P times.o_R kappa(frak(p)))-dim_(kappa(frak(p))) (Q times.o_R kappa(frak(p))) $
  其中 $kappa(frak(p))$ 是剩余域. 扩张标量保持这些纤维的维数, 所以同构自然. 参见 @Wei13[II, 定理 2.2.2].
]

=== 秩映射与约化 $K_0$

下面 $R$ 是任意交换环, 不再要求零维, 并记 $X=Spec R$.

#definition[
  定义交换环
  $ H_0 (R):=[Spec R,ZZ] $
  其中 $ZZ$ 取离散拓扑, 加法与乘法逐点计算. 这里的 $H_0$ 专指*局部常值整数函数环*, 不表示奇异同调.
] <def-k0-rank-ring>

若 $X$ 非空且连通, 每个这样的函数都为常数, 所以 $H_0 (R) tilde.eq ZZ$; 整环就是一个例子. 若 $X$ 有有限个连通分支, 记为 $c$ 个, 则这些分支都开闭, 因而 $H_0 (R) tilde.eq ZZ^c$. 特别地, Noether 环总属于这种情形.

一般情形下, $H_0 (R)$ 的加法群仍是自由Abel群, 但未必有限生成. 这是拟紧空间上局部常值整数函数的一个非平凡事实, 这里直接引用 @Wei13[II, 例 1.4].

#definition(title: [秩映射])[
  对有限生成投射模 $P$, 其秩函数为
  $ op("rk")_P (frak(p)):=dim_(kappa(frak(p))) (P times.o_R kappa(frak(p))) $
  由 @prop-finite-projective-local, 它局部常值. 直和的秩相加, 张量积的秩相乘, 而 $R$ 的秩恒为 $1$, 因而得到环同态
  $ op("rk"):K_0 (R)->H_0 (R), quad [P]-[Q]|->op("rk")_P-op("rk")_Q $
]

#proposition(title: [秩映射有自然截面])[
  存在自然的环同态 $s:H_0 (R)->K_0 (R)$, 使
  $ op("rk") compose s=id_(H_0 (R)) $
  因而 $s$ 是单射, 可以将 $H_0 (R)$ 视为 $K_0 (R)$ 的一个自然子环.
] <prop-k0-rank-section>

#proof[
  给定 $h in H_0 (R)$. 因为 $X$ 拟紧, $h$ 只取有限多个值 $a_1,dots,a_r$. 写各个非空纤维为 $h^(-1)(a_j)=D(e_j)$, 其中 $e_j$ 是对应的幂等元. 定义
  $ s(h):=sum_(j=1)^r a_j [e_j R] $
  模 $e_j R$ 在 $D(e_j)$ 上秩为 $1$, 在其余点秩为 $0$, 所以 $op("rk")(s(h))=h$.

  对两个函数取共同的开闭分拆, 加法就逐块计算. 乘法也一样, 因为 $e R times.o_R e'R tilde.eq e e'R$ 对应开闭集的交. 常值函数 $1$ 对应 $[R]$, 所以 $s$ 是环同态. 环同态保持幂等元及这些分解, 也就给出了自然性.
]

当 $f:X->NN$ 非负时, $s(f)$ 由实际的投射模表示:
$ R^f:=(e_1 R)^(f_1) plus.o dots plus.o (e_r R)^(f_r), quad s(f)=[R^f] $
这里 $f_j$ 是 $f$ 在 $D(e_j)$ 上的值. 这样的模称为*逐分量自由模* (componentwise free): 在有限个开闭块上分别自由, 各块的秩可以不同. 特别地,
$ R^f plus.o R^g tilde.eq R^(f+g), quad R^f times.o_R R^g tilde.eq R^(f g) $
因此 $H_0 (R)$ 正是这些逐分量自由模在 $K_0 (R)$ 中给出的部分.

#definition(title: [约化 Grothendieck 群])[
  定义
  $ tilde(K)_0 (R):=ker(op("rk"):K_0 (R)->H_0 (R)) $
  称为*约化 Grothendieck 群*. 它也是 $K_0 (R)$ 的一个理想, 其元素恰好是在每个点上秩都为零的虚拟投射模类.
] <def-reduced-k0>

#proposition[
  有自然的Abel群分解
  $ K_0 (R) tilde.eq H_0 (R) plus.o tilde(K)_0 (R) $
  具体地, 分解及其逆分别为
  $ x |-> (op("rk")(x),x-s(op("rk")(x))), quad (h,y)|->s(h)+y $
] <prop-k0-rank-decomposition>

#proof[
  由 $op("rk") compose s=id$, 差 $x-s(op("rk")(x))$ 的秩为零. 上面两条映射显然互逆.
]

这里的直和是加法群的分解, 一般不是两个环的直积: $H_0 (R)$ 仍通过子环 $s(H_0 (R))$ 乘在理想 $tilde(K)_0 (R)$ 上.

*波浪号表示去掉秩以后剩下的稳定信息.* 例如, 秩恒为 $n$ 的有限投射模 $P$ 给出
$ [P]-[R^n] in tilde(K)_0 (R) $
它比较 $P$ 与同秩自由模 $R^n$. 由 @prop-k0-stable-isomorphism, 这个类为零当且仅当
$ P plus.o R^m tilde.eq R^(n+m) quad "对某个" m>=0 $
也就是 $P$ 稳定自由. 因而约化类检测的是稳定同构的差别, 不会检测补上自由项后已经消失的差别. 反过来, 用前面的 $[P]-[R^n]$ 表示法可知, $tilde(K)_0 (R)$ 中每个元素都能这样写, 此时零秩条件恰好要求 $P$ 的秩恒为 $n$.

若 $X$ 连通, 作为Abel群有 $tilde(K)_0 (R) tilde.eq K_0 (R)\/ZZ[R]$. 一般情形则应模掉整个加法子群 $s(H_0 (R))$. 若 $R$ 零维, 由 @thm-k0-zero-dimensional, 秩映射已是同构, 因而 $tilde(K)_0 (R)=0$.

#remark(title: [与幂零根的关系])[
  还有一个更强的事实: 对任意交换环 $R$, $tilde(K)_0 (R)$ 中的每个元素都幂零. 这个结论的证明涉及外幂诱导的运算, 此处引用 @Wei13[II, 推论 4.6.1].

  另一方面, $H_0 (R)$ 逐点取值于 $ZZ$, 所以是约化环; 因而 $K_0 (R)$ 中的任何幂零元都落在秩映射的核中. 两边合起来得到
  $ tilde(K)_0 (R)=sqrt((0))_(K_0 (R)), quad K_0 (R)_"red" tilde.eq H_0 (R) $
  这里说的是每个元素各自幂零, 不要求整个理想有统一的幂零次数. 定义中的"约化"是去掉秩部分; 从环的意义看, 这个约化群本身恰好组成 $K_0 (R)$ 的幂零根.
]

#theorem[
  设 $R$ 是Dedekind整环, 则 $tilde(K)_0 (R) tilde.eq "Cl"(R), H_0 (R) tilde.eq ZZ$.
]

#proof[
  $R$ 是整环, 所以 $Spec R$ 连通, 已有 $H_0 (R) tilde.eq ZZ$.

  用 Dedekind 整环上的 Steinitz 分解: 每个秩为 $n>=1$ 的有限投射模都形如 $R^(n-1) plus.o I$, 其中 $I$ 是非零分式理想; 而对两个这样的理想, 有
  $ I plus.o J tilde.eq R plus.o I J $
  这些理想都是秩为 $1$ 的有限投射模. 参见 @Wei13[I, §3, Dedekind domains].

  记 $op("cl")(I)$ 为 $I$ 的理想类. 定义
  $ Phi:"Cl"(R)->tilde(K)_0 (R), quad op("cl")(I)|->[I]-[R] $
  同一理想类的代表作为模同构, 所以定义良好. 上面的直和公式给出
  $ [I J]-[R]=([I]-[R])+([J]-[R]) $
  因而 $Phi$ 是群同态.

  *满射很直接.* 任取 $x in tilde(K)_0 (R)$, 写成 $x=[P]-[R^n]$, 其中 $n>=1$. 零秩条件说明 $P$ 的秩为 $n$, 再用 Steinitz 分解就得到
  $ x=[R^(n-1) plus.o I]-[R^n]=[I]-[R] $

  *单射则看最高外幂.* 若 $[I]-[R]=0$, 由 @prop-k0-stable-isomorphism, 存在 $m>=0$, 使
  $ I plus.o R^m tilde.eq R^(m+1) $
  两边取第 $m+1$ 次外幂, 左边是 $I$, 右边是 $R$, 所以 $I tilde.eq R$. 这意味着 $I$ 是主分式理想, 即 $op("cl")(I)=1$. 故 $Phi$ 也单射, 得到所需同构.
]

=== 稳定化与稳定范围

对交换环 $R$ 和整数 $n>=0$, 记 $cal(P)_n (R)$ 为秩恒为 $n$ 的有限生成投射模的同构类集合. 加上一个自由直和项给出*稳定化映射*
$ sigma_n:cal(P)_n (R)->cal(P)_(n+1) (R), quad P|->P plus.o R $
这里用 $P$ 简记它的同构类.

#lemma[
  映射
  $ alpha_n:cal(P)_n (R)->tilde(K)_0 (R), quad P|->[P]-[R^n] $
  与稳定化相容, 并诱导典范双射
  $ varinjlim(n) cal(P)_n (R) tilde.eq tilde(K)_0 (R) $
  左边先在 $Set$ 中取余极限; 直和诱导其加法, 使这个双射成为Abel群同构.
] <lem-reduced-k0-stabilization>

#proof[
  相容性就是
  $ [P plus.o R]-[R^(n+1)]=[P]-[R^n] $
  前面已说明, 每个约化类都能写成 $[P]-[R^n]$, 且 $P$ 的秩恒为 $n$, 所以诱导的映射满射.

  再看单射. 若两个代表映到同一个约化类, 先加上自由项, 把它们提高到同一个秩 $N$. 此时它们在 $K_0 (R)$ 中的类相等. 由 @prop-k0-stable-isomorphism, 再各加上同一个 $R^m$ 后便同构, 所以它们在余极限中本来就是同一个元素.

  最后, 直和与稳定化相容, 所以在余极限上给出加法. 自由模都代表零; 由 @thm-finite-projective-characterizations, 每个有限投射模都能补成有限自由模, 补项便代表它的加法逆元. 因而左边确实是Abel群, 且上述双射保持加法. 参见 @Wei13[II, 引理 2.3.1].
]

#corollary[
  设 $R$ 是 Krull 维数为 $d<oo$ 的交换 Noether 环. 则对每个 $n>d$, 上面的映射都是双射:
  $ alpha_n:cal(P)_n (R) ->^~ tilde(K)_0 (R), quad P|->[P]-[R^n] $
  更一般地, 若交换环 $R$ 的 Bass 稳定范围不超过 $d+1$, 结论仍成立.
] <cor-reduced-k0-stable-range>

#proof[
  先证 Noether 情形, 用 Bass--Serre 定理, 参见 @Wei13[I, 定理 2.3].

  *满射用 Serre 分裂定理.* 任取约化类 $x=[P]-[R^m]$, 其中 $P$ 的秩为 $m$. 若 $m<n$, 就同时加上自由项, 使 $m>=n$. 因为 $n>d$, Serre 分裂定理给出
  $ P tilde.eq Q plus.o R^(m-n), quad op("rk")_Q=n $
  所以 $x=[Q]-[R^n]=alpha_n (Q)$.

  *单射用 Bass 消去定理.* 若 $alpha_n (P)=alpha_n (Q)$, 则 $[P]=[Q]$. 由 @prop-k0-stable-isomorphism, $P,Q$ 稳定同构; 因为二者秩为 $n>d$, Bass 消去定理进一步给出 $P tilde.eq Q$.

  一般稳定范围下的版本引用 Bass 的稳定性结果, 参见 @Wei13[II, 推论 2.3.2; I, 习题 1.5].
]

这里的 Bass 稳定范围不超过 $s$, 指任意生成单位理想的元组 $(a_0,a_1,dots,a_s)$, 都能找到 $b_1,dots,b_s in R$, 使
$ (a_1+a_0 b_1,dots,a_s+a_0 b_s)=R $
左边表示这些元素生成的理想. 直观地说, 足够长的生成元组能通过调整去掉一个元素.

因此, 一般要不断加自由项, 才能用稳定同构类描述 $tilde(K)_0 (R)$; 在稳定范围内, 固定一个足够大的秩就够了. 这里的 $cal(P)_n (R)$ 本身没有由直和给出的加法, 因为直和会改变秩; 推论首先说的是集合的双射.

== 拓扑向量丛基础

前面的 $K_0$ 从投射模出发, 拓扑中的对应物是向量丛: 在每个点上放一个向量空间, 让它们连续地变化. 本节先讨论紧 Hausdorff 空间, 可以先想成有限 CW 复形. 涉及奇异上同调时取 CW 复形, 最后再用可表性推广到任意 CW 复形.

=== 向量空间如何连续地变化

#definition(title: [拓扑向量丛])[
  取 $bb(F) in {RR,CC}$. 空间 $X$ 上的有限秩 $bb(F)$-*向量丛*是连续映射 $p:E->X$, 每个纤维 $E_x=p^(-1)(x)$ 是有限维 $bb(F)$-向量空间, 且局部有同胚
  $ phi_U:p^(-1)(U) ->^~ U times bb(F)^n $
  它保持底空间, 在每个纤维上是线性同构. 各处的秩可以不同, 但秩函数 $x|->dim_(bb(F)) E_x$ 局部常值.

  同一底空间上的*丛态射*是逐纤维线性的连续映射; 可逆的丛态射称为丛同构. 秩恒为 $1$ 的向量丛称为*线丛*. 记平凡丛为
  $ epsilon_X^n:=X times bb(F)^n -> X $
] <def-topological-vector-bundle>

局部平凡化就是在一小块区域上连续地选一组基. 不同的基在交集上由可逆矩阵联系:
$ g_(i j):U_i inter U_j -> GL_n (bb(F)), quad g_(i j)g_(j k)=g_(i k) $
相容条件让这些局部乘积能粘起来. 能否通过换基拼出一组全局基, 决定了丛是否平凡.

#example(title: [两个线丛])[
  *Möbius 线丛*可写成
  $ M=([0,1] times RR)\/~, quad (0,t)~(1,-t) $
  底空间是 $S^1=[0,1]\/ (0~1)$. 绕一圈后方向反转, 所以这个实线丛不平凡. 它把通常 Möbius 带的每条纤维延长成了整条 $RR$.

  射影空间 $bb(F) PP^n$ 上有*典范线丛*
  $ gamma_1:= {(ell,v) in bb(F) PP^n times bb(F)^(n+1) | v in ell} -> bb(F) PP^n $
  每个点 $ell$ 代表一条直线, 纤维就取这条直线.
]

=== 拉回, 运算与平凡补项

对连续映射 $f:Y->X$, 拉回丛定义为
$ f^* E:=Y times_X E={(y,v) | f(y)=p(v)} ->Y, quad (f^* E)_y=E_(f(y)) $
拉回局部平凡化, 就知道这仍是向量丛. 直和, 张量积和对偶都在每条纤维上计算:
$ (E plus.o F)_x=E_x plus.o F_x, quad (E times.o F)_x=E_x times.o_(bb(F)) F_x, quad (E^*)_x=(E_x)^* $
这些运算与拉回相容. 截面是满足 $p compose s=id_X$ 的连续映射 $s:X->E$. 秩 $n$ 的丛平凡, 就是说能找到 $n$ 个截面, 在每点组成一组基.

#proposition(title: [向量丛可以补成平凡丛])[
  若 $X$ 紧 Hausdorff, 则对任意有限秩向量丛 $E$, 都存在向量丛 $F$ 和整数 $N$, 使
  $ E plus.o F tilde.eq epsilon_X^N $
] <prop-topological-bundle-complement>

#proof[
  取有限的平凡化覆盖和从属的单位分解 $(rho_i)$. 把局部坐标乘上 $rho_i$, 在覆盖外延拓为零, 合起来便得到逐纤维单射
  $ E ↪ epsilon_X^N $
  每点至少有一个 $rho_i$ 非零, 所以这个映射确实单射. 它的像是子丛, 在标准内积下取正交补 $F$ 即可. 参见 @Hat17VB[命题 1.4].
]

这与"有限投射模是有限自由模的直和项"很像. 取连续截面, 就能把两者联系起来:

#theorem(title: [Serre--Swan 定理])[
  设 $X$ 是紧 Hausdorff 空间, $bb(F) in {RR,CC}$. 连续截面函子给出范畴等价
  $ Gamma(X,-):cat("Vect")_(bb(F)) (X) ->^~ cat("Proj")^"fg" (C(X,bb(F))), quad E|->Gamma(X,E) $
  两边分别是有限秩向量丛与有限生成投射模的范畴. 其中 $C(X,bb(F))$ 是连续函数环, $Gamma(X,E)$ 是连续截面组成的模.
] <thm-serre-swan>

参见 @Wei13[I, 例 2.1.1 与习题 4.9].

=== 用分类空间表示向量丛

Grassmann 空间 $op("Gr")_n (bb(F)^N)$ 的点是 $bb(F)^N$ 中的 $n$ 维子空间. 每点的纤维取这个子空间本身, 就得到典范秩 $n$ 丛. 令
$ B O(n):=varinjlim(N) op("Gr")_n (RR^N), quad B U(n):=varinjlim(N) op("Gr")_n (CC^N) $
记对应的典范丛为 $gamma_n$. 这里 $O,U$ 是正交群与酉群; 选好内积后, 正交标架之间的变换就在这两个群里.

#theorem(title: [向量丛的分类])[
  对紧 Hausdorff 空间, 或更一般的仿紧 Hausdorff 空间 $X$, 有自然双射
  $ op("VB")_(RR,n) (X) tilde.eq [X,B O(n)], quad op("VB")_(CC,n) (X) tilde.eq [X,B U(n)] $
  左边是秩 $n$ 的丛的同构类, 右边是连续映射的同伦类. 对应由拉回给出:
  $ [f]|->[f^* gamma_n] $
] <thm-topological-bundle-classification>

#proofsketch[
  以紧空间上的复丛为例. 将 $E$ 嵌入 $epsilon_X^N$, 每个 $E_x$ 就是 $CC^N$ 中的 $n$ 维子空间. 这给出连续映射 $f:X->op("Gr")_n (CC^N)$, 且 $E tilde.eq f^* gamma_n$.

  将两个嵌入 $j_0,j_1$ 放进不同的直和坐标, 再用
  $ v|->(cos(pi t/2)j_0(v),sin(pi t/2)j_1(v)), quad 0<=t<=1 $
  连接. 它始终逐纤维单射, 所以不同嵌入给出的分类映射同伦. 反过来, 沿同伦拉回得到 $X times [0,1]$ 上的丛, 两端同构. 仿紧情形改用局部有限的单位分解. 详见 @Hat17VB[命题 1.7 与定理 1.16].
]

因此, 同伦的映射 $f,g:Y->X$ 拉回同一个丛, 结果同构. 特别地, 可缩的仿紧 Hausdorff 空间上所有有限秩向量丛都平凡. 分类映射把丛的粘合方式记成了一个同伦类.

=== 用特征类记录粘合信息 <sec-topological-characteristic-classes>

本小节取 $X$ 为 CW 复形, $H^i (X;A)$ 表示奇异上同调. 特征类用上同调类记录丛的信息, 并且与拉回相容.

#definition(title: [Chern 类与 Stiefel--Whitney 类])[
  复向量丛 $E$ 的 *Chern 类*与实向量丛 $V$ 的 *Stiefel--Whitney 类*分别为
  $ c_i (E) in H^(2i) (X;ZZ), quad w_i (V) in H^i (X;ZZ\/2ZZ) $
  这些类存在, 且由以下性质唯一确定:

  + *归一与维数:* $c_0=w_0=1$; 秩为 $n$ 时, $i>n$ 的类为零.
  + *自然性:* $c_i (f^* E)=f^* c_i (E)$, $w_i (f^* V)=f^* w_i (V)$.
  + *Whitney 直和公式:* 记 $c(E)=1+c_1 (E)+dots$, $w(V)=1+w_1 (V)+dots$, 则
    $ c(E plus.o F)=c(E)c(F), quad w(V plus.o W)=w(V)w(W) $
    右边使用上同调的杯积.
  + *线丛归一:* 实典范线丛在 $RR PP^oo$ 上的 $w_1$ 是 $H^1 (RR PP^oo;ZZ\/2ZZ)$ 的非零元; 复典范线丛在 $CC PP^oo$ 上满足 $c_1(gamma_1)=-h$, 其中 $h$ 是标准超平面类.
] <def-topological-characteristic-classes>

存在性暂引 @Hat17VB[定理 3.1--3.2]. 构造时先在典范丛上定义: 若 $E tilde.eq f^* gamma_n$, 就取 $c_i(E)=f^* c_i(gamma_n)$, 实情形同理. 同伦映射在上同调上作用相同, 所以这不依赖分类映射的选择.

这些性质立刻给出 $c(epsilon_X^n)=w(epsilon_X^n)=1$, 以及
$ c(E plus.o epsilon_X^m)=c(E), quad w(V plus.o epsilon_X^m)=w(V) $
也就是说, 补上平凡项不改变特征类. 特征类一般不能完整分类高秩丛, 但可以分类线丛:
$ op("VB")_(RR,1) (X) tilde.eq H^1 (X;ZZ\/2ZZ), quad op("VB")_(CC,1) (X) tilde.eq H^2 (X;ZZ) $
对应分别是 $w_1,c_1$. 这是因为 $B O(1)=RR PP^oo$ 是 $K(ZZ\/2ZZ,1)$, 而 $B U(1)=CC PP^oo$ 是 $K(ZZ,2)$. 线丛的张量积对应上同调类相加. 这里 $K(A,n)$ 指 Eilenberg--Mac Lane 空间, 不同于后面的 $K(X)$.

#example(title: [特征类能看出什么])[
  Möbius 线丛的 $w_1(M)!=0$ 记录了方向反转. 一般地, 实向量丛可定向当且仅当 $w_1(V)=0$.

  在 $S^2 tilde.eq CC PP^1$ 上, 典范复线丛 $L$ 满足 $c_1(L)=-h!=0$. 所以 $L$ 不平凡, 补上多少平凡项也不行.
]

把复丛 $E$ 看成实丛 $E_(RR)$, 两种特征类的关系是
$ w_(2i)(E_(RR))=c_i (E) mod 2, quad w_(2i+1)(E_(RR))=0 $
特别地, 复向量丛天然可定向. 参见 @May99[第 23 章, §7].

=== $K(X)$, $K O(X)$ 与 $K U(X)$

#definition(title: [向量丛的 Grothendieck 群])[
  记 $op("VB")_(bb(F)) (X)$ 为 $X$ 上有限秩 $bb(F)$-向量丛的同构类幺半群, 运算为直和. 定义
  $ K_(bb(F)) (X):=(op("VB")_(bb(F)) (X))^"gp", quad K O(X):=K_(RR) (X), quad K U(X):=K_(CC) (X) $
  通常简写 $K U(X)=K(X)$. 下文同时讨论实, 复情形时, 也统一写 $K$.

  元素写作 $[E]-[F]$, 称为*虚拟向量丛*. 张量积给出交换环结构
  $ [E][F]=[E times.o F], quad 1=[epsilon_X^1] $
] <def-topological-k-group>

群化本身适用于一般拓扑空间, 下面仍假设 $X$ 紧 Hausdorff. "虚拟"就是允许作形式差.

#proposition[
  连续映射 $f:Y->X$ 通过拉回给出环同态
  $ f^*:K(X)->K(Y), quad [E]-[F]|->[f^* E]-[f^* F] $
  因而 $K$ 是反变函子, 且具有同伦不变性. 此外,
  $ K O(*) tilde.eq K U(*) tilde.eq ZZ, quad K(X union.sq Y) tilde.eq K(X) times K(Y) $
] <prop-topological-k-functor>

#proof[
  拉回保持丛的运算, 也与复合, 同伦相容, 群化后仍然如此. 点上的丛由维数分类, 不交并上的丛则是一对分别在 $X,Y$ 上的丛. 群化后就得到上面的公式.
]

用 @prop-topological-bundle-complement 把减去的丛补成平凡丛, 就和投射模的情形一样, 每个类都能写成
$ x=[E]-[epsilon_X^n] $
而 $[E]=[F]$ 当且仅当对某个 $m>=0$, 有 $E plus.o epsilon_X^m tilde.eq F plus.o epsilon_X^m$. 所以 $K$ 群中的相等就是稳定同构. Serre--Swan 等价还给出
$ K O(X) tilde.eq K_0 (C(X,RR)), quad K U(X) tilde.eq K_0 (C(X,CC)) $

=== 约化 $K$ 群

记 $[X,ZZ]$ 为局部常值整数函数环. $ZZ$ 离散, 所以取连续映射或取其同伦类都一样. 秩给出环同态
$ op("rk"):K(X)->[X,ZZ], quad [E]-[F]|->(x|->dim E_x-dim F_x) $

#definition(title: [逐分量约化])[
  定义
  $ tilde(K)(X):=ker(op("rk"):K(X)->[X,ZZ]) $
  实, 复情形分别记为 $tilde(K O)(X)$, $tilde(K U)(X)$. 其中的虚拟丛在每点的秩都为零.
] <def-topological-reduced-k>

#proposition(title: [秩的自然分解])[
  对紧 Hausdorff 空间 $X$, 有自然的Abel群同构
  $ K(X) tilde.eq tilde(K)(X) plus.o [X,ZZ] $
] <prop-topological-k-rank-splitting>

#proof[
  对局部常值函数 $r:X->NN$, 在 $r^(-1)(n)$ 上取秩 $n$ 的平凡丛, 得到 $epsilon_X^r$. 对一般的 $h:X->ZZ$, 分开正负部分, 定义
  $ s(h):=[epsilon_X^(h_+)]-[epsilon_X^(h_-)], quad h_+=max(h,0), quad h_-=max(-h,0) $
  逐点看, $s$ 保持加法和乘法, 且 $op("rk") compose s=id$. 因此
  $ x|->(x-s(op("rk")(x)),op("rk")(x)), quad (u,h)|->u+s(h) $
  互为逆映射. 这个分解是加法群的直和, 一般不是环的直积.
]

若 $X$ 非空且连通, 则 $[X,ZZ]=ZZ$, 因而 $K(X) tilde.eq tilde(K)(X) plus.o ZZ$. 一个秩恒为 $n$ 的丛给出约化类 $[E]-[epsilon_X^n]$; 它为零, 就是说 $E$ 稳定平凡.

#remark(title: [与基点约化的区别])[
  常见的基点约化取 $ker(K(X)->K({x_0}))$, 只要求基点处的秩为零. 本节要求每点的秩都为零, 两者在连通空间上一致. 例如两点空间的 $K(X)=ZZ^2$: 本节的约化群为零, 基点约化群是 $ZZ$.
]

=== 稳定化为什么产生 $B U$ 与 $B O$

直和一个平凡线丛给出稳定化映射
$ op("VB")_(bb(F),n) (X)->op("VB")_(bb(F),n+1) (X), quad E|->E plus.o epsilon_X^1 $
在分类空间上, 这对应 $B U(n)->B U(n+1)$ 或 $B O(n)->B O(n+1)$. 取余极限, 得到*稳定分类空间*
$ B U:=varinjlim(n) B U(n), quad B O:=varinjlim(n) B O(n) $
这些包含可取成 CW 子复形包含, 所以这里也是同伦余极限.

#lemma[
  对紧 Hausdorff 空间 $X$, 映射 $E|->[E]-[epsilon_X^n]$ 诱导自然同构
  $ varinjlim(n) op("VB")_(bb(F),n) (X) tilde.eq tilde(K)(X) $
  左边先是集合的余极限, 加法由直和诱导.
] <lem-topological-k-stabilization>

#proof[
  约化类写成 $[E]-[epsilon_X^n]$ 后, $E$ 的秩必为 $n$, 所以映射满射. 若两个代表给出同一个类, 先把秩补到相同, 再用稳定同构判据, 它们便在某个后续阶段同构. 所以映射也单射.

  直和对应加法, 平凡丛代表零, 平凡补项给出加法逆元. 这正是 @lem-reduced-k0-stabilization 的丛版本.
]

#theorem(title: [拓扑 K 理论的同伦可表性])[
  对紧 Hausdorff 空间 $X$, 有自然同构
  $ K U(X) tilde.eq [X,ZZ times B U], quad tilde(K U)(X) tilde.eq [X,B U] $
  实情形同样有
  $ K O(X) tilde.eq [X,ZZ times B O], quad tilde(K O)(X) tilde.eq [X,B O] $
  右边取连续映射的同伦类, 加法由稳定直和诱导.
] <thm-topological-k-representability>

#proof[
  只证复情形. 合用 @thm-topological-bundle-classification 与 @lem-topological-k-stabilization, 得到
  $ tilde(K U)(X) tilde.eq varinjlim(n) [X,B U(n)] $
  在这些 CW 模型中, 紧空间到 $B U$ 的映射落在某个有限阶段. $X times [0,1]$ 也紧, 所以同伦也落在某个有限阶段. 于是
  $ varinjlim(n) [X,B U(n)] tilde.eq [X,B U] $
  最后用秩的分解:
  $ K U(X) tilde.eq [X,B U] plus.o [X,ZZ] tilde.eq [X,ZZ times B U] $
  这些对应都与拉回相容, 所以同构自然. 参见 @Wei13[II, 定理 3.1--3.2].
]

这个公式把虚拟丛分成两部分: $ZZ$ 坐标是秩, $B U$ 坐标是去掉秩后的类 $x-s(op("rk")(x))$. 若后者由 $f:X->B U(n)$ 表示, 它对应的虚拟丛就是
$ [f^* gamma_n]-[epsilon_X^n] $
沿 $g:Y->X$ 拉回, 就是把分类映射与 $g$ 复合. 这样, 不同空间上的 $K$ 群都由同一个表示空间来描述.

丛的直和与张量积, 分别给出 $ZZ times B U$ 上表示加法与乘法的映射. 可表性也保留了环结构.

=== 从零次函子到广义上同调

普通上同调也能这样表示. 对 CW 复形 $X$ 与Abel群 $A$, 有
$ H^n (X;A) tilde.eq [X,K(A,n)] quad (n>=0) $
两种理论可以放在一起看:

#table(
  columns: (1fr, 1fr, 1fr),
  table.header([理论], [表示空间], [映射记录的信息]),
  [$H^n (X;A)$], [$K(A,n)$], [$n$ 次上同调类],
  [$K U(X)$], [$ZZ times B U$], [秩与稳定复丛类],
  [$K O(X)$], [$ZZ times B O$], [秩与稳定实丛类],
)

#definition(title: [一般空间上的可表 K 理论])[
  对任意 CW 复形 $X$, 定义
  $ K U^0 (X):=[X,ZZ times B U], quad K O^0 (X):=[X,ZZ times B O] $
  对有限 CW 复形, 它们与前面向量丛群化得到的 $K U(X),K O(X)$ 一致.
]

上标 $0$ 为其他次数留出了位置. 非紧空间上的这个定义未必等于有限秩丛的群化: 丛未必有平凡补项, 分类映射也未必落在某个固定秩的阶段. 对一般拓扑空间, 可以先取 CW 逼近, 得到只依赖弱同伦型的版本.

要从零次函子得到一整套上同调, 还需要悬挂之间的相容性. Bott 周期性提供了这一步:
$ Omega^2 (ZZ times B U) tilde.eq ZZ times B U, quad Omega^8 (ZZ times B O) tilde.eq ZZ times B O $
由此可构造谱 $K U,K O$, 满足
$ Omega^oo K U tilde.eq ZZ times B U, quad Omega^oo K O tilde.eq ZZ times B O $
这里先引用 Bott 定理及谱的构造, 参见 @May99[第 24 章, §2] 与 @Wei13[II, §3].

所有次数便可统一定义. 对 $E=K U$ 或 $K O$ 以及 $q in ZZ$, 令
$ E^q (X):=pi_0 underline(Map)_(Sp) (Sigma^oo X_+,Sigma^q E) $
这里 $X_+$ 是给 $X$ 添上一个不交基点, 右边取稳定同伦类. 当 $q=0$, 由悬挂谱与 $Omega^oo$ 的伴随, 就回到 $[X,Omega^oo E]$. Bott 周期性还给出
$ K U^(q+2) (X) tilde.eq K U^q (X), quad K O^(q+8) (X) tilde.eq K O^q (X) $

对带基点空间 $Y$, 定义基点约化群 $E_*^q (Y):=pi_0 underline(Map)_(Sp) (Sigma^oo Y,Sigma^q E)$; 下标 $*$ 用来区别前面的逐分量约化. 若 $A subset X$ 是非空 CW 子复形, 令 $E^q (X,A):=E_*^q (X\/A)$. 将余纤维序列
$ Sigma^oo A_+ -> Sigma^oo X_+ -> Sigma^oo (X\/A) $
映射到 $E$, 就得到纤维序列, 进而得到长正合列
$ dots -> E^q (X,A) -> E^q (X) -> E^q (A) -> E^(q+1) (X,A) -> dots $
悬挂同构与 Mayer--Vietoris 序列也由此得到. 因此 $K$ 理论是一种广义上同调: 把普通上同调的系数谱 $H A$ 换成 $K U$ 或 $K O$, 就得到它.

#example(title: [从圆周与球面开始])[
  $B U$ 单连通, 所以 $K U(S^1)=ZZ$, 圆周上复丛的稳定类只剩下秩. 实情形则有
  $ K O(S^1) tilde.eq ZZ plus.o ZZ\/2ZZ $
  约化部分由 $[M]-[epsilon^1]$ 生成. $w_1$ 说明它非零, 两个 Möbius 线丛的直和平凡说明它的阶为 $2$.

  在 $S^2$ 上, 有 $tilde(K U)(S^2) tilde.eq pi_2 (B U) tilde.eq ZZ$. 一个生成元是
  $ beta=[L]-[epsilon^1] $
  其中 $L$ 是前面的典范复线丛. 把 $S^2$ 切成两个圆盘, 沿赤道用 $S^1->U(n)$ 粘合. 稳定后由 $pi_1(U)=ZZ$ 中的绕数分类, $L$ 对应一个生成元.

  Bott 周期性进一步给出, 对 $d>=1$,
  $ tilde(K U)(S^d) tilde.eq cases(ZZ & quad d "为偶数", 0 & quad d "为奇数") $
  丛的稳定分类就这样变成了同伦群的计算.
]

特征类也能用映射来理解: 稳定 Chern 类由 $B U->K(ZZ,2i)$ 表示, Stiefel--Whitney 类由 $B O->K(ZZ\/2ZZ,i)$ 表示. 与丛的稳定分类映射复合, 就得到它的特征类. 对虚拟丛, 定义
$ c([E]-[F])=c(E)c(F)^(-1), quad w([V]-[W])=w(V)w(W)^(-1) $
逆元在按次数完成的上同调环中计算, Whitney 公式保证定义良好. 特征类给出自然变换; 不过高次的 $c_i,w_i$ 一般不保持加法, 因为直和公式里还有低次类的乘积.

== 对称幺半范畴的 $K_0$ <sec-monoidal-k0>

=== 定义

把前面的"直和后取群化"抽象出来, 就得到下面的定义.

#definition(title: [对称幺半范畴])[
  *对称幺半范畴* (symmetric monoidal category) 是范畴 $C$, 带有"相加"的函子 $plus.o:C times C->C$ 和单位对象 $0$, 以及相容的自然同构
  $ (X plus.o Y) plus.o Z tilde.eq X plus.o (Y plus.o Z) $
  $ X plus.o 0 tilde.eq X tilde.eq 0 plus.o X, quad X plus.o Y tilde.eq Y plus.o X $
  也就是结合律, 单位律和交换律在自然同构的意义下成立, 并满足通常的相容条件; 交换两次为恒等.
] <def-symmetric-monoidal-category>

#definition(title: [对称幺半范畴的 Grothendieck 群])[
  设 $C$ 的对象同构类组成一个集合. 它们在 $plus.o$ 下形成交换幺半群, 其群化称为 *Grothendieck 群* $K_(0) (C)$.

  也就是说, $K_(0) (C)$ 是由对象同构类 $[X]$ 生成的Abel群, 关系为
  $ [X plus.o Y]=[X]+[Y], quad [0]=0 $
  元素可以写成形式差 $[X]-[Y]$.
] <def-symmetric-monoidal-k0>

例如, 有限生成投射模在直和下给出 $K_(0) (R)$; 实, 复向量丛在直和下给出 $K O(X),K U(X)$.

=== 典型例子

#example(title: [有限集合])[
  有限集合与映射组成范畴 $Fin$. 取不交并 $S union.sq T$ 为幺半运算, 空集 $∅$ 为单位, 就得到对称幺半范畴.

  有限集合的同构就是双射, 所以同构类由元素个数确定. 又有
  $ |S union.sq T|=|S|+|T| $
  因而同构类幺半群是 $NN$, 群化后得到
  $ K_(0) (Fin) tilde.eq ZZ, quad [S]-[T]|->|S|-|T| $
  单点集的类对应 $1$. 这里取的是不交并所给的幺半结构.
]

#example(title: [有限集合与笛卡尔积])[
  在 $Fin$ 上也可以取笛卡尔积 $S times T$ 为幺半运算, 单位是单点集. 此时同构类组成乘法幺半群 $(NN,times,1)$, 群化的关系变为
  $ [S times T]=[S]+[T] $
  因为空集满足 $S times ∅ tilde.eq ∅$, 所以
  $ [∅]=[S]+[∅] $
  在群中消去 $[∅]$, 就得到每个 $[S]=0$. 因而
  $ K_(0) (Fin,times)=0 $
  这说明 $K_0$ 依赖所选的幺半运算.
]

#example(title: [非空有限集合与笛卡尔积])[
  记 $Fin_(>0)$ 为非空有限集合与映射组成的范畴. 笛卡尔积仍给出对称幺半结构, 单位是单点集. 同构类按元素个数识别为乘法幺半群 $(NN_(>0),times,1)$.

  对正整数的乘法作群化, 就是允许取比值, 因而
  $ K_(0) (Fin_(>0),times) tilde.eq (QQ_(>0),times), quad [S]-[T]|->frac(|S|,|T|) $
  两个比值相等, 恰好表示交叉相乘后的集合等势; 每个正有理数又都能写成这样的比值. 左边的加法对应右边的乘法, 零元对应 $1$.

  由唯一素因子分解, 这个群也可以写成
  $ K_(0) (Fin_(>0),times) tilde.eq plus.o.big_(p "为素数") ZZ $
  各坐标记录比值中素数 $p$ 的指数, 可以为负. 参见 @Wei13[II, 例 5.2.1].
]

#example(title: [有限维向量空间])[
  域 $F$ 上的有限维向量空间与线性映射组成范畴 $cat("Vect")_(F)^"fd"$. 直和是幺半运算, 零向量空间是单位.

  维数把同构类幺半群识别为 $NN$, 所以
  $ K_(0) (cat("Vect")_(F)^"fd") tilde.eq ZZ, quad [V]-[W]|->dim_F V-dim_F W $
  这与有限集合按元素个数分类完全类似.
]

#example(title: [有限生成投射模])[
  环 $R$ 上的有限生成投射模与模同态组成范畴 $cat("Proj")^"fg" (R)$. 直和仍是幺半运算, 零模是单位. 按定义,
  $ K_(0) (cat("Proj")^"fg" (R)) tilde.eq K_(0) (R) $
  一般环上的投射模还有秩以外的稳定信息, 所以这个群可以比 $ZZ$ 更丰富.
]

#example(title: [向量丛])[
  固定紧 Hausdorff 空间 $X$. 实, 复向量丛与丛态射分别组成对称幺半范畴, 运算是逐纤维直和, 单位是零丛. 它们的 Grothendieck 群分别为
  $ K_(0) (cat("Vect")_(RR) (X)) tilde.eq K O(X), quad K_(0) (cat("Vect")_(CC) (X)) tilde.eq K U(X) $
  形式差 $[E]-[F]$ 就是前面的虚拟向量丛.
]

#example(title: [Burnside 环])[
  固定有限群 $G$. 有限 $G$-集合与 $G$-等变映射组成范畴 $Fin^G$. 对不交并取群化, 定义
  $ A(G):=K_(0) (Fin^G,union.sq) $
  笛卡尔积取对角作用 $g(s,t)=(g s,g t)$, 并对不交并分配, 因而给出乘法
  $ [S][T]:=[S times T] $
  单位是带平凡作用的单点集. 得到的交换环称为 *Burnside 环*.

  每个有限 $G$-集合唯一分解为轨道的不交并. 轨道都形如 $G\/H$, 且由子群 $H$ 的共轭类决定, 所以作为Abel群,
  $ A(G) tilde.eq plus.o.big_([H]) ZZ dot [G\/H] $
  这里 $[H]$ 遍历 $G$ 的子群共轭类.

  例如 $G=C_2$ 时, 只有单点轨道与二点自由轨道. 记后者的类为 $u$, 它与自身的直积是两个自由轨道, 所以
  $ A(C_2) tilde.eq ZZ[u]\/ (u^2-2u) $
  参见 @Wei13[II, 例 1.5 与 5.2.2].
]

#example(title: [表示环])[
  固定有限群 $G$. 有限维复表示与 $G$-等变线性映射组成范畴 $cat("Rep")_(CC) (G)$. 对直和取群化, 定义
  $ R(G):=K_(0) (cat("Rep")_(CC) (G),plus.o) $
  张量积取对角 $G$ 作用, 并对直和分配, 因而给出乘法
  $ [V][W]:=[V times.o_CC W] $
  单位是一维平凡表示. 得到的交换环称为*复表示环*.

  由 Maschke 定理, 每个复表示都是不可约表示的直和, 且各个不可约表示出现的重数唯一. 若 $V_1,dots,V_r$ 代表全部不可约表示的同构类, 则作为Abel群,
  $ R(G) tilde.eq plus.o.big_(i=1)^r ZZ dot [V_i] $
  乘法则由各 $V_i times.o_CC V_j$ 的不可约分解决定.

  例如 $G=C_2$ 时, 不可约表示只有平凡表示与符号表示. 记符号表示的类为 $s$, 因为 $s^2=1$, 所以
  $ R(C_2) tilde.eq ZZ[s]\/ (s^2-1) $
  后面讨论外幂运算时还会用到这个例子. 参见 @Wei13[II, 例 1.6 与 5.2.3].
]

这两个例子还有自然的联系: 将有限 $G$-集合 $S$ 换成以 $S$ 为基, 由 $G$ 置换基向量的表示 $CC[S]$, 就得到环同态
$ A(G)->R(G), quad [S]|->[CC[S]] $
因为不交并对应直和, 笛卡尔积对应张量积.

=== 共尾性

#definition(title: [共尾子范畴])[
  设 $(S,plus.o,0)$ 是对称幺半范畴, $T subset.eq S$ 是包含单位 $0$, 对 $plus.o$ 封闭的满子范畴. 若对每个 $X in S$, 都存在 $Y in S$ 和 $U in T$, 使
  $ X plus.o Y tilde.eq U $
  就称 $T$ 在 $S$ 中*共尾* (cofinal). 也就是说, 每个对象都能补上一项, 成为 $T$ 中的对象. 这里的共尾性是相对于幺半运算而言的.
] <def-monoidal-cofinal-subcategory>

#theorem(title: [共尾定理])[
  设 $T$ 在对称幺半范畴 $S$ 中共尾, 且 $S$ 的对象同构类组成一个集合. 则:

  + 包含诱导的群同态 $K_(0) (T)->K_(0) (S)$ 是单射, 因而可以把前者看作后者的子群.
  + 每个 $K_(0) (S)$ 中的元素都能写成 $[X]-[U]$, 其中 $X in S$, $U in T$.
  + 若 $[X]=[Y]$ 在 $K_(0) (S)$ 中成立, 则存在 $U in T$, 使
    $ X plus.o U tilde.eq Y plus.o U $
] <thm-monoidal-cofinality>

#proof[
  *先证第三条.* 由群化的定义, $[X]=[Y]$ 意味着存在 $Z in S$, 使
  $ X plus.o Z tilde.eq Y plus.o Z $
  用共尾性给 $Z$ 补一项: 取 $Z' in S$, 使 $Z plus.o Z' tilde.eq U in T$. 两边再加上 $Z'$, 就得到 $X plus.o U tilde.eq Y plus.o U$.

  *第一条随之得到.* 若 $[A]-[B] in K_(0) (T)$ 映到零, 则 $[A]=[B]$ 在 $K_(0) (S)$ 中成立. 由第三条, 存在 $U in T$, 使 $A plus.o U tilde.eq B plus.o U$. 两边都是 $T$ 中的对象, 而 $T$ 是满子范畴, 所以这已经是 $T$ 中的同构. 在 $K_(0) (T)$ 中消去 $[U]$, 原来的类就为零.

  *再证第二条.* 任取 $[A]-[B] in K_(0) (S)$. 给 $B$ 补一项 $C$, 使 $B plus.o C tilde.eq U in T$, 则
  $ [A]-[B]=[A plus.o C]-[B plus.o C]=[A plus.o C]-[U] $
  这就是所需的表示. 参见 @Wei13[II, 定理 5.3].
]

#example(title: [自由模])[
  记 $cat("Free")(R)$ 为有限生成自由 $R$-模组成的范畴, 幺半运算取直和. 由 @thm-finite-projective-characterizations, 每个有限生成投射模 $P$ 都有补项 $Q$, 使
  $ P plus.o Q tilde.eq R^n $
  所以 $cat("Free")(R)$ 在 $cat("Proj")^"fg" (R)$ 中共尾. 由 @thm-monoidal-cofinality,
  $ K_(0) (cat("Free")(R)) arrow.r.hook K_(0) (R) $
  它的像就是 $[R]$ 生成的循环子群, 因为 $[R^n]=n[R]$. 若 $R$ 满足*基数不变性*, 即 $R^m tilde.eq R^n$ 蕴含 $m=n$, 则
  $ K_(0) (cat("Free")(R)) tilde.eq ZZ $
  例如, 非零交换环都满足这个条件: 模掉一个极大理想, 比较剩余域上的维数即可.

  共尾定理的另两条, 正好给出前面的两个结论: 每个 $K_(0) (R)$ 中的元素都能写成 $[P]-[R^n]$, 而 $[P]=[Q]$ 当且仅当补上同一个有限自由模后同构.

  还可以只看*稳定自由模*, 即满足 $P plus.o R^m tilde.eq R^n$ 的模 $P$. 它们组成直和下的范畴 $cat("StFree")(R)$, 自由模在其中仍然共尾. 又因为
  $ [P]=(n-m)[R] $
  包含在群化后既单又满, 从而
  $ K_(0) (cat("Free")(R)) tilde.eq K_(0) (cat("StFree")(R)) $
  参见 @Wei13[II, 例 5.4.1].
]

#example(title: [Brauer 群])[
  固定域 $F$. 一个有限维 $F$-代数 $A$ 称为*中心单代数*, 若它的中心为 $F$, 且没有非零真双边理想. 这些代数与 $F$-代数同态组成范畴 $cat("Az")(F)$. 中心单代数的张量积仍然中心单, 所以 $times.o_F$ 给出对称幺半结构, 单位是 $F$.

  矩阵代数组成满子范畴 $cat("Mat")(F)$, 它满足
  $ M_m (F) times.o_F M_n (F) tilde.eq M_(m n) (F) $
  这个子范畴共尾. 事实上, 对任意 $A$, 取乘法顺序反过来的*反代数* $A^"op"$, 就有
  $ A times.o_F A^"op" tilde.eq End_F (A) tilde.eq M_d (F), quad d=dim_F A $
  第一个同构将 $a times.o b$ 送到 $x|->a x b$: 源是单代数, 所以这个保单位的映射单射; 两边维数相同, 因而是同构. 参见 @Stacks26[Tags 074G, 074I].

  矩阵代数的同构类按大小 $n>=1$ 识别为乘法幺半群 $NN_(>0)$. 因而与非空有限集合的例子一样,
  $ K_(0) (cat("Mat")(F),times.o_F) tilde.eq (QQ_(>0),times), quad [M_m (F)]-[M_n (F)]|->frac(m,n) $
  由共尾定理, 它是 $K_(0) (cat("Az")(F),times.o_F)$ 的子群. 再把这部分商掉, 就得到域 $F$ 的 *Brauer 群*:
  $ op("Br")(F):=K_(0) (cat("Az")(F),times.o_F) slash K_(0) (cat("Mat")(F),times.o_F) $
  也就是在群化关系之外, 再令所有矩阵代数的类为零:
  $ [A times.o_F B]=[A]+[B], quad [M_n (F)]=0 $

  共尾定理还说明, 商群中的每个类都由一个实际代数 $A$ 代表, 而
  $ [A]=[B] "于" op("Br")(F) quad <==> quad A times.o_F M_m (F) tilde.eq B times.o_F M_n (F) "对某些" m,n>=1 $
  右边显然给出相等的类. 反过来, 商群中相等意味着 $[A]-[B]$ 是两个矩阵代数类之差; 移项后用共尾定理, 再张量上同一个矩阵代数即可得到同构. 这正是通常的 *Brauer 等价*: 允许在两边作矩阵扩张.

  最后, $A times.o_F A^"op"$ 是矩阵代数, 所以 $-[A]=[A^"op"]$. 因而取反代数就给出逆元. 参见 @Wei13[II, 例 5.4.3] 与 @Stacks26[Tag 074J].
]

=== 等变向量丛与等变 $K$ 理论

固定有限群 $G$ 和带连续 $G$-作用的紧 Hausdorff 空间 $X$. 等变向量丛把前面的向量丛和群表示放到了一起.

#definition(title: [$G$-向量丛与等变 $K$ 群])[
  一个 *$G$-向量丛*是复向量丛 $p:E->X$, 连同 $E$ 上的连续 $G$-作用, 满足 $p(g e)=g p(e)$, 且每个 $g in G$ 都给出复线性同构
  $ g:E_x -> E_(g x) $
  它们与 $G$-等变的丛态射组成范畴 $cat("Vect")_G (X)$. 直和给出对称幺半结构, 定义
  $ K_G^0 (X):=K_(0) (cat("Vect")_G (X),plus.o) $
  张量积取对角作用, 给出乘法 $[E][F]=[E times.o F]$. 单位是 $X times CC$, 作用为 $g(x,z)=(g x,z)$, 因而 $K_G^0 (X)$ 是交换环.
] <def-equivariant-topological-k0>

若 $X$ 是一点, 一个 $G$-向量丛就是有限维复表示, 所以 $K_G^0 ("pt")=R(G)$. 更一般地, 在不动点 $x in X^G$ 处取纤维, 给出环同态
$ K_G^0 (X)->R(G), quad [E]|->[E_x] $
等变映射 $f:Y->X$ 也给出拉回 $f^*:K_G^0 (X)->K_G^0 (Y)$.

下面假设 $G$ 在 $X$ 上的作用平凡. 此时 $G$ 保持每条纤维, 但在纤维上的表示仍然可以非平凡. 对表示 $V$, 记 $underline(V)=X times V$, 其中 $g(x,v)=(x,g v)$.

#proposition(title: [按不可约表示分解])[
  设 $G$ 在 $X$ 上平凡作用, $V_1,dots,V_r$ 代表 $G$ 的全部不可约复表示. 对任意 $G$-向量丛 $E$, 存在唯一到同构的普通向量丛 $E_i$, 使
  $ E tilde.eq plus.o.big_(i=1)^r E_i times.o underline(V_i) $
  这里 $G$ 在 $E_i$ 上平凡作用. $E_i$ 称为相应的*重数丛*, 其纤维是
  $ (E_i)_x=Hom_G (V_i,E_x) $
] <prop-equivariant-bundle-isotypical-decomposition>

#proof[
  在向量丛 $underline(V_i)^* times.o E$ 上, 平均算子 $frac(1,|G|) sum_(g in G) g$ 是连续的幂等算子, 像正是上面的 $E_i$. 连续幂等矩阵的秩局部不变, 所以这些像确实组成向量丛.

  求值 $u times.o v|->u(v)$ 给出所需的丛映射. 在每条纤维上, 它就是有限群复表示的不可约分解, 因而是同构. 再取 $Hom_G (V_i,-)$, 由 Schur 引理恢复 $E_i$, 也就得到唯一性. 参见 @Wei13[II, 命题 5.5].
]

#corollary(title: [平凡作用时的等变 $K$ 群])[
  若 $G$ 在 $X$ 上平凡作用, 则有自然的环同构
  $ K U(X) times.o_ZZ R(G) ->^~ K_G^0 (X), quad [E] times.o [V]|->[E times.o underline(V)] $
] <cor-trivial-action-equivariant-k0>

#proof[
  上面的分解与直和相容, 所以群化后 $K_G^0 (X)$ 是 $r$ 份 $K U(X)$ 的直和. 而 $R(G)$ 作为Abel群, 恰以 $[V_1],dots,[V_r]$ 为基, 因而显示的映射是群同构. 它也保持张量积和单位, 所以是环同构. 参见 @Wei13[II, 推论 5.5.1].
]

例如, $C_2$ 平凡作用时, 每个等变丛都分成 $+1$ 和 $-1$ 两个特征子丛. 对应地,
$ K_(C_2)^0 (X) tilde.eq K U(X)[s] slash (s^2-1) $
其中 $s$ 是带符号作用的平凡线丛的类.

== Abel 范畴的 $K_0$ <sec-abelian-k0>

#link(<sec-monoidal-k0>)[前一节]从直和出发, 要求 $[x plus.o z]=[x]+[z]$. 在 Abel 范畴里, 还可以把一个对象拆成子对象和商对象. 这里把这种拆分也写成关系:
$ 0->x->y->z->0 quad ==> quad [y]=[x]+[z] $
这样得到的 $K_0$ 是短正合列的通用加性不变量. 下面先比较两种定义, 再用正合列和滤过做计算, 最后讨论局部化与导出范畴. 主要参考 @Wei13[II, 第 6 节] 与 @Stacks26[Tags 02MT, 0FDE].

=== 从短正合列到 Grothendieck 群

*回顾 Abel 范畴.*

#definition(title: [Abel 范畴])[
  一个范畴 $C$ 称为*加性范畴*, 若各 $Hom_C (x,y)$ 都是 Abel 群, 复合对两边都可加, 并且有零对象和有限双积 $x plus.o y$. 这里双积同时是积与余积, 带有通常的嵌入和投影.

  加性范畴 $C$ 称为 *Abel 范畴* (abelian category), 若每个态射 $f:x->y$ 都有核与余核, 且自然映射
  $ op("coim")(f):=x slash ker(f) -> Im(f):=ker(y->coker(f)) $
  是同构. 因而每个态射都能写成
  $ x ->> Im(f) arrow.r.hook y $
  参见 @Stacks26[Tag 0109].
] <def-abelian-category-k0>

对相邻两条态射 $x stretch(->)^i y stretch(->)^p z$, 在 $y$ 处*正合*是指 $Im(i)=ker(p)$. 一个*短正合列*
$ 0->x stretch(->)^i y stretch(->)^p z->0 $
则说明 $i$ 把 $x$ 识别为 $ker(p)$, 而 $p$ 把 $z$ 识别为 $y slash x$. 若 $p$ 有截面, 序列就分裂, 此时 $y tilde.eq x plus.o z$.

#example(title: [常见的 Abel 范畴])[
  域 $F$ 上的有限维向量空间, 有限 Abel 群, 以及环 $R$ 上的全部左模, 都组成 Abel 范畴. 若 $R$ 左 Noetherian, 有限生成左模也组成 Abel 范畴: 核仍有限生成, 余核显然如此.

  有限生成投射模一般只组成加性范畴. 例如在有限自由 $ZZ$-模范畴中, $2:ZZ->ZZ$ 是单态射也是满态射, 却不是同构, 因而这个范畴不是 Abel 范畴. 满态射的断言来自自由模没有 $2$-挠元: $u compose 2=v compose 2$ 蕴含 $u=v$.
]

以下默认范畴*本质小*, 即对象的同构类组成一个集合; 需要时可先选一个小骨架. 环上的模统一取左模.

*定义与泛性质.*

#definition(title: [Abel 范畴的 Grothendieck 群])[
  $K_0 (C)$ 是由对象同构类 $[x]$ 生成的 Abel 群, 对每个短正合列 $0->x->y->z->0$ 加入关系
  $ [y]=[x]+[z] $
  等价地, 从对象同构类上的自由 Abel 群出发, 商掉所有 $[y]-[x]-[z]$ 生成的子群.
] <def-abelian-grothendieck-group>

取全零短正合列得到 $[0]=0$; 取分裂短正合列得到 $[x plus.o y]=[x]+[y]$. 因而每个元素仍可写成 $[x]-[y]$.

#proposition(title: [加性不变量的泛性质])[
  设 $B$ 是 Abel 群. 给出群同态 $K_0 (C)->B$, 等价于给每个对象指定一个同构不变的值 $v(x) in B$, 使每个短正合列都满足
  $ v(y)=v(x)+v(z) $
  对应的群同态由 $[x]|->v(x)$ 唯一确定.
] <prop-abelian-k0-universal-property>

#proof[
  在自由 Abel 群上, 对生成元指定值就唯一确定一个同态. 它能通过商群, 恰好要求每个关系 $[y]-[x]-[z]$ 都映到零, 也就是上面的可加性.
]

例如, 维数给出 $K_0 (cat("Vect")_F^"fd")->ZZ$. 要证明它是同构, 只需再说明每个类都由一维空间生成.

*与直和群化的关系.*

为区分 @sec-monoidal-k0 中的直和群化, 记
$ K_0^"split" (C):=K_0 (C,plus.o) $
为只使用直和关系的*分裂 Grothendieck 群*. 再加入所有短正合列关系, 得到自然满射
$ K_0^"split" (C)->>K_0 (C) $
其核由短正合列给出的 $[y]-[x]-[z]$ 生成. 以下对 Abel 范畴 $C$, 不加上标的 $K_0 (C)$ 均按 @def-abelian-grothendieck-group 理解.

#example(title: [一个新的关系])[
  在有限 Abel 群范畴中, 对素数 $p$, 短正合列
  $ 0->ZZ slash p ZZ ->ZZ slash p^2 ZZ ->ZZ slash p ZZ ->0 $
  给出 $[ZZ slash p^2 ZZ]=2[ZZ slash p ZZ]$.

  这个等式在分裂 Grothendieck 群中不成立. 事实上, 令 $M[p]=ker(p\:M->M)$, 则 $dim_(bb(F)_p) M[p]$ 对直和可加. 它在左边取值 $1$, 在右边取值 $2$. 因而*加入短正合列关系, 确实会合并原来不同的类*.
]

若所有短正合列都分裂, 则上面的满射是同构. 特别地, 有限维向量空间和特征零下有限群的表示, 都与#link(<sec-monoidal-k0>)[前一节]的计算一致.

*函子性与基本构造.*

#proposition(title: [正合函子诱导群同态])[
  设 $F:C->D$ 是正合函子, 即保持短正合列的加性函子. 则
  $ K_0 (F):K_0 (C)->K_0 (D), quad [x]|->[F(x)] $
  良定义, 并保持恒等函子与复合. 自然同构的正合函子诱导同一个同态, 所以正合等价诱导 $K_0$ 的同构.

  若正合函子 $F',F,F''$ 之间有逐对象短正合的自然变换 $0->F'->F->F''->0$, 则
  $ K_0 (F)=K_0 (F')+K_0 (F'') $
] <prop-abelian-k0-exact-functors>

#proof[
  正合函子把定义关系送到定义关系, 所以由泛性质得到同态. 其余等式都可在生成元 $[x]$ 上检查.
]

这里需要正合性, 只保持直和并不足够. 上例中的 $M|->M[p]$ 是加性函子, 但它不能按 $[M]|->[M[p]]$ 诱导这两个 Abel 范畴的 $K_0$ 之间的同态.

#proposition(title: [有限乘积与滤过并])[
  Abel 范畴的有限乘积满足
  $ K_0 (C times D) tilde.eq K_0 (C) plus.o K_0 (D) $
  若 $C$ 是满 Abel 子范畴 $C_i$ 的滤过并, 且各包含函子正合, 则
  $ varinjlim(i) K_0 (C_i) tilde.eq K_0 (C) $
] <prop-abelian-k0-basic-colimits>

#proof[
  乘积范畴的短正合列逐分量计算, 而 $(x,y) tilde.eq (x,0) plus.o (0,y)$, 所以投影与嵌入给出第一式的互逆映射.

  第二式的满射性来自每个对象都在某个 $C_i$ 中. 若一个类在 $K_0 (C)$ 中为零, 这个等式只用到有限多个短正合列关系. 滤过性让这些对象和态射同时落在某个阶段, 等式便已在该阶段成立, 所以映射也单射.
]

=== 正合列与 Euler 特征

*从短正合列到长正合列.*

#proposition(title: [有限正合列的交错和])[
  对有限正合列
  $ 0->x_0->x_1->dots->x_n->0 $
  有 $sum_(i=0)^n (-1)^i [x_i]=0$. 特别地, 对任意态射 $f:x->y$,
  $ [y]-[x]=[coker(f)]-[ker(f)] $
] <prop-abelian-k0-exact-euler>

#proof[
  记 $b_i=Im(x_(i-1)->x_i)$, 约定两端 $b_0=b_(n+1)=0$. 正合性给出短正合列
  $ 0->b_i->x_i->b_(i+1)->0 $
  所以 $[x_i]=[b_i]+[b_(i+1)]$. 交错相加时, 每个中间项出现两次, 符号相反, 全部消去. 对 $0->ker(f)->x->y->coker(f)->0$ 应用这个结论, 就得到第二式.
]

#corollary(title: [有限滤过的可加性])[
  若 $0=x_0 subset.eq x_1 subset.eq dots subset.eq x_n=x$ 是有限子对象滤过, 则
  $ [x]=sum_(i=1)^n [x_i slash x_(i-1)] $
] <cor-abelian-k0-filtration>

#proof[
  将 $0->x_(i-1)->x_i->x_i slash x_(i-1)->0$ 给出的关系相加即可.
]

因此 $K_0$ 允许把对象换成有限滤过的各层. 各层怎样扩张成原对象, 在这个群里不会额外贡献一个类.

*有界复形的 Euler 特征.*

#definition(title: [Euler 特征])[
  设 $x^bullet$ 是 $C$ 中的有界上链复形, 微分 $d^i:x^i->x^(i+1)$ 满足 $d^(i+1) d^i=0$. 定义
  $ chi(x^bullet):=sum_i (-1)^i [x^i] in K_0 (C) $
  有界性保证这里只是有限和. 记 $z^i=ker(d^i)$, $b^i=Im(d^(i-1))$, 上同调对象为 $H^i (x^bullet)=z^i slash b^i$.
] <def-abelian-k0-euler-characteristic>

#theorem(title: [Euler 特征只依赖上同调])[
  对任意有界复形 $x^bullet$, 有
  $ chi(x^bullet)=sum_i (-1)^i [H^i (x^bullet)] $
  因而拟同构的有界复形有相同 Euler 特征, 正合的有界复形的 Euler 特征为零.
] <thm-abelian-k0-euler-cohomology>

#proof[
  逐次取核与像, 得到
  $ 0->z^i->x^i->b^(i+1)->0 $
  $ 0->b^i->z^i->H^i (x^bullet)->0 $
  所以 $[x^i]=[b^i]+[H^i (x^bullet)]+[b^(i+1)]$. 乘上 $(-1)^i$ 再求和, 两组边界项相消, 便得到公式. 参见 @Wei13[II, 命题 6.6].
]

若 $0->x^bullet->y^bullet->z^bullet->0$ 是有界复形的逐次短正合列, 则 $chi(y^bullet)=chi(x^bullet)+chi(z^bullet)$. 也可以先取上同调, 再对所得有限长正合列取交错和.

#example(title: [熟悉的 Euler 数])[
  对有限 CW 复形 $X$, 用域 $F$ 上的胞腔上链复形计算. 若第 $i$ 维有 $c_i$ 个胞腔, 则在 $K_0 (cat("Vect")_F^"fd") tilde.eq ZZ$ 中, 上面的公式成为
  $ sum_i (-1)^i c_i=sum_i (-1)^i dim_F H^i (X,F) $
  普通 Euler 数就是这个群值 Euler 特征在向量空间范畴中的情形.
]

*由长正合列构造同态.*

#proposition(title: [带高阶项的加性])[
  设函子 $T^i:C->D$, $i>=0$, 把每个短正合列 $0->x->y->z->0$ 送到自然的长正合列
  $ 0->T^0 (x)->T^0 (y)->T^0 (z)->T^1 (x)->dots $
  并且对每个对象, 只有有限多个 $T^i$ 非零. 则
  $ [x]|->sum_(i>=0) (-1)^i [T^i (x)] $
  给出群同态 $K_0 (C)->K_0 (D)$.
] <prop-abelian-k0-delta-functor>

#proof[
  对这条长正合列使用 @prop-abelian-k0-exact-euler. 每组三项的符号依次为 $(-1)^i,-(-1)^i,(-1)^i$, 所以所得等式正是交错和对短正合列的可加性.
]

这个结论说明, 当第零项本身不正合时, 可以把高阶项一并计入. 有限性是公式的一部分: 一般 Abel 群里没有无穷交错和这个操作.

=== 有限长度范畴

*滤过的共同细化.*

要用滤过计算 $K_0$, 先要知道不同滤过之间怎样比较.

#lemma(title: [Schreier 细化引理])[
  同一对象的两个有限子对象滤过, 都有细化, 使两边的非零商对象逐个同构, 只差排列次序.
] <lem-abelian-schreier-refinement>

#proof[
  设两个滤过为 $0=x_0 subset.eq dots subset.eq x_r=x$ 和 $0=y_0 subset.eq dots subset.eq y_s=x$. 在 $x_(i-1)$ 与 $x_i$ 之间插入
  $ x_(i,j):=x_(i-1)+(x_i inter y_j), quad 0<=j<=s $
  这里 $+$ 表示子对象之和. 对第二个滤过, 对称地插入 $y_(j,i):=y_(j-1)+(y_j inter x_i)$.

  子对象的同构定理给出
  $ x_(i,j) slash x_(i,j-1) tilde.eq (x_i inter y_j) slash ((x_(i-1) inter y_j)+(x_i inter y_(j-1))) $
  右边交换两个滤过后不变, 所以它也同构于 $y_(j,i) slash y_(j,i-1)$. 按 $(i,j)$ 配对这些商对象, 删去零项, 就得到结论.
]

*简单对象与 Jordan--Hölder 定理.*

#definition(title: [有限长度])[
  非零对象 $s$ 称为*简单对象*, 若它只有 $0$ 和自身两个子对象. 对象 $x$ 称为*有限长度的*, 若存在有限滤过
  $ 0=x_0 subset x_1 subset dots subset x_n=x $
  使每个 $x_i slash x_(i-1)$ 都简单. 这样的滤过称为*组成列*, 这些简单商对象称为*组成因子*.

  若 $C$ 的每个对象都有限长度, 就称 $C$ 为*长度范畴*.
] <def-abelian-length-category>

#theorem(title: [Jordan--Hölder 定理])[
  有限长度对象的组成因子, 连同每种因子出现的次数, 与组成列的选择无关. 特别地, 组成列的长度是一个良定义的整数, 记为 $ell(x)$.
] <thm-abelian-jordan-holder>

#proof[
  对两条组成列应用 @lem-abelian-schreier-refinement. 简单对象没有非平凡的子对象, 所以继续细化只会插入零因子, 不会改变原有的非零因子. 两条组成列因而有相同的简单因子及重数. 参见 @Stacks26[第 12.9 节].
]

有限长度对象的子对象与商对象也有限长度: 将组成列分别与子对象相交, 再映到商对象即可. 反过来, 若子对象与商对象有限长度, 把两边的组成列接起来就得到中间对象的组成列.

#theorem(title: [长度范畴的 $K_0$])[
  设 $C$ 是长度范畴, 用 $cal(S)$ 表示简单对象的同构类集合. 则
  $ K_0 (C) tilde.eq plus.o.big_(s in cal(S)) ZZ dot [s] $
  具体地, 若 $m_s (x)$ 是 $s$ 在 $x$ 中的组成重数, 则
  $ [x]=sum_(s in cal(S)) m_s (x)[s] $
  每个对象只出现有限多个非零重数.
] <thm-k0-length-category>

#proof[
  有限滤过的可加性说明简单对象生成 $K_0 (C)$. 对短正合列 $0->x->y->z->0$, 把 $x$ 的组成列和 $z$ 的组成列在 $y$ 中接起来, 由 Jordan--Hölder 定理得到
  $ m_s (y)=m_s (x)+m_s (z) $
  所以各 $m_s$ 都给出群同态 $K_0 (C)->ZZ$. 它们在简单对象上取值 $m_s (t)=delta_(s,t)$, 因而与送基向量到 $[s]$ 的映射互逆. 这同时证明生成性与线性无关性.
]

长度函数 $ell:K_0 (C)->ZZ$ 就是把所有组成重数相加. 若简单对象不止一种, 只看总长度通常会丢掉信息.

*几个计算.*

#example(title: [有限 Abel 群])[
  记 $Ab^"fin"$ 为有限 Abel 群范畴. 简单对象恰为 $ZZ slash p ZZ$, 其中 $p$ 遍历素数. 因而
  $ K_0 (Ab^"fin") tilde.eq plus.o.big_(p "为素数") ZZ $
  对有限群 $M$, 第 $p$ 个坐标是 $v_p (|M|)$, 即群阶中 $p$ 的指数. 这是因为短正合列的群阶相乘, 而每个简单因子的群阶是相应素数.

  若只取有限 $p$-群, 则 $K_0 tilde.eq ZZ$, 由 $[ZZ slash p ZZ]$ 生成. 例如 $[ZZ slash p^n ZZ]=n[ZZ slash p ZZ]$.
]

#example(title: [有限维代数的模])[
  设 $R$ 是域 $F$ 上的有限维代数. 每个有限生成 $R$-模都有限维, 严格的子模链使维数严格变化, 所以这些模组成长度范畴.

  简单模只有有限种: 任意简单模都是 $R$ 的商, 因而会出现在 $R$ 的组成列中. 若简单模代表为 $S_1,dots,S_r$, 则
  $ K_0 (Mod_R^"fg") tilde.eq ZZ^r $
  坐标是组成重数. 这里没有要求 $R$ 半单; 即使存在非分裂扩张, 结论也成立.
]

#example(title: [模特征下的群表示])[
  设 $G=C_p$, 域 $F$ 的特征为 $p$. 写 $t=g-1$, 就有 $F[G] tilde.eq F[t] slash (t^p)$. 这个环只有一个简单模 $F$, 对应平凡表示. 因而
  $ K_0 (cat("Rep")_F^"fd" (C_p)) tilde.eq ZZ, quad [V]|->dim_F V $
  任意有限维表示都能按组成列逐层换成平凡表示. 但它未必是平凡表示的直和, 所以这里使用的是短正合列关系.
]

=== 环的 $G_0$ 与投射模的 $K_0$

*有限生成模的 Grothendieck 群.*

#definition(title: [$G_0$ 与 Cartan 同态])[
  对左 Noetherian 环 $R$, 定义
  $ G_0 (R):=K_0 (Mod_R^"fg") $
  这里使用全部有限生成左模及其短正合列. 有限生成投射模的包含给出 *Cartan 同态*
  $ c_R:K_0 (R)->G_0 (R), quad [P]|->[P] $
] <def-g0-cartan-map>

这个映射良定义, 因为直和关系也是短正合列关系. 而投射模之间的短正合列都分裂: 若商对象投射, 满射便有截面. 所以前面定义的 $K_0 (R)$ 已包含投射模之间的全部短正合列关系.

左 Noetherian 假设保证有限生成模范畴是 Abel 范畴. 对非 Noetherian 环, 有限生成模的核可能不再有限生成; Abel 范畴的 $K_0$ 定义不能原样套用到这个子范畴. 参见 @Stacks26[Tag 0AZ5].

#example(title: [主理想整环])[
  设 $R$ 是主理想整环, $F$ 是其分式域. 对任意非零 $a in R$, 有
  $ 0->R stretch(->)^a R->R slash a R->0 $
  所以 $[R slash a R]=0$ 在 $G_0 (R)$ 中成立. 由有限生成模的结构定理, 每个 $M$ 都满足 $[M]=r[R]$, 其中 $r=dim_F (F times.o_R M)$.

  换到分式域是正合函子, 因而秩给出逆映射, 得到
  $ K_0 (R) stretch(->)^~ G_0 (R) tilde.eq ZZ $
  特别地, $G_0 (ZZ)=ZZ$. 每个有限 Abel 群在这里的类都为零, 虽然它在 $K_0 (Ab^"fin")$ 中通常非零. 一个类的含义依赖允许哪些对象和短正合列.
]

#example(title: [Cartan 同态不一定是同构])[
  取 $R=F[epsilon] slash (epsilon^2)$. 唯一的简单模是 $F=R slash (epsilon)$, 所以 $G_0 (R)=ZZ[F]$. 短正合列
  $ 0->(epsilon)->R->F->0, quad (epsilon) tilde.eq F $
  给出 $[R]=2[F]$.

  另一方面, $R$ 是局部环, 有限生成投射模都自由, 所以 $K_0 (R)=ZZ[R]$. 因而 Cartan 同态是
  $ ZZ stretch(->)^(times 2) ZZ $
  它不是满射. 局部环上投射模自由的理由是: 提升剩余域上的一组基, 由 Nakayama 引理得到分裂满射 $R^n->P$; 补项模掉极大理想后为零, 再用 Nakayama 引理便知补项为零. 参见 @Stacks26[第 10.55 节].
]

*有限投射分解给出同构.*

#theorem(title: [投射分解与 Cartan 同构])[
  设 $R$ 左 Noetherian, 且每个有限生成左模都有有限生成投射模组成的有限分解. 则 $c_R:K_0 (R)->G_0 (R)$ 是同构. 对分解
  $ 0->P_n->dots->P_1->P_0->M->0 $
  其逆映射为
  $ [M]|->sum_(i=0)^n (-1)^i [P_i] $
] <thm-cartan-finite-projective-resolution>

#proof[
  *先检查与分解的选择无关.* 两个投射分解 $P_bullet,Q_bullet$ 之间, 可以利用投射性逐次提升 $id_M$, 得到链映射 $P_bullet->Q_bullet$. 它诱导同调同构, 所以映射锥是有界正合的投射模复形, 第 $i$ 项为 $Q_i plus.o P_(i-1)$.

  有界正合的投射模复形逐段分裂: 从最右端的非零项开始, 满射到投射模必分裂, 核仍投射, 然后继续向左. 因此它在投射模的直和群化中已有交错和为零. 对映射锥应用这一点, 得到
  $ sum_i (-1)^i [Q_i]=sum_i (-1)^i [P_i] $

  *再检查对短正合列可加.* 给定 $0->M'->M->M''->0$, 选两端的有限投射分解 $P'_bullet,P''_bullet$. 马蹄引理构造中间项的分解, 第 $i$ 项为 $P'_i plus.o P''_i$. 构造的第一步是将 $P''_0->M''$ 提升到 $M$, 与 $P'_0->M'$ 合起来满射到 $M$; 三个核仍成短正合列, 于是逐次重复. 两端分解有限, 所得分解也有限.

  取交错和便得可加性, 所以公式诱导同态 $e:G_0 (R)->K_0 (R)$. 对投射模取长度零的分解, 得 $e c_R=id$. 对任意 $M$, 有限正合列的交错和又给出 $c_R e([M])=[M]$. 因而两者互逆. 参见 @Wei13[II, 第 7 节的 Resolution 定理].
]

例如, 左 Noetherian 且有限左整体维数的环满足假设. 对 $ZZ$ 和域上的有限变量多项式环, 都可以通过有限投射分解比较 $K_0$ 与 $G_0$. 定理只要求每个有限生成模各自有有限分解.

*函子性与乘法.*

以下令 $R,S$ 为交换 Noetherian 环. 若 $R->S$ 平坦, 则扩张标量正合, 给出 $G_0 (R)->G_0 (S)$. 若 $S$ 作为 $R$-模有限生成, 则限制标量保持有限生成性并且正合, 给出反方向的 $G_0 (S)->G_0 (R)$.

更一般地, 若 $S$ 在 $R$ 上有有限平坦维数, 则 Tor 长正合列给出同态
$ G_0 (R)->G_0 (S), quad [M]|->sum_(i>=0) (-1)^i [Tor_i^R (S,M)] $
各 Tor 模都是有限生成 $S$-模, 且高次消失. 证明与 @prop-abelian-k0-delta-functor 相同, 只是把长正合列改为同调次数.

对 Abel 范畴上的张量积, 若它对每个变量都正合, 才能直接用 $[x][y]=[x times.o y]$ 在 $K_0$ 上定义乘法. 有限维群表示满足这一点, 因为底层是在域上张量.

一般的 $G_0 (R)$ 则未必能这样相乘. 在上面的双数环例子中, $[R]=2[F]$; 若张量 $F$ 能直接作用在 $G_0 (R)$ 上, 就会得到 $[F]=2[F]$, 与 $G_0 (R)=ZZ[F]$ 矛盾.

不过, 有限投射模平坦, 所以总有自然的 $K_0 (R)$-模结构
$ K_0 (R) times G_0 (R)->G_0 (R), quad ([P],[M])|->[P times.o_R M] $
投射模这一边的直和可加性, 与一般模这一边的短正合列可加性, 恰好保证良定义. 若满足 @thm-cartan-finite-projective-resolution 的假设, 则可把 $K_0 (R)$ 的环结构传到 $G_0 (R)$, 其公式是
$ [M] dot [N]=sum_(i>=0) (-1)^i [Tor_i^R (M,N)] $
这是因为投射分解与 $N$ 张量后的 Euler 特征, 等于其 Tor 同调的交错和.

=== Dévissage 定理

长度范畴的计算有一个更一般的版本: 各层可以来自某个较小的 Abel 范畴, 不必全是简单对象.

#theorem(title: [Dévissage 定理])[
  设 $D subset.eq C$ 是满 Abel 子范畴, 包含函子正合, 并满足:

  + $D$ 对在 $C$ 中取子对象和商对象封闭.
  + 每个 $x in C$ 都有有限滤过, 各商对象属于 $D$.

  则包含诱导同构
  $ K_0 (D) ->^~ K_0 (C) $
] <thm-abelian-k0-devissage>

#proof[
  对 $x$ 选一条商对象属于 $D$ 的滤过, 定义
  $ e(x):=sum_i [x_i slash x_(i-1)] in K_0 (D) $
  *这个值与滤过无关.* 对两条滤过使用 @lem-abelian-schreier-refinement. 细化后的因子仍在 $D$ 中, 因为它们是原有因子的子商. 在 $K_0 (D)$ 中, 细化不改变各层之和; 两条细化的因子又逐个同构, 所以两次计算相同.

  *这个值对短正合列可加.* 对 $0->x->y->z->0$, 先选 $x,z$ 的滤过, 再把 $z$ 的滤过拉回到 $y$, 接在 $x$ 的滤过后面. 所得滤过的因子恰是两边的因子, 所以 $e(y)=e(x)+e(z)$.

  因而 $e$ 诱导群同态 $K_0 (C)->K_0 (D)$. 在 $D$ 中取一步滤过, 得到一个方向的复合为恒等; 在 $C$ 中用有限滤过的可加性, 得到另一个方向也为恒等. 参见 @Wei13[II, 定理 6.3].
]

这里没有要求 $D$ 对扩张封闭. 允许两个 $D$ 中的对象扩张出一个只在 $C$ 中的对象, 正是这个定理的常见用法.

#corollary(title: [$G_0$ 的幂零不变性])[
  设 $R$ 左 Noetherian, $I$ 是幂零双边理想. 将 $R slash I$-模视为 $R$-模, 诱导同构
  $ G_0 (R slash I) ->^~ G_0 (R) $
] <cor-g0-nilpotent-invariance>

#proof[
  令 $D$ 为被 $I$ 消去的有限生成 $R$-模组成的满子范畴. 它等价于 $Mod_(R slash I)^"fg"$, 并对子对象和商对象封闭. 若 $I^n=0$, 则任意 $M$ 都有有限滤过
  $ 0=I^n M subset.eq I^(n-1) M subset.eq dots subset.eq I M subset.eq M $
  各层都被 $I$ 消去, 所以可用 dévissage. 逆映射具体为
  $ [M]|->sum_(j=0)^(n-1) [I^j M slash I^(j+1) M] $
]

要注意同构的方向: 上面的正合函子是*限制标量*. 反方向不能一般地只取 $M slash I M$. 例如对 $R=F[epsilon] slash (epsilon^2)$, 正确的逆映射把 $[R]$ 送到 $2[F]$, 而单取 $R slash I$ 只得到一个 $F$.

#example(title: [固定支撑处的有限长度模])[
  对交换 Noetherian 局部环 $(R,frak(m))$, 有限长度模都被某个 $frak(m)^n$ 消去. 用 $frak(m)$ 的幂滤过, 各层都是剩余域 $K=R slash frak(m)$ 上的向量空间. 因而
  $ K_0 (Mod_R^"fl") tilde.eq K_0 (cat("Vect")_K^"fd") tilde.eq ZZ $
  这里 $"fl"$ 表示有限长度. 这个同构由 $R$-模长度给出. 幂次 $n$ 可以随对象变化, dévissage 只要求每个对象各自有有限滤过.
]

=== Serre 子范畴与局部化

*把一类对象看成零.*

#definition(title: [Serre 子范畴])[
  满子范畴 $S subset.eq C$ 称为 *Serre 子范畴*, 若它包含零对象, 对同构封闭, 并且对任意短正合列 $0->x->y->z->0$, 有
  $ y in S quad <==> quad x,z in S $
  等价地, 它对子对象, 商对象和扩张封闭. 此时 $S$ 本身是 Abel 范畴, 包含函子正合.
] <def-serre-subcategory-k0>

例如, 有限 Abel 群在有限生成 Abel 群中组成 Serre 子范畴. 固定素数 $p$ 后, 有限 $p$-群也组成 Serre 子范畴.

对这样的 $S$, 存在 *Serre 商范畴* $C slash S$ 和正合函子 $q:C->C slash S$. 它把 $S$ 中的对象变成零, 并满足泛性质: 任何将 $S$ 送到零的正合函子, 都唯一到自然同构地通过 $q$ 分解.

具体地, 保留 $C$ 的对象, 将所有核与余核都属于 $S$ 的态射形式地变成可逆态射. 商范畴中的态射可以写成
$ q(f) q(s)^(-1), quad x stretch(<-)^s w stretch(->)^f y, quad ker(s),coker(s) in S $
这个构造确实给出 Abel 范畴, 且 $q(x)=0$ 当且仅当 $x in S$. 此处引用商范畴的存在性与正合性, 参见 @Stacks26[Tag 02MS]; 下面直接证明它对 $K_0$ 的作用.

*局部化正合列.*

#theorem(title: [局部化定理])[
  设 $S$ 是本质小 Abel 范畴 $C$ 的 Serre 子范畴. 则有正合列
  $ K_0 (S)->K_0 (C) stretch(->)^(q_*) K_0 (C slash S)->0 $
  因而 $K_0 (C slash S)$ 是 $K_0 (C)$ 商掉所有 $S$ 中对象的类所生成的子群.
] <thm-abelian-k0-localization>

#proof[
  记 $N=Im(K_0 (S)->K_0 (C))$. $q$ 杀掉 $S$, 且商范畴的每个对象都来自 $C$, 所以已得到满射
  $ K_0 (C) slash N ->> K_0 (C slash S) $
  构造逆映射, 只需证明 $q(x)|->[x] "mod" N$ 对同构和短正合列都相容.

  *先看同构.* 若 $s:w->x$ 满足 $ker(s),coker(s) in S$, 由 @prop-abelian-k0-exact-euler,
  $ [x]-[w]=[coker(s)]-[ker(s)]=0 "mod" N $
  商范畴中的同构可表示为上面的分式, 且此时 $q(f)$ 也可逆, 所以 $ker(f),coker(f) in S$. 因而分式两端在商群中的类相同.

  *再看短正合列.* 任取商范畴中的 $0->q(x)->q(y)->q(z)->0$. 将第一个箭头表示为 $q(f)q(s)^(-1)$, 其中 $f:w->y$, $q(s):q(w)->q(x)$ 可逆. 由于这个箭头单射, $ker(f) in S$, 并且
  $ q(Im(f)) tilde.eq q(x), quad q(coker(f)) tilde.eq q(z) $
  所以这条序列同构于 $C$ 中短正合列 $0->Im(f)->y->coker(f)->0$ 的像. 刚才已检查同构相容, 现在由这个短正合列得到 $[y]=[x]+[z] "mod" N$.

  因而所需的逆映射良定义, 定理得证. 参见 @Stacks26[引理 12.11.3].
]

这个正合列的最左边通常不能补 $0$. 包含函子可以把原来非零的类送到零.

*环的局部化.*

设 $R$ 交换 Noetherian, $T subset.eq R$ 是乘法集. 令 $C_T$ 为有限生成 $T$-挠模组成的范畴, 即 $T^(-1) M=0$ 的模. 它是 $Mod_R^"fg"$ 的 Serre 子范畴, 且有等价
$ Mod_R^"fg" slash C_T tilde.eq Mod_(T^(-1) R)^"fg" $
这里的函子是局部化 $M|->T^(-1) M$. 有限表示和态射都只涉及有限多个分母, 清分母便可把它们带回 $R$; 局部化后消失的核与余核正是 $T$-挠模. 因而局部化定理给出
$ K_0 (C_T)->G_0 (R)->G_0 (T^(-1) R)->0 $
参见 @Wei13[II, 应用 6.4.1].

#example(title: [从整数到有理数])[
  取 $R=ZZ$, $T=ZZ without {0}$. 有限生成挠模就是有限 Abel 群, 而局部化得到 $QQ$. 前面的计算把局部化列写成
  $ plus.o.big_(p "为素数") ZZ stretch(->)^0 ZZ stretch(->)^~ ZZ->0 $
  左边记录各素数处的长度, 中间和右边记录秩. 每个生成元 $[ZZ slash p ZZ]$ 在中间都因 $0->ZZ stretch(->)^p ZZ->ZZ slash p ZZ->0$ 而消失.
]

=== 凝聚模的几何例子

设 $X$ 是 Noetherian 概形. 凝聚 $cal(O)_X$-模组成 Abel 范畴 $cat("Coh")(X)$, 定义
$ G_0 (X):=K_0 (cat("Coh")(X)) $
对仿射概形 $X=Spec R$, 凝聚模与有限生成 $R$-模的等价给出 $G_0 (X) tilde.eq G_0 (R)$. 这里取的是普通凝聚模.

若 $i:Z arrow.r.hook X$ 是闭子概形, $j:U arrow.r.hook X$ 是其开补集, 则有正合列
$ G_0 (Z) stretch(->)^(i_*) G_0 (X) stretch(->)^(j^*) G_0 (U)->0 $
理由是: 支撑在 $Z$ 上的凝聚模组成 Serre 子范畴. 它们被定义 $Z$ 的理想层的某个幂消去, 所以 dévissage 将这一子范畴的 $K_0$ 识别为 $G_0 (Z)$. 再用凝聚模的商范畴与 $cat("Coh")(U)$ 的等价, 就能应用局部化定理. 这个商范畴的等价使用开集上凝聚模可延拓的事实, 参见 @Wei13[II, 应用 6.4.2].

对紧合态射 $f:X->Y$, 导出前推的上同调仍凝聚, 且只有有限多次非零, 因而还得到
$ f_*:G_0 (X)->G_0 (Y), quad [M]|->sum_i (-1)^i [cal(H)^i (f_* M)] $
右边的 $f_* M$ 按前面的约定是整个导出对象. 上同调长正合列与 @prop-abelian-k0-delta-functor 保证这个公式可加. 特别地, 当 $Y=Spec F$ 时, 它给出
$ [M]|->chi(X,M)=sum_i (-1)^i dim_F H^i (X,M) $
所用的凝聚性与有限性是紧合前推的标准定理, 参见 @Stacks26[第 36.38 节].

=== 与有界导出范畴的联系

把 $C$ 中的有界复形组成的范畴按拟同构局部化, 得到有界导出范畴 $Dcat^b (C)$. 它是三角范畴, 短正合列给出区分三角. 对象 $x in C$ 视为仅在第零次非零的复形, 记为 $x[0]$.

#definition(title: [三角范畴的 $K_0$])[
  对本质小三角范畴 $D$, 用对象同构类 $[x]$ 生成 Abel 群, 并对每个区分三角
  $ x->y->z->x[1] $
  加入关系 $[y]=[x]+[z]$, 得到 $K_0 (D)$.
]

由三角 $x->0->x[1]->x[1]$ 得到 $[x[1]]=-[x]$, 因而 $[x[n]]=(-1)^n [x]$. 若在稳定无穷范畴中表述, 这里的关系就是由纤维序列给出的关系.

#theorem(title: [有界导出范畴不改变 $K_0$])[
  嵌入 $C->Dcat^b (C)$ 诱导自然同构
  $ K_0 (C) ->^~ K_0 (Dcat^b (C)) $
  逆映射为 $[x^bullet]|->sum_i (-1)^i [H^i (x^bullet)]$.
] <thm-k0-bounded-derived-category>

#proof[
  短正合列在导出范畴中给出区分三角, 所以嵌入确实诱导同态. 反方向取上同调的交错和: 区分三角给出上同调长正合列, 因而 @prop-abelian-k0-exact-euler 保证它尊重三角关系.

  在 $x[0]$ 上, 两个映射的复合显然是恒等. 对一般有界复形, 逐次截断给出区分三角
  $ tau_(<=n-1) x^bullet ->tau_(<=n) x^bullet ->H^n (x^bullet)[-n]->(tau_(<=n-1) x^bullet)[1] $
  这里 $tau_(<=n)$ 保留次数不超过 $n$ 的上同调, 消去更高次上同调. 从最低非零次数走到最高非零次数, 有限次使用这些三角和移位的符号规则, 得到
  $ [x^bullet]=sum_n (-1)^n [H^n (x^bullet)[0]] $
  所以另一个复合也是恒等. 参见 @Stacks26[Tag 0FCM].
]

这个证明只用到有限次截断. 因而对带有*有界* $t$-结构的本质小稳定无穷范畴, 同样有 $K_0 (C) tilde.eq K_0 (C^suit.heart)$: 每个对象都能由有限多个移位后的上同调对象组成, 心中的短正合列又给出纤维序列.

最后说明为什么一直强调有限性. 若一个 Abel 范畴允许可数直和, 对任意 $x$ 取
$ y=plus.o.big_(n>=0) x $
则 $y tilde.eq x plus.o y$, 所以 $[y]=[x]+[y]$, 在群中消去 $[y]$ 就得 $[x]=0$. 这称为 *Eilenberg 消去法* (Eilenberg swindle). 例如, 至多可数维的 $F$-向量空间组成的 Abel 范畴, 其 $K_0$ 就是零. 这解释了为什么这里使用有限生成模, 凝聚模和有界复形这些有限性条件.

== $lambda$-运算与 $lambda$-环

直和与张量积给出了 $K$ 群的加法和乘法, 外幂则给出一组新的运算. 本节沿着 @Wei13[II, §4] 的主线, 从外幂走到 Adams 运算, $gamma$-滤过和 Chern 特征. 主要例子是交换环的 $K_(0) (R)$, 以及紧 Hausdorff 空间的 $K O(X),K U(X)$.

=== 外幂怎样作用在虚拟对象上

先看实际的模或丛. 定义
$ lambda^n ([P]):=[Lambda^n P], quad lambda^n ([E]):=[Lambda^n E] $
其中 $Lambda^0 P=R$, $Lambda^0 E=epsilon^1$. 外幂仍是有限投射模或有限秩丛, 因为它与基变换相容, 且局部是自由对象的外幂.

#lemma(title: [外幂的直和公式])[
  对有限投射模 $P,Q$, 有自然同构
  $ Lambda^n (P plus.o Q) tilde.eq plus.o.big_(i+j=n) Lambda^i P times.o_R Lambda^j Q $
  向量丛也满足同一个公式.
] <lem-exterior-power-sum>

#proof[
  右边到左边的映射, 就是先把来自 $P$ 的向量排在前面, 再与来自 $Q$ 的向量作外积. 在一组局部基下, 左边的基按"取了几个 $P$ 中的向量"分组, 恰好得到右边. 所以这个自然映射局部是同构, 从而是同构.
]

把所有外幂放进一个形式幂级数:
$ lambda_(t) ([P]):=sum_(n>=0) [Lambda^n P]t^n $
直和公式便成为 $lambda_(t) ([P]+[Q])=lambda_(t) ([P])lambda_(t) ([Q])$. 常数项为 $1$, 所以这个级数可逆. 这就让外幂能作用在形式差上.

#proposition(title: [外幂延拓到群化])[
  外幂唯一地延拓为 $K_(0) (R)$ 上的运算 $lambda^n$, 满足直和公式. 具体地,
  $ lambda_(t) ([P]-[Q])=lambda_(t) ([P])lambda_(t) ([Q])^(-1) $
  $K O(X),K U(X)$ 上的构造相同.
] <prop-lambda-group-completion>

#proof[
  $lambda_t$ 是从直和幺半群到乘法群 $1+t K[[t]]$ 的幺半群同态. 由群化的泛性质, 它唯一地延拓为群同态. 取 $t^n$ 的系数, 就得到 $lambda^n$.

  也可以直接检查: 若两个形式差表示同一个类, 加上同一个补项后, 对应的直和相等. 对它们作用 $lambda_t$, 再消去可逆的级数, 就得到相同的商. 所以定义不依赖表示法.
]

例如,
$ lambda^2 (x+y)=lambda^2 (x)+x y+lambda^2 (y), quad lambda^2 (-x)=x^2-lambda^2 (x) $
因此单个 $lambda^n$ 一般不加性. 对虚拟对象取外幂, 也不能把减号直接搬到外面.

若 $n>=1$, 展开 $(1+t)^(-n)$ 还能得到计算公式
$ lambda^k ([P]-n)=sum_(i=0)^k (-1)^i binom(n+i-1,i)[Lambda^(k-i) P] $
这里 $n$ 表示自由模 $R^n$ 的类; 丛的情形同样成立.

=== 预 $lambda$-环与基本例子

#definition(title: [预 $lambda$-环])[
  交换环 $K$ 上的一组集合映射 $lambda^n:K->K$, $n>=0$, 称为*预 $lambda$-环结构*, 若
  $ lambda^0 (x)=1, quad lambda^1 (x)=x, quad lambda^n (x+y)=sum_(i=0)^n lambda^i (x)lambda^(n-i) (y) $
  等价地, $lambda_(t) (x)=sum_(n>=0) lambda^n (x)t^n$ 给出群同态
  $ (K,+)->(1+t K[[t]],dot) $
  与所有 $lambda^n$ 相容的环同态称为预 $lambda$-环同态.
] <def-pre-lambda-ring>

这里采用常见的现代术语. K-book 把这种较弱的结构直接叫作 $lambda$-环, 把稍后加入乘法与复合公理的结构叫作 *special $lambda$-ring*. 本节把后者称为 $lambda$-环, 避免混用.

立刻有 $lambda_(t) (0)=1$ 与 $lambda_(t) (-x)=lambda_(t) (x)^(-1)$. 反过来, 单凭这些加法公理, 还不能决定 $lambda^n (x y)$ 或 $lambda^m (lambda^n (x))$.

#example(title: [二项式结构])[
  在 $ZZ$ 上取
  $ lambda^n (a)=binom(a,n), quad lambda_(t) (a)=(1+t)^a $
  二项式恒等式正好给出预 $lambda$-环公理. 负整数也一样, 例如 $lambda^n (-1)=(-1)^n$.

  更一般地, 若环 $H$ 嵌入一个 $QQ$-代数, 且每个
  $ binom(h,n)=frac(h(h-1) dots (h-n+1),n!) $
  都落在 $H$ 中, 则称 $H$ 为*二项式环*, 并取同样的运算. $QQ$-代数和局部常值函数环 $[X,ZZ]$ 都是例子, 后者逐点计算.
]

#definition(title: [$lambda$-理想])[
  理想 $I subset.eq K$ 若满足 $lambda^n (I) subset.eq I$ 对所有 $n>=1$ 成立, 就称为 *$lambda$-理想*.
]

#proposition[
  预 $lambda$-环同态的核是 $lambda$-理想. 若 $I$ 是 $lambda$-理想, 则商环 $K\/I$ 继承预 $lambda$-环结构.
]

#proof[
  第一条来自同态与 $lambda^n$ 相容. 对第二条, 若 $a in I$, 则模 $I$ 有 $lambda_(t) (a)=1$. 因而 $lambda_(t) (x+a)=lambda_(t) (x)lambda_(t) (a)$ 与 $lambda_(t) (x)$ 的系数相同, 运算便能下降到商环.
]

外幂的秩为二项式系数, 所以秩映射
$ K_(0) (R)->H_(0) (R), quad K O(X)->[X,ZZ], quad K U(X)->[X,ZZ] $
都是预 $lambda$-环同态. 它们的核, 也就是前面的约化 $K$ 群, 因而都是 $lambda$-理想. 扩张标量, 丛的拉回和实丛的复化也与外幂相容.

=== $lambda$-环的公理

先把"像外幂一样计算"写成明确的公式. 记 $e_(i) (u_1,dots,u_r)$ 为第 $i$ 个初等对称多项式, 即所有 $i$ 个不同变量的乘积之和. 约定 $e_0=1$.

设 $x$ 形式上分成 $u_1+dots+u_r$, $y$ 分成 $v_1+dots+v_s$. 那么 $x y$ 的线项是所有 $u_i v_j$, 而 $lambda^n (x)$ 的线项是所有 $u_(i_1) dots u_(i_n)$. 对称多项式基本定理给出唯一的整系数多项式 $P_n,Q_(m,n)$, 使
$ e_(n) ((u_i v_j)_(i,j))=P_(n) (e_(1) (u),dots,e_(n) (u);e_(1) (v),dots,e_(n) (v)) $
$ e_(m) ((u_(i_1) dots u_(i_n))_(i_1<dots<i_n))=Q_(m,n) (e_(1) (u),dots,e_(m n) (u)) $
变量数取足够大即可, 添上零变量不改变这些多项式. 它们把外幂的乘法与复合规则编码成了整系数公式.

#definition(title: [$lambda$-环])[
  预 $lambda$-环 $K$ 若还满足
  $ lambda_(t) (1)=1+t $
  $ lambda^n (x y)=P_(n) (lambda^1 (x),dots,lambda^n (x);lambda^1 (y),dots,lambda^n (y)) $
  $ lambda^m (lambda^n (x))=Q_(m,n) (lambda^1 (x),dots,lambda^(m n) (x)) $
  就称为 *$lambda$-环*. 这就是 K-book 的 special $lambda$-ring.
] <def-special-lambda-ring>

例如, 两条低次公式是
$ lambda^2 (x y)=x^2 lambda^2 (y)+y^2 lambda^2 (x)-2lambda^2 (x)lambda^2 (y) $
$ lambda^2 (lambda^2 (x))=x lambda^3 (x)-lambda^4 (x) $
因此 $lambda^n$ 既不是一般的加法同态, 也不是一般的乘法同态. 公理规定的是这些具体的多项式关系.

#remark(title: [Witt 幂级数的说法])[
  同一套公理也能用 $W(K)=1+t K[[t]]$ 表达. 在这里把普通级数乘法当作加法, 再用 $P_n$ 定义新的乘法 $star$, 使
  $ (1+a t) star (1+b t)=1+a b t $
  更一般地, 两个形式分解相乘时, 取所有根的两两乘积. 因为结果对根分别对称, 各系数由 $P_n$ 给出, 无须真的在 $K$ 中找到根. 环的零元是级数 $1$, 单位是 $1+t$.

  同样用 $Q_(m,n)$ 定义 $W(K)$ 上的外幂运算. 环公理和外幂公理都可在形式根上验证, 再由整系数对称多项式下降. 于是 $K$ 是 $lambda$-环, 等价于 $lambda_t:K->W(K)$ 是 $lambda$-环同态. 这是大 Witt 向量环的一种符号约定; 换用 $f(-t)^(-1)$ 就得到常用的另一种幂级数约定.
]

#example(title: [自由 $lambda$-环])[
  环 $U=ZZ[s_1,s_2,dots]$ 有唯一的 $lambda$-环结构, 使 $lambda^n (s_1)=s_n$. 对任意 $lambda$-环 $K$ 和 $x in K$, 存在唯一的 $lambda$-环同态
  $ U->K, quad s_n|->lambda^n (x) $
  所以 $U$ 是一个生成元上的自由 $lambda$-环.

  构造方法是把 $s_i$ 看成形式根的初等对称多项式. 外幂仍给出对称多项式, 因而可唯一地写回 $s_i$; 每次计算只用有限多个变量. 公理在根上成立, 泛性质则直接来自 $P_n,Q_(m,n)$ 的公式.
]

=== 正元, 线元与分裂原理

#definition(title: [正结构])[
  设 $K$ 是预 $lambda$-环. 一个*正结构*包括带二项式运算的子预 $lambda$-环 $H subset.eq K$, 与 $lambda$ 相容的收缩 $epsilon:K->H$, 以及正元集合 $cal(P) subset.eq K$, 满足:

  + $NN subset.eq cal(P)$, 且 $cal(P)$ 对加法, 乘法与各 $lambda^n$ 封闭.
  + 每个 $x in I:=ker(epsilon)$ 都能写成 $p-q$, 其中 $p,q in cal(P)$.
  + 若 $p in cal(P)$, 则 $epsilon(p)=r in NN$, $lambda^i (p)=0$ 对 $i>r$ 成立, 而 $lambda^r (p)$ 可逆.

  称 $epsilon$ 为*增广*, 把 $epsilon(p)$ 看作 $p$ 的秩. 若每个 $p$ 都有正元补项 $q$, 使 $p+q=N in NN$, 就说 *$NN$ 在正元中共尾*.
] <def-lambda-positive-structure>

在 $K_(0) (R)$ 中, $H=H_(0) (R)$, $epsilon$ 是秩, 正元取秩恒定的有限投射模类. 在 $K O(X),K U(X)$ 中, 则取秩恒定的实际丛类, $H=[X,ZZ]$. 前面证明的平凡补项, 恰好说明这些例子的正元满足共尾条件. 即使原来的秩不恒定, 也能先在各个开闭块上补齐秩.

一个*线元*是满足 $lambda_(t) (ell)=1+ell t$ 的可逆元 $ell$, 并要求 $epsilon(ell)=1$. 正的秩 $1$ 元就是线元. 在 $lambda$-环中, 线元组成乘法群 $L$: 通用乘法公式给出
$ lambda^n (ell x)=ell^n lambda^n (x) $
取 $x=ell^(-1)$, 就得到逆元也是线元.

#definition(title: [分裂原理])[
  称带正结构的预 $lambda$-环满足*分裂原理*, 若每个正元 $p$ 都能在一个保持正结构的单射扩张 $K->K'$ 中写成线元之和
  $ p=ell_1+dots+ell_r, quad r=epsilon(p) $
  有限多个正元可依次扩张, 在同一个环中同时分裂.
] <def-lambda-splitting-principle>

分裂以后,
$ lambda_(t) (p)=product_(i=1)^r (1+ell_i t), quad lambda^n (p)=e_(n) (ell_1,dots,ell_r) $
所以外幂问题变成了对称多项式问题. 这里的单射很重要: 在扩张环中验证的等式, 能回到原环.

#theorem(title: [分裂判据与 K 群])[
  对带正结构且 $NN$ 共尾的预 $lambda$-环, 分裂原理等价于 $lambda$-环公理. 外幂给出的 $K_(0) (R),K O(X),K U(X)$ 都满足这些条件.
] <thm-k-lambda-splitting>

#proof[
  先看分裂原理如何给出公理. 在扩张中把正元分成线元, 乘积取两两相乘的线元, 外幂取不同线元的乘积. 于是乘法与复合恰好由 $P_n,Q_(m,n)$ 描述. 共尾性让零秩元素写成 $p-r$, 再用 $lambda_(t) (p-r)=lambda_(t) (p)(1+t)^(-r)$, 就把这些公式延拓到虚拟元素; $H$ 上用二项式公式. 单射性把等式带回 $K$.

  反方向和这些 K 群的分裂原理, 是这里使用的标准分裂定理, 参见 @Wei13[II, 定理 4.2.3, 以及第 4.2.2 段后的说明]. 分裂扩张的构造按原书作为工具引用: 抽象情形在相容的 $lambda$-环中逐次添加根; 复丛和代数几何中的 K 群也可借助旗丛与射影丛公式. 实 K 群使用抽象的 $lambda$-环扩张. 下面的运算, 滤过与幂零结论都从这些工具逐步证明.
]

#proposition(title: [行列式])[
  有自然的群同态
  $ det:(K,+)->(L,dot), quad det(p)=lambda^r (p) quad (r=epsilon(p)), quad det(h)=1 quad (h in H) $
  在本节的 K 群中, $L$ 就是线模或线丛的同构类群. 特别地, $K_(0) (R)$ 的 $L=Pic(R)$.
] <prop-lambda-determinant>

#proof[
  正元的最高外幂是线元. 若 $p,q$ 的秩分别为 $r,s$, 直和公式中只有一项能贡献最高次, 所以
  $ lambda^(r+s) (p+q)=lambda^r (p)lambda^s (q) $
  因而 $det$ 从正元延拓到它们的群化. 又有 $det(n)=1$, 配上 $det(H)=1$ 就得到 $K$ 上的同态.

  在分裂扩张中, $det(p)=product_i ell_i$, 与通常的最高外幂完全一致. 对共尾情形的任意线元 $ell$, 写成 $p-r$. 由 $lambda_(t) (p)=(1+ell t)(1+t)^r$, 比较最高系数得到 $ell=lambda^(r+1) (p)$. 所以这些线元确实都来自实际的线模或线丛.
]

=== Adams 运算与幂和

外幂对应初等对称多项式. 若想得到加性的运算, 更适合使用幂和 $sum_i ell_i^k$. Newton 恒等式正好把二者联系起来.

#definition(title: [Adams 运算])[
  定义 $psi^1 (x)=x$, 对 $k>=2$ 递归定义
  $ psi^k (x)=sum_(i=1)^(k-1) (-1)^(i-1) lambda^i (x)psi^(k-i) (x)+(-1)^(k-1) k lambda^k (x) $
  称为 *Adams 运算*. 有增广时, 另记 $psi^0=epsilon$, 视为取值于 $H subset.eq K$ 的运算.
] <def-adams-operations>

前几项是
$ psi^2 (x)=x^2-2lambda^2 (x), quad psi^3 (x)=x^3-3x lambda^2 (x)+3lambda^3 (x) $
递归式没有除法, 所以有挠元的环上也能使用. 等价的生成函数公式是
$ sum_(k>=1) psi^k (x)t^k=-t frac(frac(d,d t)lambda_(-t) (x),lambda_(-t) (x)) $
将分母乘到左边, 比较 $t^k$ 的系数, 就得到上面的递归式. 这里的商只是在求常数项为 $1$ 的级数的逆, 没有使用需要分母的对数级数.

#proposition(title: [Adams 运算的基本性质])[
  在 $lambda$-环中, 对 $j,k>=1$, 有
  $ psi^k (x+y)=psi^k (x)+psi^k (y), quad psi^k (x y)=psi^k (x)psi^k (y), quad psi^k (1)=1 $
  $ psi^j compose psi^k=psi^(j k), quad psi^k (ell)=ell^k quad (ell in L) $
  二项式环上的 $psi^k$ 是恒等. 对素数 $p$, 还有
  $ psi^p (x) equiv x^p mod p K $
] <prop-adams-properties>

#proof[
  对 $lambda_(-t) (x+y)=lambda_(-t) (x)lambda_(-t) (y)$ 求导并除以乘积, 就得到加性. 若 $x=sum_i ell_i$, 生成函数给出
  $ psi^k (x)=sum_i ell_i^k $
  此时乘法与复合公式都是直接计算. 它们是通用的整系数恒等式, 因而由 $lambda$-环公理对所有元素成立. 对带正结构的例子, 也可以分裂正元后, 再用加性处理形式差. 二项式环上代入 $lambda_(-t) (h)=(1-t)^h$, 就得到 $psi^k (h)=h$.

  最后的同余要在整系数通用环中验证: $sum_i u_i^p-(sum_i u_i)^p$ 的系数都被 $p$ 整除. 除以 $p$ 后仍是整系数对称多项式, 所以仍可用初等对称多项式表示, 再代入 $lambda^i (x)$. 这样证明不要求原环无挠, 也不需要从某个扩张环中消去 $p$.
]

当 $K$ 是 $QQ$-代数时, 可以反过来写
$ lambda_(t) (x)=exp(sum_(k>=1) (-1)^(k-1) frac(psi^k (x),k)t^k) $
所以有理系数下, Adams 运算决定全部 $lambda$-运算. 整系数下不能随便除以 $k$, 须保留原来的递归式.

=== $gamma$-运算与有限 $gamma$-维数

下面给 $K$ 配上前述正结构, 并记 $I=ker(epsilon)$. 换一次级数变量, 就能让外幂更适合处理零秩元素.

#definition(title: [$gamma$-运算])[
  定义
  $ gamma_(t) (x):=lambda_(t/(1-t)) (x)=sum_(n>=0) gamma^n (x)t^n $
  因而 $gamma^0 (x)=1$, $gamma^1 (x)=x$, 且
  $ gamma_(t) (x+y)=gamma_(t) (x)gamma_(t) (y) $
] <def-gamma-operations>

#lemma[
  对 $n>=1$, 有
  $ gamma^n (x)=lambda^n (x+n-1) $
  若 $p$ 是秩 $r$ 的正元, 则 $gamma^n (p-r)=0$ 对 $n>r$ 成立. 特别地,
  $ gamma_(t) (ell-1)=1+(ell-1)t quad (ell in L) $
] <lem-gamma-finite-degree>

#proof[
  展开换元后的级数, $t^n$ 的系数为
  $ sum_(i=1)^n binom(n-1,i-1)lambda^i (x) $
  另一方面, $lambda_(t) (x+n-1)=lambda_(t) (x)(1+t)^(n-1)$ 的第 $n$ 个系数也是它.

  对秩 $r$ 的正元, 直接算得
  $ gamma_(t) (p-r)=sum_(i=0)^r lambda^i (p)t^i (1-t)^(r-i) $
  这是次数至多 $r$ 的多项式. 取 $r=1$ 就得到线元公式.
]

称 $gamma_(t) (x-epsilon(x))$ 的次数为 $x$ 的 *$gamma$-维数*, 允许取 $oo$. 共尾条件保证每个元素的 $gamma$-维数有限: 先减去秩, 再将 $p-q$ 中的 $q$ 补成某个整数 $N$, 就得到 $p'-N$, 此时 $epsilon(p')=N$, 可用上面的引理.

=== 约化部分为什么幂零

#lemma(title: [多项式环中的单位])[
  若 $f(t)=1+a_1 t+dots+a_r t^r$ 在交换环 $K[t]$ 中可逆, 则每个 $a_i$ 都幂零.
]

#proof[
  对任意素理想 $frak(p)$, 将等式 $f(t)g(t)=1$ 降到整环 $(K\/frak(p))[t]$. 次数相加, 所以 $f$ 只能是常数. 因而每个 $a_i$ 都落在所有素理想中, 也就是落在幂零根中.
]

#theorem(title: [有限 $gamma$-维数给出幂零性])[
  若每个元素都有有限 $gamma$-维数, 则 $I=ker(epsilon)$ 是幂零元组成的理想: 每个 $x in I$ 都幂零.
] <thm-gamma-nilpotence>

#proof[
  对 $x in I$, $gamma_(t) (x)$ 与 $gamma_(t) (-x)$ 都是多项式, 并且
  $ gamma_(t) (x)gamma_(t) (-x)=gamma_(t) (0)=1 $
  因此它们是 $K[t]$ 中的单位. 上一引理说明 $gamma_(t) (x)$ 的所有正次系数都幂零, 特别是一次系数 $gamma^1 (x)=x$.
]

#corollary(title: [约化 K 群就是幂零根])[
  对交换环 $R$ 和紧 Hausdorff 空间 $X$, 有
  $ tilde(K)_(0) (R)=sqrt((0))_(K_(0) (R)) $
  $ tilde(K O)(X)=sqrt((0))_(K O(X)), quad tilde(K U)(X)=sqrt((0))_(K U(X)) $
] <cor-reduced-k-nilradical-proof>

#proof[
  平凡补项给出共尾性, 所以约化部分的每个元素都幂零. 反过来, 秩环 $H_(0) (R)$ 或 $[X,ZZ]$ 都是约化环, 任何幂零元的秩只能是零. 两个包含便给出等号. 这也补上了前面引用的幂零根结论.
]

#example(title: [不能省去有限性条件])[
  取 $C_2$ 的复表示环 $K=ZZ[s]\/ (s^2-1)$, 其中 $s$ 是符号表示的类, 增广取 $epsilon(s)=1$. 令 $u=s-1$, 则
  $ u^2=-2u, quad u^n=(-2)^(n-1)u !=0 $
  所以增广核不由幂零元组成. 原因是符号表示没有平凡表示补项. 实际上 $gamma_(t) (u)=1+u t$, 而 $gamma_(t) (-u)=(1+u t)^(-1)$ 是无限级数.
]

这里证明的是每个元素各自幂零, 还没有得到某个统一的 $N$ 使 $I^N=0$. 要进一步讨论统一的次数, 就需要滤过.

=== $gamma$-滤过

#definition(title: [$gamma$-滤过])[
  令 $F_gamma^0 K=K$. 对 $n>=1$, 定义 $F_gamma^n K$ 为以下元素生成的理想:
  $ gamma^(i_1) (x_1) dots gamma^(i_s) (x_s), quad x_j in I, quad i_j>=1, quad sum_j i_j>=n $
  这给出下降滤过
  $ K=F_gamma^0 K supset.eq F_gamma^1 K supset.eq F_gamma^2 K supset.eq dots $
] <def-gamma-filtration>

每个 $gamma^i (x)$ 都有零秩, 而 $gamma^1 (x)=x$, 所以 $F_gamma^1 K=I$. 定义还直接给出
$ F_gamma^a K dot F_gamma^b K subset.eq F_gamma^(a+b) K, quad I^n subset.eq F_gamma^n K $
于是伴随分次环
$ op("gr")_gamma K:=plus.o.big_(n>=0) F_gamma^n K\/F_gamma^(n+1) K $
的零次部分是 $H$, 每一层都是 $H$-模. 注意, $gamma$-滤过还把 $gamma^i (x)$ 放在第 $i$ 层, 因而通常比理想幂滤过包含更多元素.

#lemma(title: [线元生成时的滤过])[
  若 $K$ 作为 $H$-代数由线元生成, 则
  $ F_gamma^n K=I^n $
  特别地, 对通用 Laurent 环
  $ W_s=H[u_1,u_1^(-1),dots,u_s,u_s^(-1)], quad epsilon(u_i)=1 $
  取每个单项式为线元, 就有
  $ op("gr")_gamma W_s tilde.eq H[z_1,dots,z_s], quad z_i=[u_i-1] $
  其中 $z_i$ 的次数为 $1$.
] <lem-gamma-line-model>

#proof[
  每个零秩元素都能写成有限和 $sum_j h_(j) (ell_j-1)$, 其中 $h_j in H$, $ell_j$ 是线元. 二项式公式给出
  $ gamma_(t) (h(ell-1))=(1+(ell-1)t)^h $
  所以它的第 $i$ 个系数落在 $I^i$. 对有限和使用乘法公式, 仍有 $gamma^i (x) in I^i$. 因而 $F_gamma^n K subset.eq I^n$, 反向包含已知.

  对 $W_s$, 令 $z_i=u_i-1$, 就把环写成 $H[z_1,dots,z_s,(1+z_1)^(-1),dots,(1+z_s)^(-1)]$. 这些分母的常数项都是 $1$, 不改变按 $(z_1,dots,z_s)$ 分次得到的环. 因而伴随分次就是多项式环. $H$ 无挠, 所以这些分次层也无挠.
]

这里 $W_s$ 的运算可直接定义: 对单项式 $u^a$, 令 $lambda_(t) (h u^a)=(1+u^a t)^h$, 再对有限和相乘. 二项式环条件保证各系数仍在 $W_s$ 中.

后面还用到*带滤过的分裂原理*: 对有限次计算中涉及的元素, 可以选取分裂扩张 $K subset.eq K'$, 使
$ F_gamma^n K=K inter F_gamma^n K' $
并把 $F_gamma^n$ 中的指定元素写成 $H$-线性组合, 每项是至少 $n$ 个 $ell-1$ 的乘积. 这是分裂定理的标准加强版, 这里同原书一样作为工具引用, 参见 @Wei13[II, 定理 4.7 前的 Filtered Splitting Principle]. 它保证滤过中的同余也能从扩张环带回原环; 仅有环的单射还不够.

=== 秩与行列式

#theorem(title: [$gamma$-滤过的第一层])[
  对本节带正结构, 满足分裂原理的 $lambda$-环, 映射
  $ L->I\/F_gamma^2 K, quad ell|->ell-1 $
  是群同构, 逆映射由 $det$ 给出. 因而
  $ F_gamma^0 K\/F_gamma^1 K tilde.eq H, quad F_gamma^1 K\/F_gamma^2 K tilde.eq L $
] <thm-gamma-first-quotient>

#proof[
  先看群运算. 因为
  $ ell m-1=(ell-1)+(m-1)+(ell-1)(m-1) $
  最后一项落在 $F_gamma^2$, 所以线元的乘法对应商群中的加法.

  再看行列式. 分裂以后, $F_gamma^2$ 的元素是至少两个线元差的乘积的 $H$-线性组合. 系数 $h$ 可以先吸收到第一个因子 $h(ell-1) in I$ 中, 将它写成同秩正元的差, 再分裂一次. 这样就得到整系数的线元差乘积之和. 对线元 $ell,m,n$, 有
  $ det((ell-1)(m-1)n)=frac((ell m n)n,(ell n)(m n))=1 $
  展开其余因子后, 更长的乘积也一样. 带滤过的分裂原理因此给出 $det(F_gamma^2)=1$, 所以 $det$ 能下降到商群.

  最后验证互逆. 对秩 $r$ 的正元 $p$, 在 @lem-gamma-finite-degree 的多项式公式中代入 $t=1$, 得到
  $ det(p)=sum_(i=0)^r gamma^i (p-r) equiv 1+(p-r) mod F_gamma^2 K $
  由正元的差生成 $I$, 可知任意 $x in I$ 都满足 $x equiv det(x)-1 mod F_gamma^2 K$. 对零秩差 $p-q$, 行列式也就是将 $gamma_(t) (p-q)$ 写成两个多项式的商后在 $t=1$ 处取值, 此时分母是可逆的 $det(q)$. 应用于 $gamma_(t) (ell-1)=1+(ell-1)t$, 就得到 $det(ell-1)=ell$. 所以两条映射互逆.
]

因此, 若记 $S K_(0) (R):=ker(det\:tilde(K)_(0) (R)->Pic(R))$, 就有
$ F_gamma^1 K_(0) (R)=tilde(K)_(0) (R), quad F_gamma^2 K_(0) (R)=S K_(0) (R) $
对有限 CW 复形, #link(<sec-topological-characteristic-classes>)[线丛分类]还给出
$ F_gamma^1 K O(X)\/F_gamma^2 K O(X) tilde.eq H^1 (X;ZZ\/2ZZ) $
$ F_gamma^1 K U(X)\/F_gamma^2 K U(X) tilde.eq H^2 (X;ZZ) $
所以前两层分别记录秩与行列式; 在拓扑中, 后者就是 $w_1$ 或 $c_1$.

=== 滤过何时终止

#proposition(title: [有限滤过与幂零理想])[
  若 $F_gamma^N K=0$, 则 $I^N=0$. 反过来, 假设每个元素的 $gamma$-维数有限, $I$ 是幂零理想, 且作为Abel群有限生成, 则 $gamma$-滤过在有限步后为零.
] <prop-gamma-finite-filtration>

#proof[
  第一条就是 $I^N subset.eq F_gamma^N K$.

  反过来, 设 $I^r=0$, 并取加法生成元 $x_1,dots,x_s$. 取 $d$ 大于等于所有 $gamma_(t) (x_i)$ 和 $gamma_(t) (-x_i)$ 的次数. 任意 $x in I$ 是这些正负生成元的有限和, 因而 $gamma_(t) (x)$ 是相应多项式的乘积.

  展开乘积时, 若取了至少 $r$ 个正次项, 系数就落在 $I^r=0$ 中. 所以所有未消失的项, 次数都不超过 $D=(r-1)d$. 这给出统一的界 $gamma^j (x)=0$ 对 $j>D$ 成立.

  在 $F_gamma^(r(D+1))$ 的生成元中, 每个非零因子的权重至多 $D$, 总权重这么大就至少要有 $r$ 个因子. 它们的乘积又落在 $I^r$, 所以这个滤过项为零.
]

同一个证明适用于有理系数下有限维的 $I$: 将整数次幂改为二项式展开即可, 因为 $I^r=0$ 使展开只剩有限项.

#corollary[
  对有限 CW 复形 $X$, $K O(X)$ 与 $K U(X)$ 的 $gamma$-滤过都在有限步后为零.
]

#proof[
  由胞腔长正合列和 Bott 系数群的有限生成性, 按胞腔数归纳, 两个 K 群都是有限生成Abel群. 因而约化理想 $I$ 也有限生成.

  由 @cor-reduced-k-nilradical-proof, 每个加法生成元 $x_i$ 都幂零, 设 $x_i^(a_i)=0$. 任意超过 $sum_(i) (a_i-1)$ 个生成元的乘积, 必有某个 $x_i$ 出现至少 $a_i$ 次. 所以 $I$ 是幂零理想, 再用上一命题即可.
]

对前面的表示环 $ZZ[s]\/ (s^2-1)$, 则由线元生成的引理得到 $F_gamma^n=I^n=2^(n-1)I$, 永远不为零. 这也说明有限滤过是额外的性质.

=== Adams 运算在每一层上做什么

#proposition(title: [分次上的 Adams 运算])[
  对 $x in F_gamma^n K$, $n>=1$, 以及 $k>=1$, 有
  $ psi^k (x) equiv k^n x mod F_gamma^(n+1) K $
  $ lambda^k (x) equiv (-1)^(k-1) k^(n-1) x mod F_gamma^(n+1) K $
  特别地, 这些运算保持 $gamma$-滤过, 而 $psi^k$ 在第 $n$ 个分次层上就是乘 $k^n$.
] <prop-adams-on-gamma-graded>

#proof[
  先在 @lem-gamma-line-model 的无挠通用环 $W_s$ 中计算, 记 $J=(u_1-1,dots,u_s-1)$. 对一个线元差, 有
  $ psi^k (u_i-1)=u_i^k-1 equiv k(u_i-1) mod J^2 $
  $psi^k$ 保持乘法, 并在 $H$ 上恒等, 所以在 $J^n\/J^(n+1)$ 上乘 $k^n$. 带滤过的分裂原理把这个结论带回 $K$.

  再算 $lambda^k$. 对 $x in J^n$, 用 Newton 递归式对 $k$ 归纳, 可知 $k lambda^k (x) in J^n$. 因为 $W_s\/J^n$ 无挠, 所以 $lambda^k (x) in J^n$. 递归式中其余乘积都落在 $J^(2n) subset.eq J^(n+1)$, 从而
  $ k^n x equiv (-1)^(k-1)k lambda^k (x) mod J^(n+1) $
  $W_s\/J^(n+1)$ 也无挠, 这时才可消去 $k$. 所得整系数同余再由分裂原理下降到 $K$. 原环可以有挠元, 不能直接在原环中做这一步除法.
]

=== 有理化后, 滤过分裂成权重

记 $K_Q:=K times.o_ZZ QQ$. Adams 运算自然延拓到 $K_Q$, $lambda$-运算则由前面的指数公式延拓. 这里 $F_gamma^n K_Q=F_gamma^n K times.o_ZZ QQ$: 展开 $gamma_(t) (x\/d)=gamma_(t) (x)^(1\/d)$, 每个系数仍是总权重相同的 $gamma$ 系数的有理线性组合. 有理化以后, 不同的 $k^n$ 可以分开, 滤过便能拆成直和.

#theorem(title: [有理权重分解])[
  假设 $K$ 满足本节的正结构与分裂原理, 且每个元素都有有限 $gamma$-维数. 对任意固定整数 $k>=2$, 令
  $ K_Q^((n)):= {x in K_Q | psi^k (x)=k^n x} $
  则这些子空间与 $k$ 的选择无关, 并且
  $ K_Q=plus.o.big_(n>=0) K_Q^((n)), quad K_Q^((a))K_Q^((b)) subset.eq K_Q^((a+b)) $
  $ K_Q^((n)) tilde.eq (F_gamma^n K\/F_gamma^(n+1) K) times.o_ZZ QQ $
  特别地, $K_Q^((0)) tilde.eq H times.o_ZZ QQ$, $K_Q^((1)) tilde.eq L times.o_ZZ QQ$.
] <thm-lambda-rational-weights>

#proof[
  *先把零秩元素放进有限的小环.* 任意有限多个零秩元素, 清掉分母后都能写成正元的差. 收集其中的正元 $p_j$, 再取它们的有限多个非零外幂 $lambda^i (p_j)$. 特殊性公理说明, 这些外幂生成的环对所有运算封闭. 它们减去各自的整数秩后都幂零, 所以有理化后生成有限维的 $QQ$-代数 $A$: 每个生成元的幂只需取到某个有限次数. 此时 $A$ 的秩取值于 $QQ$, 增广理想也是幂零的.

  $A$ 中的元素仍有有限 $gamma$-维数. 只需检查除以整数这一步: 对零秩 $x$, 在 $gamma_(t) (x\/d)=gamma_(t) (x)^(1\/d)$ 的二项式展开中, $gamma_(t) (x)-1$ 的系数生成幂零理想, 所以只有有限项. 由 @prop-gamma-finite-filtration 的有理版本, $A$ 的 $gamma$-滤过有限.

  *有限滤过可以逐层分开.* 设 $F_gamma^(N+1) A=0$, 令 $T=psi^k$. 由上一命题, $T-k^n$ 把第 $n$ 层送入下一层. 所以
  $ product_(n=0)^N (T-k^n)=0 $
  当 $k>=2$ 时, $1,k,dots,k^N$ 两两不同. 因而插值多项式
  $ e_(n) (T):=product_(0<=j<=N, j!=n) frac(T-k^j,k^n-k^j) $
  给出互相正交, 和为恒等的投影, 将 $A$ 拆成 $T$ 的特征子空间. 第 $n$ 个子空间自然映到 $F_gamma^n A\/F_gamma^(n+1) A$, 且是同构.

  不同特征值的有限分解是唯一的, 所以这些小环给出的分解相容, 拼起来便得到 $I times.o_ZZ QQ$ 的正权重分解. $H times.o_ZZ QQ$ 上的 Adams 运算是恒等, 它就是零权重部分. 乘法保持权重相加, 来自 $psi^k$ 是环同态.

  *再认出滤过.* 小环中的第 $m$ 个权重落在 $F_gamma^m A$, 所以全环中所有权重至少为 $n$ 的元素都落在 $F_gamma^n K_Q$. 反过来, 对任意零秩 $x$, 在包含它的小环中计算可知 $gamma^i (x)$ 只含权重至少为 $i$ 的项. 滤过生成元的总权重至少为 $n$, 而乘上环中任意元素都不会降低权重. 因而
  $ F_gamma^n K_Q=plus.o.big_(m>=n) K_Q^((m)) $
  取相邻两层的商, 就得到所述分次同构.

  *最后检查它与 $k$ 无关.* 所有 $psi^m$ 与 $T$ 交换, 因而保持 $T$ 的特征子空间. 它在第 $n$ 个分次层上乘 $m^n$, 而该层与第 $n$ 个特征子空间同构, 所以在这个子空间上也乘 $m^n$. 因此权重不依赖 $k$. 零次与一次的描述由 @thm-gamma-first-quotient 得到.
]

这里必须取 $k>=2$: $psi^1=id$ 的所有特征值都相同, 无法用它区分权重. 每个元素只含有限多个权重, 但整个环未必只有有限多个非零权重.

=== 从 $gamma$-运算到 Chern 类

把上同调的例子抽象出来. 设 $A=plus.o.big_(n>=0) A^n$ 是交换分次环, 并固定 $H->A^0$. 复丛的例子取 $A^n=H^(2n) (X;ZZ)$; 实丛取 $A^n=H^n (X;ZZ\/2ZZ)$.

#definition(title: [Chern 类系统])[
  一组映射 $c_n:K->A^n$ 称为 Chern 类系统, 若 $c_(0) (x)=1$, 并满足:

  + 对 $h in H$ 和 $n>=1$, 有 $c_(n) (h)=0$.
  + 对秩 $r$ 的正元 $p$, 有 $c_(n) (p)=0$ 当 $n>r$.
  + 总类 $c_(t) (x):=sum_(n>=0)c_(n) (x)t^n$ 满足 $c_(t) (x+y)=c_(t) (x)c_(t) (y)$.
  + 对线元, $c_(1) (ell m)=c_(1) (ell)+c_(1) (m)$.

  当 $H!=ZZ$ 时, 还要求与系数相容: $c_(t) (h x)=c_(t) (x)^h$. 右边用二项式展开, 系数 $binom(h,j)$ 通过 $H->A^0$ 解释; $H=ZZ$ 时这已包含在直和公式中.
]

条件中是 $n>r$, 所以最高次 $c_(r) (p)$ 可以非零. #link(<sec-topological-characteristic-classes>)[前面定义的 Chern 类与 Stiefel--Whitney 类]都满足这些条件.

#proposition(title: [$gamma$-滤过给出的 Chern 类])[
  在 $A=op("gr")_gamma K$ 中定义
  $ c_n^gamma (x):=gamma^n (x-epsilon(x)) mod F_gamma^(n+1) K $
  就得到一组 Chern 类.
]

#proof[
  减去秩后, 第 $n$ 个 $gamma$ 系数落在 $F_gamma^n$. $gamma_t$ 的乘法公式给出 Whitney 公式, @lem-gamma-finite-degree 给出维数条件. 对线元, 归一公式就是
  $ ell m-1 equiv (ell-1)+(m-1) mod F_gamma^2 K $
  而 $h-epsilon(h)=0$, 所以正次类在 $H$ 上为零. 与 $H$ 系数相容, 则来自 $gamma_(t) (h x)=gamma_(t) (x)^h$.
]

计算 Chern 类时, 使用同时适用于 $K$ 与 $A$ 的分裂原理: 在保持单射的扩张中, 把正元写成 $p=ell_1+dots+ell_r$, 并延拓这些类. 抽象版本参见 @Wei13[II, 第 4.11.2 段后的 Chern Splitting Principle]. 对复丛可用旗丛实现, 单射性来自射影丛公式. 对实丛的 Stiefel--Whitney 类, 实旗丛在模 $2$ 上同调上也给出单射, 足以计算这些类; 此处并不要求实 K 群的拉回也单射.

令 $a_i=c_(1) (ell_i)$, 称为 *Chern 根*. 线元只有一次类, 因而
$ c_(t) (p)=product_(i=1)^r (1+a_i t), quad c_(n) (p)=e_(n) (a_1,dots,a_r) $
任意关于根的对称多项式都能写回 $c_(i) (p)$, 因而回到原来的 $A$. 这里的根属于扩张后的上同调环, 不必属于 $A$ 本身.

#proposition(title: [Adams 运算放大 Chern 根])[
  对 $k>=1$, 有
  $ c_(n) (psi^k (x))=k^n c_(n) (x) $
]

#proof[
  分裂以后, $psi^k$ 把 $ell_i$ 换成 $ell_i^k$, 而
  $ c_(1) (ell_i^k)=k c_(1) (ell_i)=k a_i $
  第 $n$ 个初等对称多项式齐次为 $n$ 次, 所以所有根乘 $k$, 结果就乘 $k^n$. 对形式差, 对应的总类是两个乘积的商, 换元 $t|->k t$ 后仍得到同一个结论. 单射性将等式带回 $A$.
]

=== Chern 特征与加性的上同调类

Chern 类把直和变成总类的乘法. 若想把直和变成加法, 再次改用根的幂和即可. 以下令 $A$ 为 $QQ$-代数, 并记 $hat(A)=product_(n>=0) A^n$.

#definition(title: [Chern 特征])[
  对 Chern 根为 $a_1,dots,a_r$ 的正元 $p$, 定义
  $ op("ch")(p):=sum_(i=1)^r exp(a_i), quad op("ch")_(n) (p):=frac(1,n!)sum_(i=1)^r a_i^n $
  每一项都是对称多项式, 因而取值于 $A^n$. 以加性延拓到形式差, 并在 $H$ 上取给定的 $H->A^0$, 得到 *Chern 特征* $op("ch"):K->hat(A)$.
] <def-chern-character>

用 Newton 恒等式写回 Chern 类, 前几项为
$ op("ch")(x)=epsilon(x)+c_(1) (x)+frac(c_(1) (x)^2-2c_(2) (x),2)+frac(c_(1) (x)^3-3c_(1) (x)c_(2) (x)+3c_(3) (x),6)+dots $
这里 $epsilon(x)$ 通过 $H->A^0$ 看成零次项. 分母来自指数级数, 这就是有理系数自然出现的原因.

#proposition(title: [Chern 特征是环同态])[
  $op("ch"):K->hat(A)$ 是环同态, 且
  $ op("ch")_(n) (psi^k (x))=k^n op("ch")_(n) (x) $
] <prop-chern-character-ring-map>

#proof[
  直和把两组根放在一起, 所以 $op("ch")(p+q)=op("ch")(p)+op("ch")(q)$. 这也保证它能良好地延拓到群化.

  若 $p,q$ 的根为 $a_i,b_j$, 则张量积的根是 $a_i+b_j$, 因为线元满足 $c_(1) (ell_i m_j)=a_i+b_j$. 因而
  $ op("ch")(p q)=sum_(i,j) exp(a_i+b_j)=(sum_i exp(a_i))(sum_j exp(b_j)) $
  所以它保持乘法; 秩 $1$ 的平凡对象给出单位 $1$. 对形式差再用加性, 涉及 $H$ 中的系数则用系数相容条件即可. 最后的公式来自 Adams 运算把每个根乘 $k$.
]

#corollary(title: [Chern 特征与权重])[
  在 @thm-lambda-rational-weights 的假设下, $op("ch")$ 的值实际落在直和 $A$, 且
  $ op("ch")_(n) (K_Q^((m)))=0 quad (n!=m) $
  因而 $op("ch"):K_Q->A$ 是关于权重的分次环同态.
]

#proof[
  若 $x$ 的权重为 $m$, 取 $k>=2$. 一方面由加性有 $op("ch")_(n) (psi^k x)=k^m op("ch")_(n) (x)$, 另一方面上一命题给出 $k^n op("ch")_(n) (x)$. 当 $m!=n$, 两者之差是非零有理数, 所以这一项为零. 每个 $x$ 只有有限多个权重, 因而只有有限多个非零的 Chern 特征分量.
]

这里使用了 $op("ch")_n$ 的加性. 高次的单个 $c_n$ 一般不加性, 不能对它照搬这个特征值论证.

对于上面的 $c_n^gamma$, Chern 特征给出的同构正是
$ K_Q ->^~ (op("gr")_gamma K) times.o_ZZ QQ $
也就是有理权重分解. 对 $n>=1$, 可以在第 $n$ 层直接检查: @prop-adams-on-gamma-graded 与 $gamma^n (x)=lambda^n (x+n-1)$ 给出
$ c_n^gamma (x)=(-1)^(n-1) (n-1)![x] quad (x in F_gamma^n K) $
其中系数由第 $n-1$ 阶有限差分求得. 此时低于 $n$ 次的 Chern 类为零, Newton 恒等式给出 $op("ch")_(n) (x)=(-1)^(n-1)c_n^gamma (x)\/(n-1)!=[x]$. 零次则就是秩. 因此这个映射在每个权重上都是前面得到的典范同构.

=== 有理 K 理论与上同调

#theorem(title: [有理 Chern 特征同构])[
  对有限 CW 复形 $X$, Chern 特征给出自然同构
  $ K U^0 (X) times.o_ZZ QQ ->^~ plus.o.big_(i>=0) H^(2i) (X;QQ) $
  这是交换环同构. 通过悬挂延拓到奇次后, 还有
  $ K U^1 (X) times.o_ZZ QQ ->^~ plus.o.big_(i>=0) H^(2i+1) (X;QQ) $
] <thm-topological-rational-chern-character>

#proof[
  先看球面. 在 $S^2$ 上, Bott 类 $beta=[L]-1$ 满足
  $ op("ch")(beta)=exp(c_(1) (L))-1=c_(1) (L) $
  因为 $S^2$ 没有更高次的非零上同调. 这是 $H^2 (S^2;ZZ)$ 的一个生成元. 在 $S^(2m)$ 上, Bott 周期性把生成元写成 $m$ 个 Bott 类的外积; Chern 特征保持外积, 所以它仍送到最高次上同调的生成元. 奇数维球面的约化 $K U^0$ 为零. 再用悬挂定义奇次 Chern 特征, 就得到所有球面上的有理同构.

  对 CW 对 $(X,A)$, 用商空间定义相对 Chern 特征. 悬挂构造保证它与连接映射相容, 所以得到 K 理论与有理上同调长正合列之间的映射. 现在按胞腔数归纳: 商空间是有限个球面的楔和, 相对项上已有同构; 对已构造的子复形也有同构. 五引理便给出 $X$ 上的同构. 零维情形就是逐点的秩计算.

  乘法相容性已由 @prop-chern-character-ring-map 证明. 参见 @Hat17VB[命题 4.5] 与 @Wei13[II, 定理 4.13].
]

对一般紧 Hausdorff 空间, 对应的结论使用 Čech 上同调:
$ K U(X) times.o_ZZ QQ tilde.eq plus.o.big_(i>=0) std.math.accent(H, "̌")^(2i) (X;QQ) $
证明可从有限多面体逼近得到. 将 $X$ 写成有限多面体的逆极限后, 分类映射及其同伦可下降到某个阶段: 先在有限维 Grassmann 流形中作逼近, 再用邻域收缩把近似映射送回流形. 因而 K 类在这些阶段上取直极限; Čech 上同调也按同样的直极限计算. 对各阶段使用上一定理, 再取直极限即可. 这正是紧空间情形要用 Čech 上同调的地方.

#example(title: [球面上的 Adams 运算与阶乘])[
  取 $b_m in tilde(K U)(S^(2m)) tilde.eq ZZ$ 为 Bott 生成元, 记 $u_m=op("ch")_(m) (b_m)$ 为最高次上同调生成元. 则
  $ psi^k (b_m)=k^m b_m $
  因为 Chern 特征把左边送到 $k^m u_m$, 而球面上的约化 K 群无挠.

  球面上低于 $2m$ 的正次上同调都为零, 因而 Newton 公式还给出
  $ c_(m) (b_m)=(-1)^(m-1) (m-1)!u_m $
  所以高维球面上的最高 Chern 类一般不是整系数同构; Chern 特征中的阶乘恰好补偿了这个倍数.
]

到这里, 外幂, Adams 运算与 Chern 特征有了共同的解释: 外幂取线元的初等对称多项式, Adams 运算取线元的幂和, Chern 特征则取 Chern 根的指数和. $gamma$-滤过把这些信息分层, 有理化以后各层由 Adams 特征值分开.

== 小结

本章反复使用的办法是: 先用平凡补项把虚拟对象写成 $[P]-[R^n]$ 或 $[E]-[epsilon^n]$, 再拆出秩. 剩下的约化类, 记录补上自由项或平凡项之后仍存在的差别.

#table(
  columns: (1.1fr, 3fr),
  table.header([工具], [主要用法]),
  [平凡补项与稳定化], [将 K 群中的相等换成稳定同构; 满足 Bass 消去的条件时, 进一步得到原来的模同构.],
  [幂等矩阵], [把投射模写成有限矩阵数据. 系数与等式可以下降到滤过系统的某一阶段; 提升幂等矩阵则处理幂零商与完备情形.],
  [秩与行列式], [秩先拆出 $H_0$; 行列式再把约化部分送到线模或线丛的类群, 提取第一层信息.],
  [Serre--Swan 与分类空间], [紧 Hausdorff 空间上的丛可换成连续截面模; 丛的分类也可换成到 $B U(n),B O(n)$ 的同伦类.],
  [Bott 周期性与长正合列], [先算球面, 再沿胞腔附着计算有限 CW 复形的 K 群; 不同次数由周期性联系.],
  [外幂与分裂原理], [用 $lambda_(t) (x-y)=lambda_(t) (x)\/lambda_(t) (y)$ 处理虚拟对象; 在单射扩张中分裂成线元后, 用对称多项式证明运算公式.],
  [$gamma$-滤过与 Adams 运算], [按层研究零秩部分. 在前述条件下, $psi^k$ 在第 $n$ 层上乘 $k^n$; 有理化后据此分离权重.],
  [特征类与 Chern 特征], [特征类检测丛的非平凡性; Chern 特征保持加法与乘法, 将有理复 K 理论转成上同调计算.],
)

*代数上*, 先用幂零不变性和有限乘积分解化简环, 再计算秩与约化部分. 零维环的 $K_0$ 完全由局部常值秩函数决定; Dedekind 整环的约化部分则由理想类群给出. 一般情形可以继续用行列式与 $gamma$-滤过逐层研究.

*拓扑上*, 对有限 CW 复形, 可以用 Bott 周期性与胞腔长正合列作整系数计算. 若只关心有理信息, @thm-topological-rational-chern-character 将 $K U^0$, $K U^1$ 分别换成偶次, 奇次有理上同调. 有理化会丢掉挠元, 所以 Möbius 丛给出的二阶类, 仍需用整系数 K 理论或 $w_1$ 检测.
