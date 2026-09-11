#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= $K_1$ 群 / The Group $K_1$ <chap-k1>

在#chapter-ref(<chap-k0>)中, $K_0$ 记录投射模在直和下的加法关系. 现在进一步保留投射模的自同构. 从自由模上的可逆矩阵出发, 先允许补上恒等矩阵, 再将复合写成加法, 就得到 $K_1$.

本章先用初等变换计算 $K_1$, 再改用投射模的语言说明 Morita 不变性与转移. 最后讨论取商和局部化时的正合列, 并由 Laurent 多项式环引出 $K_(-1)$. 主要参考 @Wei13[III, §1--§4].

== $K_1$ 的定义与初等变换

=== 无穷一般线性群

设 $R$ 是含幺结合环, 不要求交换. 记 $GL_n (R)$ 为 $R$ 上所有 $n times n$ 可逆矩阵组成的群, 群运算是矩阵乘法.

#definition(title: [无穷一般线性群])[
  将可逆矩阵补大一阶, 得到单射群同态
  $ GL_n (R) arrow.r.hook GL_(n+1) (R), quad g mapsto mat(g,0;0,1) $
  于是可以将这些群依次看作子群:
  $ GL_1 (R) subset.eq GL_2 (R) subset.eq dots subset.eq GL_n (R) subset.eq GL_(n+1) (R) subset.eq dots $
  定义*无穷一般线性群* (infinite general linear group)
  $ GL(R):=varinjlim(n>=1) GL_n (R)=union.big_(n>=1) GL_n (R) $
] <def-infinite-general-linear-group>

这个群的每个元素仍由有限阶矩阵表示. 比较或相乘两个元素时, 先在右下角补单位矩阵, 将它们放进同一个 $GL_N (R)$ 即可. 补单位矩阵的操作称为*稳定化*.

接下来通过 Abel 化, 把矩阵乘法变成交换的群运算.

#definition(title: [交换子子群])[
  对群 $G$ 中的 $g,h$, 定义它们的*交换子*
  $ [g,h]:=g h g^(-1) h^(-1) $
  由所有交换子生成的子群称为*交换子子群*, 记为
  $ [G,G]:=⟨ [g,h] | g,h in G ⟩ $
] <def-commutator-subgroup>

#proposition(title: [Abel 化的泛性质])[
  $[G,G]$ 是 $G$ 的正规子群, 商群
  $ G^"ab":=G slash [G,G] $
  是 Abel 群, 称为 $G$ 的*Abel 化*. 记商映射为 $q:G->G^"ab"$. 对任意 Abel 群 $A$ 和群同态 $phi:G->A$, 存在唯一的群同态 $overline(phi):G^"ab"->A$, 使
  $ phi=overline(phi) compose q $
] <prop-group-abelianization>

#proof[
  对任意 $x in G$, 有
  $ x[g,h]x^(-1)=[x g x^(-1),x h x^(-1)] $
  所以共轭将生成元仍送到交换子, 故 $[G,G]$ 正规. 在商群里所有交换子都变成单位元, 因而任意两个元素交换.

  若 $A$ 是 Abel 群, 则 $phi([g,h])=1$, 所以 $[G,G] subset.eq ker(phi)$. 因而 $phi$ 通过商群分解; $q$ 满射保证分解唯一.
]

=== $K_1$ 的定义与函子性

#definition(title: [环的 Whitehead 群])[
  对含幺结合环 $R$, 定义
  $ K_1 (R):=GL(R)^"ab"=GL(R) slash [GL(R),GL(R)] $
  称为 $R$ 的*第一 $K$ 群*, 也称环的 *Whitehead 群*. 记典范商映射为
  $ q_R:GL(R)->K_1 (R), quad g mapsto [g] $
] <def-ring-k1>

由 @prop-group-abelianization, 每个从 $GL(R)$ 到 Abel 群 $A$ 的群同态, 都唯一地通过 $q_R$ 分解. 等价地, 有自然同构
$ Hom_(Ab) (K_1 (R),A) tilde.eq Hom_(Grp) (GL(R),A) $
这就是 $K_1$ 的泛性质. 定义见 @Wei13[III, 定义 1.1].

下面把 $K_1 (R)$ 写成加法群, 因而
$ [g h]=[g]+[h], quad [I_n]=0, quad [g^(-1)]=-[g] $
需要与单位群比较时, 也会使用乘法记号 $[g h]=[g][h]$. 两种写法表示同一个 Abel 群. 由于商映射满射, 每个 $K_1$ 类都能用一个有限阶可逆矩阵表示.

#proposition(title: [函子性])[
  含幺环同态 $phi:R->S$ 诱导群同态
  $ K_1 (phi):K_1 (R)->K_1 (S), quad [g] mapsto [phi(g)] $
  这里 $phi(g)$ 表示逐项施加 $phi$. 因而 $K_1$ 是函子
  $ K_1:Ring->Ab $
] <prop-k1-functoriality>

#proof[
  因为 $phi(g)phi(g^(-1))=I_n$, 逐项施加 $phi$ 将可逆矩阵送到可逆矩阵, 并保持乘法与稳定化, 所以给出 $GL(R)->GL(S)$. 群同态将交换子送到交换子, 因而通过商群给出 $K_1 (phi)$. 恒等态射与复合的相容性逐项检验即可.
]

#proposition(title: [分块直和对应加法])[
  对 $g in GL_m (R)$ 和 $h in GL_n (R)$, 有
  $ [mat(g,0;0,h)]=[g]+[h] in K_1 (R) $
] <prop-k1-block-sum>

#proof[
  分块矩阵满足
  $ mat(g,0;0,h)=mat(g,0;0,I_n) mat(I_m,0;0,h) $
  第一项的类是 $[g]$. 第二项与 $mat(h,0;0,I_m)$ 由置换矩阵共轭, 而 Abel 化中共轭不改变类, 所以它的类是 $[h]$.
]

=== 行列式与 $S K_1$

先在交换环上看一个熟悉的不变量. 本小节设 $R$ 交换, 记 $R^times$ 为单位群. 行列式满足
$ det(g h)=det(g)det(h), quad det(mat(g,0;0,1))=det(g) $
所以给出群同态 $det:GL(R)->R^times$. 它把每个交换子送到 $1$, 因而由泛性质诱导
$ det:K_1 (R)->R^times, quad [g] mapsto det(g) $

#definition(title: [特殊线性群与 $S K_1$])[
  定义*特殊线性群*
  $ SL_n (R):=ker (det:GL_n (R)->R^times), quad SL(R):=union.big_(n>=1) SL_n (R) $
  并定义
  $ S K_1 (R):=ker (det:K_1 (R)->R^times) $
] <def-sk1>

#proposition(title: [行列式给出的分裂])[
  行列式 $det:K_1 (R)->R^times$ 满射, 且有自然的群同态截面
  $ s:R^times->K_1 (R), quad u mapsto [(u)] $
  其中 $(u)$ 是一阶矩阵. 因而有自然的 Abel 群同构
  $ K_1 (R) tilde.eq R^times plus.o S K_1 (R) $
  此外,
  $ GL(R) tilde.eq SL(R) semidirect R^times, quad
    S K_1 (R) tilde.eq SL(R) slash [GL(R),GL(R)] $
] <prop-k1-determinant-splitting>

#proof[
  把单位看成一阶矩阵, 得到 $j:R^times->GL(R)$, 且 $det compose j=id$. 取 $s=q_R compose j$, 仍有 $det compose s=id$. 这同时说明行列式满射与截面存在.

  在加法记号下, 每个 $z in K_1 (R)$ 唯一分解为
  $ z=s(det z)+(z-s(det z)) $
  第二项的行列式为 $1$, 所以属于 $S K_1 (R)$. 因而同构及其逆分别是
  $ z mapsto (det z,z-s(det z)), quad (u,x) mapsto s(u)+x $

  在 $GL(R)$ 中, 每个 $g$ 也唯一分解为
  $ g=(g j(det g)^(-1))j(det g) $
  第一项属于 $SL(R)$. 这给出半直积, 其中 $u in R^times$ 对 $SL(R)$ 的作用是沿 $j(u)$ 共轭. 最后, $[GL(R),GL(R)] subset.eq SL(R)$, 而 $K_1$ 中行列式为 $1$ 的类正是 $SL(R)$ 的像, 所以得到 $S K_1$ 的商群描述.
]

$S K_1 (R)$ 记录行列式为 $1$ 的类. 它为零时, 行列式就完全确定 $K_1$ 类. 域是最基本的例子. 参见 @Wei13[III, 例 1.1.1].

=== 域上的计算

#proposition(title: [域的第一 $K$ 群])[
  对任意域 $F$, 行列式给出自然同构
  $ K_1 (F) tilde.eq F^times $
  等价地, $S K_1 (F)=0$.
] <prop-k1-field>

#proof[
  只需证明 $SL(F)=[GL(F),GL(F)]$. 右边包含于左边已经由行列式说明.

  记 $E_(i j)$ 为 $(i,j)$ 位置是 $1$, 其余位置是 $0$ 的矩阵单位. 对 $i!=j$, 矩阵
  $ e_(i j)(a):=I+a E_(i j) $
  称为*初等矩阵*. 它的逆是 $e_(i j)(-a)$; 左乘它就是将第 $j$ 行的 $a$ 倍加到第 $i$ 行. 取互异的 $i,j,k$, 直接相乘可得
  $ [e_(i k)(a),e_(k j)(1)]=e_(i j)(a) $
  在 $GL(F)$ 中总能补大矩阵找到第三个指标 $k$, 所以每个初等矩阵都是交换子.

  下面说明行列式为 $1$ 的矩阵由初等矩阵生成. 对 $g in SL_n (F)$ 作行消元: 若当前主元为零, 就加上一条该列非零的行; 主元非零后, 可用加行清掉该列的其他项. 逐列进行, 得到行列式仍为 $1$ 的对角矩阵.

  对 $u in F^times$, 直接计算
  $ w(u):=e_(1 2)(u)e_(2 1)(-u^(-1))e_(1 2)(u)=mat(0,u;-u^(-1),0) $
  $ w(u)w(-1)=mat(u,0;0,u^(-1)) $
  因而 $op("diag")(u,u^(-1))$ 是初等矩阵的乘积. 将这样的两阶块依次放在相邻的坐标上, 就能逐个消去对角矩阵的前 $n-1$ 个对角元; 最后一个由行列式为 $1$ 也必为 $1$.

  所以 $SL(F)$ 中每个元素都是初等矩阵的乘积, 也就是交换子的乘积. 这证明了另一方向的包含关系, 从而 $S K_1 (F)=0$. 再用 @prop-k1-determinant-splitting 即得结论.
]

例如对素数 $p$, 有 $K_1 (bb(F)_p) tilde.eq bb(F)_p^times$; 另有 $K_1 (RR) tilde.eq RR^times$. 这个计算见 @Wei13[III, 例 1.1.2]; 上面的证明使用初等矩阵与行消元.

=== 乘积环与矩阵环

计算复杂环之前, 先看 $K_1$ 怎样处理环的有限乘积与矩阵扩张.

#proposition(title: [保持有限乘积])[
  对含幺结合环 $R_1,R_2$, 两个投影诱导自然同构
  $ K_1 (R_1 times R_2) tilde.eq K_1 (R_1) plus.o K_1 (R_2) $
  因而 $K_1$ 保持有限乘积, 且 $K_1 (0)=0$.
] <prop-k1-finite-products>

#proof[
  乘积环上的矩阵就是两边矩阵组成的对, 可逆性也逐分量检验, 所以
  $ GL_n (R_1 times R_2) tilde.eq GL_n (R_1) times GL_n (R_2) $
  两个有限阶矩阵总能补到同一个阶数, 因而稳定化后得到
  $ GL(R_1 times R_2) tilde.eq GL(R_1) times GL(R_2) $
  对任意两个群 $G,H$, 交换子逐分量计算, 给出
  $ [G times H,G times H]=[G,G] times [H,H] $
  一边的包含由逐分量计算得到; 另一边则分别取形如 $(g,1)$ 与 $(1,h)$ 的元素作交换子. 因而对上面的群同构作 Abel 化即可. 有限个因子用归纳, 零环上的一般线性群是平凡群.
]

再把环换成它的矩阵环. 分块矩阵展开后仍是原环上的矩阵, 因而稳定化会得到同一个群.

#proposition(title: [矩阵环不改变 $K_1$])[
  对含幺结合环 $R$ 和整数 $r>=1$, 有自然同构
  $ K_1 (M_r (R)) tilde.eq K_1 (R) $
] <prop-k1-matrix-invariance>

#proof[
  将分块矩阵展开, 得到环同构 $M_m (M_r (R)) tilde.eq M_(m r) (R)$, 因而有群同构
  $ GL_m (M_r (R)) tilde.eq GL_(m r) (R) $
  左边的稳定化补上一个单位元 $I_r$, 展开后正是右边补上 $r$ 阶单位矩阵. 所以这些同构与稳定化相容, 给出
  $ GL(M_r (R)) tilde.eq varinjlim(m>=1) GL_(m r) (R) tilde.eq GL(R) $
  最后一步因为每个有限阶矩阵都能补到某个 $r$ 的倍数阶; 两个这样的矩阵若稳定后相等, 也能在某个倍数阶检验. 两边作 Abel 化即可.
]

这是 Morita 不变性的一个特例, 见 @Wei13[III, 例 1.1.4]. 结合域上的计算, 对域 $F$ 有
$ K_1 (M_r (F)) tilde.eq F^times $
具体地, 将 $GL_m (M_r (F))$ 中的矩阵展开成 $m r$ 阶矩阵, 再取行列式.

还要区分这个同构与标量包含诱导的映射. 环同态 $R->M_r (R)$, $a mapsto a I_r$ 在 $K_1$ 上诱导的映射, 经上述同构识别后是乘以 $r$. 因为 $g=(g_(i j))$ 被送到分块矩阵 $(g_(i j) I_r)$, 重新排列坐标后就是 $r$ 份 $g$ 的分块直和, 由 @prop-k1-block-sum, 其类为 $r[g]$.

=== 初等矩阵群

现在回到任意含幺结合环 $R$. 域上的证明已经用到初等矩阵. 将它们生成的群单独记下, 就能把 $K_1$ 的 Abel 化定义改写成初等变换的语言.

#definition(title: [初等矩阵群])[
  对 $1<=i!=j<=n$ 和 $a in R$, 定义*初等矩阵*
  $ e_(i j)(a):=I_n+a E_(i j) $
  其中 $E_(i j)$ 是矩阵单位. 定义
  $ E_n (R):=⟨ e_(i j)(a) | 1<=i!=j<=n, a in R ⟩ subset.eq GL_n (R) $
  为这些初等矩阵生成的子群, 并约定 $E_1 (R)={1}$. 稳定化与初等矩阵相容, 因而可以定义
  $ E(R):=varinjlim(n>=1) E_n (R)=union.big_(n>=1) E_n (R) subset.eq GL(R) $
] <def-elementary-matrix-groups>

左乘 $e_(i j)(a)$, 就是将第 $j$ 行左乘 $a$ 后加到第 $i$ 行; 右乘它, 则是将第 $i$ 列右乘 $a$ 后加到第 $j$ 列. 非交换环上要保留这个左右次序. 因而 $E_n (R)$ 恰好由能通过有限次加行操作化成单位矩阵的可逆矩阵组成.

#lemma(title: [初等矩阵的基本关系])[
  对 $a,b in R$, 有
  $ e_(i j)(a)e_(i j)(b)=e_(i j)(a+b), quad e_(i j)(a)^(-1)=e_(i j)(-a) $
  若 $j!=k$ 且 $i!=l$, 则
  $ [e_(i j)(a),e_(k l)(b)]=1 $
  若 $i,j,k$ 两两不同, 则
  $ [e_(i j)(a),e_(j k)(b)]=e_(i k)(a b) $
] <lem-elementary-matrix-relations>

#proof[
  使用 $(a E_(i j))(b E_(k l))=delta_(j k) a b E_(i l)$ 展开即可. 例如在最后一种情形, 记 $A=a E_(i j)$, $B=b E_(j k)$, 则 $A^2=B^2=B A=0$, 且
  $ (I+A)(I+B)(I-A)(I-B)=I+A B=I+a b E_(i k) $
]

#definition(title: [完美群])[
  称群 $G$ 为*完美群* (perfect group), 若 $G=[G,G]$, 等价地, $G^"ab"$ 是平凡群.
] <def-perfect-group>

#lemma(title: [初等矩阵群是完美群])[
  若 $n>=3$, 则 $E_n (R)$ 是完美群. 稳定初等矩阵群 $E(R)$ 也是完美群.
] <lem-elementary-group-perfect>

#proof[
  对每个生成元 $e_(i j)(a)$, 选取与 $i,j$ 不同的 $k$. 上一引理给出
  $ e_(i j)(a)=[e_(i k)(a),e_(k j)(1)] $
  右边的两个矩阵都在 $E_n (R)$ 中, 所以每个生成元都属于 $[E_n (R),E_n (R)]$. 这就证明了第一句. 在稳定群中总能找到第三个指标, 同样的论证证明第二句.
]

第三个指标是这里的关键. 例如 $E_2 (bb(F)_2)=SL_2 (bb(F)_2) tilde.eq frak(S)_3$, 并不是完美群. 这里用到前面域上的行消元, 以及该群对三个非零向量的置换作用.

=== Whitehead 引理

先证明一个分块恒等式, 它能让稳定化后的共轭留在初等矩阵群里.

#lemma(title: [一对互逆矩阵的初等分解])[
  对任意 $g in GL_n (R)$, 有
  $ mat(g,0;0,g^(-1)) in E_(2 n) (R) $
] <lem-elementary-inverse-blocks>

#proof[
  对 $n times n$ 矩阵 $A$, 记
  $ U(A):=mat(I_n,A;0,I_n), quad L(A):=mat(I_n,0;A,I_n) $
  它们都在 $E_(2 n) (R)$ 中: 分别将 $A$ 的各个矩阵元放进右上块或左下块的初等矩阵, 再相乘即可. 直接相乘得到
  $ w(g):=U(g)L(-g^(-1))U(g)=mat(0,g;-g^(-1),0) $
  $ w(g)w(-I_n)=mat(g,0;0,g^(-1)) $
  所以右边是初等矩阵的乘积.
]

#theorem(title: [Whitehead 引理])[
  对任意含幺结合环 $R$, 有
  $ E(R)=[GL(R),GL(R)] $
  特别地, $E(R)$ 是 $GL(R)$ 的正规子群, 且
  $ K_1 (R) tilde.eq GL(R) slash E(R) $
] <thm-whitehead-lemma>

#proof[
  *先证正规性.* 取 $g in GL(R)$ 和 $e in E(R)$, 补到同一个 $n$ 阶. 由上一引理,
  $ d:=mat(g,0;0,g^(-1)) in E_(2 n) (R) $
  因而
  $ mat(g e g^(-1),0;0,I_n)=d mat(e,0;0,I_n)d^(-1) in E(R) $
  这说明 $g e g^(-1) in E(R)$, 所以商群 $Q:=GL(R) slash E(R)$ 有定义.

  *再证商群交换.* 对 $g,h in GL_n (R)$, 记
  $ g_1:=mat(g,0;0,I_n), quad h_1:=mat(h,0;0,I_n), quad h_2:=mat(I_n,0;0,h) $
  上一引理说明 $h_1 h_2^(-1)=op("diag")(h,h^(-1)) in E(R)$, 因而 $h_1,h_2$ 在 $Q$ 中相等. 但 $g_1$ 与 $h_2$ 在矩阵群里就交换, 所以 $g,h$ 的像在 $Q$ 中交换. 因此
  $ [GL(R),GL(R)] subset.eq E(R) $

  反过来, @lem-elementary-group-perfect 的证明已经把每个初等矩阵写成了交换子, 所以 $E(R) subset.eq [GL(R),GL(R)]$. 两边相等, 最后再用 $K_1$ 的定义即可.
]

初等群的完美性与 Whitehead 引理分别见 @Wei13[III, 引理 1.3.2 与引理 1.3.5]. 因而 $g,h$ 表示同一个 $K_1$ 类, 当且仅当稳定化后能通过有限次加行操作从一个变成另一个. 对交换环, 也得到
$ S K_1 (R) tilde.eq SL(R) slash E(R) $

=== 单位群中的关系

半局部环上的矩阵可以消元到对角矩阵, 因而其 $K_1$ 类都能由单位表示. 为了识别单位之间的关系, 先定义下面的子群.

#definition(title: [子群 $W(R)$])[
  对含幺结合环 $R$, 定义
  $ W(R):=⟨ (1+a b)(1+b a)^(-1) | a,b in R, 1+a b in R^times ⟩ subset.eq R^times $
] <def-unit-whitehead-relations>

这个定义有意义, 因为 $1+a b$ 可逆时, $1+b a$ 也可逆, 且
$ (1+b a)^(-1)=1-b(1+a b)^(-1)a $
左右相乘检验即可.

#lemma(title: [单位关系在 $K_1$ 中消失])[
  $W(R)$ 是 $R^times$ 的正规子群, 且
  $ [R^times,R^times] subset.eq W(R) subset.eq ker (R^times->K_1 (R)) $
  因而 $R^times slash W(R)$ 是 Abel 群, 并有自然群同态
  $ R^times slash W(R)->K_1 (R) $
] <lem-unit-whitehead-relations>

#proof[
  沿单位 $u$ 共轭, 会把定义中的生成元送到由 $u a u^(-1),u b u^(-1)$ 给出的生成元, 所以 $W(R)$ 正规. 对单位 $u,v$, 在定义中取 $a=u$, $b=v-u^(-1)$, 就有
  $ (1+a b)(1+b a)^(-1)=u v(v u)^(-1)=[u,v] $
  所以它包含单位群的交换子子群.

  再设 $1+a b$ 可逆, 取矩阵 $M=mat(1,a;-b,1)$. 用初等矩阵从两种方向消元, 得到
  $ e_(1 2)(-a) M e_(2 1)(b)=mat(1+a b,0;0,1) $
  $ e_(2 1)(b) M e_(1 2)(-a)=mat(1,0;0,1+b a) $
  第一式也说明 $M$ 可逆. 由 Whitehead 引理, 初等矩阵在 $K_1$ 中的类为零, 因而
  $ [1+a b]=[M]=[1+b a] $
  所以每个生成元 $(1+a b)(1+b a)^(-1)$ 都映到零.
]

若 $R$ 交换, 每个这样的生成元都是 $1$, 所以 $W(R)={1}$. 非交换时, $W(R)$ 可能严格大于 $[R^times,R^times]$; 后面的半局部环公式需要保留 $W(R)$.

=== 半局部环的计算

#definition(title: [半局部环])[
  记 $J(R)$ 为 $R$ 的 *Jacobson 根*, 即所有极大右理想的交. 称含幺结合环 $R$ 为*半局部环* (semilocal ring), 若
  $ R slash J(R) tilde.eq product_(alpha=1)^s M_(d_alpha) (D_alpha) $
  其中因子只有有限个, 每个 $D_alpha$ 都是除环.
] <def-semilocal-ring>

交换环时, 这等价于只有有限多个极大理想: 用中国剩余定理, 商掉它们的交后就是有限个剩余域的乘积. 特别地, 交换局部环和有限交换环都是半局部环.

我们用到 Jacobson 根的两个基本性质: $1+j$ 对每个 $j in J(R)$ 都是单位; 一个元素在 $R slash J(R)$ 中可逆, 当且仅当它在 $R$ 中可逆. 后一句可以这样看: 若 $a,b$ 模根互逆, 则 $a b$ 与 $b a$ 都在 $1+J(R)$ 中, 从而 $a$ 同时有左逆与右逆, 两者必相等.

#lemma(title: [半局部环的单位主元])[
  设 $R$ 半局部. 若 $a R+b R=R$, 则存在 $t in R$, 使
  $ a+b t in R^times $
] <lem-semilocal-unit-pivot>

#proof[
  先模去 $J(R)$. 在有限乘积的每个因子上分别选择 $t$, 最后提升回 $R$ 即可. 因而只需考虑 $R=M_d (D)=End_D (V)$, 其中 $V$ 是有限维右 $D$-向量空间.

  条件 $a R+b R=R$ 说明 $Im(a)+Im(b)=V$. 取分解 $V=ker(a) plus.o U$. 于是 $a|_U:U->Im(a)$ 是同构, 且
  $ dim_D ker(a)=dim_D (V slash Im(a)) $
  映射 $b:V->V slash Im(a)$ 满射, 所以可以选取 $t$ 在 $ker(a)$ 上的值, 使 $b t$ 诱导同构 $ker(a)->V slash Im(a)$; 再令 $t|_U=0$.

  这样 $a+b t$ 在 $U$ 上同构地映到 $Im(a)$, 在 $ker(a)$ 上的像则补齐剩余商空间. 因而它是 $V$ 的自同构. 这证明了各矩阵环因子上的结论, 提升后再用单位的提升性质即可.
]

这就是半局部环的 Bass 稳定范围为 $1$ 的性质. 它让加行或加列操作产生一个可逆的主元.

#proposition(title: [每个 $K_1$ 类都来自单位])[
  若 $R$ 半局部, 则每个可逆矩阵都能通过初等行列操作化成对角元均可逆的对角矩阵. 因而自然映射
  $ R^times->K_1 (R), quad u mapsto [(u)] $
  满射.
] <prop-semilocal-units-surject-k1>

#proof[
  设 $g in GL_n (R)$ 的第一行为 $(a_1,dots,a_n)$. 由 $g$ 可逆, 可取 $x_1,dots,x_n$, 使 $sum_i a_i x_i=1$. 令
  $ b:=sum_(i=2)^n a_i x_i $
  则 $a_1 R+b R=R$. 由上一引理, 可取 $t$, 使
  $ u:=a_1+b t=a_1+sum_(i=2)^n a_i (x_i t) in R^times $
  分别将第 $i$ 列右乘 $x_i t$ 后加到第一列, 就让左上角变成单位 $u$.

  此时若第一列下方的元素为 $c_i$, 左乘 $e_(i 1)(-c_i u^(-1))$ 就能将它清零. 再用第一列清掉第一行其余元素, 得到
  $ mat(u,0;0,g'), quad g' in GL_(n-1) (R) $
  对 $g'$ 归纳, 最后得到 $op("diag")(u_1,dots,u_n)$, 每个 $u_i$ 都是单位. $n=1$ 时无需消元.

  由 Whitehead 引理, 初等行列操作不改变 $K_1$ 类. 再用 @prop-k1-block-sum,
  $ [g]=sum_(i=1)^n [(u_i)]=[(u_1 dots u_n)] $
  所以每个类都能由一个单位表示.
]

现在只剩下识别 $R^times->K_1 (R)$ 的核. 非交换情形使用下面的广义行列式.

#lemma(title: [半局部环的广义行列式])[
  若 $R$ 半局部, 记 $C:=R^times slash W(R)$. 对每个 $n>=1$, 存在群同态
  $ Delta_n:GL_n (R)->C $
  满足
  $ Delta_n (e_(i j)(a))=1, quad
    Delta_n (op("diag")(u,1,dots,1))=overline(u) $
  且与稳定化相容. 这里 $overline(u)$ 表示单位 $u$ 在 $C$ 中的类. 这些性质唯一确定 $Delta_n$.
] <lem-semilocal-generalized-determinant>

存在性引用 Vaserstein 的非交换行列式定理, 见 @Vas69[定理 3.6 及第 6 节] 与 @Wei13[III, 习题 1.2]. 它保证消元所得的单位乘积在 $C$ 中与选择无关, 并且与矩阵乘法相容. 唯一性由消元分解得到: 初等矩阵的值为 $1$, 对角矩阵的值是各对角元的类之积.

可以用一个两阶计算理解为什么需要 $W(R)$. 若 $a$ 是单位, 且 $g=mat(a,b;c,d)$ 可逆, 则初等消元给出
$ Delta_2 (g)=overline(a) dot overline(d-c a^(-1)b) $
若 $d$ 也可逆, 从另一个方向消元则得到 $overline(d) dot overline(a-b d^(-1)c)$. 这两个值相等, 因为 $C$ 交换, 并且 $W(R)$ 的关系给出
$ overline(1-d^(-1)c a^(-1)b)=overline(1-a^(-1)b d^(-1)c) $
这里正是将 $x=d^(-1)c$, $y=-a^(-1)b$ 代入 $overline(1+x y)=overline(1+y x)$. 这些等式解释了局部的换主元关系; 广义行列式定理保证它们在整个消元过程中相容.

#theorem(title: [半局部环的第一 $K$ 群])[
  若 $R$ 是含幺半局部环, 则自然包含 $R^times=GL_1 (R)->GL(R)$ 诱导同构
  $ R^times slash W(R) tilde.eq K_1 (R) $
] <thm-semilocal-k1>

#proof[
  由 @lem-unit-whitehead-relations 和 @prop-semilocal-units-surject-k1, 已有满射
  $ q:C:=R^times slash W(R)->K_1 (R) $
  广义行列式与稳定化相容, 所以给出 $Delta:GL(R)->C$. 它在每个初等矩阵上取值为 $1$, 因而由 Whitehead 引理通过商群分解为
  $ overline(Delta):K_1 (R)->C $
  对每个 $u in R^times$, 有
  $ overline(Delta)(q(overline(u)))=Delta_1 ((u))=overline(u) $
  因而 $overline(Delta) compose q=id_C$, 所以 $q$ 也单射. 这就证明了同构, 同时说明 $ker (R^times->K_1 (R))=W(R)$.
]

#corollary(title: [交换半局部环的行列式])[
  若 $R$ 是交换半局部环, 则
  $ S K_1 (R)=0, quad det:K_1 (R) stretch(->)^~ R^times $
] <cor-commutative-semilocal-k1>

#proof[
  此时 $W(R)={1}$, 由上一定理即可. 也可以直接使用普通行列式: 单位映射 $s:R^times->K_1 (R)$ 由 @prop-semilocal-units-surject-k1 满射, 而 $det compose s=id$ 保证它单射. 所以它与行列式互逆, 行列式的核 $S K_1 (R)$ 为零. 这个直接证明只用上述消元和普通行列式.
]

这就是 @Wei13[III, 引理 1.4]. 例如对 $n>=2$, 有
$ K_1 (ZZ slash n ZZ) tilde.eq (ZZ slash n ZZ)^times $

非交换情形可看 $R=M_2 (bb(F)_2)$. 由矩阵环不变性, $K_1 (R) tilde.eq bb(F)_2^times$ 是平凡群, 因而 $W(R)=R^times$. 但 $R^times tilde.eq frak(S)_3$, 其 Abel 化有两个元素. 所以半局部环的单位群 Abel 化一般仍比 $K_1$ 大.

== 投射模与 Morita 不变性

矩阵是自由模自同构在一组基下的表示. 有限生成投射模能补成自由模, 所以它的自同构也给出稳定矩阵类. 沿这条思路可以证明, *$K_1 (R)$ 只依赖有限生成投射模组成的加性范畴*, 并由此得到 Morita 不变性与转移映射.

=== 投射模上的自同构

#definition(title: [有限生成投射模范畴])[
  记 $cat("Proj")(R)$ 为有限生成投射右 $R$-模与 $R$-线性映射组成的范畴. 这就是#chapter-ref(<chap-k0>)的 $cat("Proj")^"fg" (R)$, 本节省去上标. 由 @thm-finite-projective-characterizations, 一个右模 $P$ 属于其中, 当且仅当存在右模 $Q$ 和整数 $n>=0$, 使
  $ P plus.o Q tilde.eq R^n $
  此时 $Q$ 也有限生成投射. 零模与直和使 $cat("Proj")(R)$ 成为加性范畴. 记 $Aut_R (P)$ 为 $P$ 的 $R$-线性自同构群.
] <def-k1-projective-category>

这里采用右模, 因而对列向量左乘矩阵给出 $Aut_R (R^n)=GL_n (R)$. #chapter-ref(<chap-k0>)的 $Proj^"fg" (R)$ 只记录同构类, 本节的 $cat("Proj")(R)$ 同时保留模之间的映射.

#lemma(title: [投射模自同构的稳定类])[
  对 $P in cat("Proj")(R)$, 选择同构 $phi:P plus.o Q stretch(->)^~ R^n$, 其中 $n>=1$, 得到群同态
  $ iota_(Q,phi):Aut_R (P)->GL(R), quad
    alpha mapsto phi(alpha plus.o id_Q)phi^(-1) $
  任意两组选择所得的同态, 相差 $GL(R)$ 的一个内自同构. 因而
  $ ⟨P,alpha⟩:=[phi(alpha plus.o id_Q)phi^(-1)] in K_1 (R) $
  与 $Q,n,phi$ 的选择无关, 并给出典范群同态 $Aut_R (P)->K_1 (R)$.
] <lem-k1-projective-automorphism>

#proof[
  固定 $Q,n$ 时, 两个同构 $phi,phi':P plus.o Q stretch(->)^~ R^n$ 相差 $g=phi' phi^(-1) in GL_n (R)$, 所以对应的同态由同一个 $g$ 共轭.

  若另有 $P plus.o Q' tilde.eq R^m$, 就在
  $ (P plus.o Q) plus.o (P plus.o Q') tilde.eq R^(n+m) $
  上比较两个自同构: 一个让 $alpha$ 作用于第一个 $P$, 另一个让它作用于第二个 $P$, 其余直和项上都取恒等. 交换两个 $P$ 的同构将它们共轭起来. 再用置换矩阵交换两个自由直和项, 就将第二种自同构写成标准稳定化的形式. 所用的换位同构都与 $alpha$ 无关, 因而得到一个同时共轭这两个同态的矩阵.

  取 Abel 化后, 内自同构诱导恒等映射, 所以到 $K_1 (R)$ 的群同态与所有选择无关.
]

特别地, 恒等自同构代表零. 补直和项与模的同构也不改变类:
$ ⟨P,alpha⟩=⟨P plus.o Q,alpha plus.o id_Q⟩, quad
  ⟨P,alpha⟩=⟨P',u alpha u^(-1)⟩ $
第二个等式中 $u:P stretch(->)^~ P'$ 是任意同构.

#corollary(title: [$K_0$ 与 $K_1$ 的外积])[
  对任意含幺环 $R,S$, 存在自然的*外积* (external product)
  $ K_0 (R) times.o_ZZ K_1 (S)->K_1 (R times.o_ZZ S) $
  若 $P$ 是有限生成投射右 $R$-模, $g in GL_m (S)$, 则它由
  $ [P] times.o [g] mapsto ⟨P times.o_ZZ S^m,id_P times.o g⟩ $
  确定. 这里 $R,S$ 不要求交换, 此推论中省略下标的张量积均取在 $ZZ$ 上.
] <cor-k1-external-product>

#proof[
  先说明右边确实有定义. 令 $A=R times.o_ZZ S$, 右 $A$-模 $P times.o_ZZ S^m$ 的作用为
  $ (p times.o v)(r times.o s)=p r times.o v s $
  取 $P plus.o Q tilde.eq R^n$, 则
  $ (P times.o_ZZ S^m) plus.o (Q times.o_ZZ S^m) tilde.eq A^(n m) $
  所以 $P times.o_ZZ S^m$ 有限生成投射, $id_P times.o g$ 是其 $A$-线性自同构. 由 @lem-k1-projective-automorphism, 固定 $P$ 后得到群同态
  $ GL_m (S)->K_1 (A), quad g mapsto ⟨P times.o_ZZ S^m,id_P times.o g⟩ $
  将 $g$ 稳定化为 $op("diag")(g,1)$, 只是在张量积后补上 $P times.o_ZZ S$ 上的恒等自同构, 所以不改变其类. 因而这些同态给出 $GL(S)->K_1 (A)$; 目标是 Abel 群, 所以它唯一地通过 $K_1 (S)$ 分解.

  再看对 $P$ 的可加性. 张量积将 $P plus.o P'$ 变成两个张量积的直和. 自同构的直和可分解为两个分别只作用在一个直和项上的自同构, 所以其 $K_1$ 类是两者之和. 这一构造对 $P$ 的同构类可加, 对 $K_1 (S)$ 是群同态. 由 $K_0 (R)$ 的群化泛性质, 它延拓为 $K_0 (R) times K_1 (S)->K_1 (A)$ 的双线性映射, 再由 Abel 群张量积的泛性质得到所需同态.

  沿 $R,S$ 的环同态扩张标量, 与上述张量积及自同构相容, 所以外积对两个环都自然.
]

这就是 @Wei13[III, 推论 1.6.1]. 若 $R$ 交换, 再复合乘法环同态 $R times.o_ZZ R->R$ 诱导的 $K_1$ 映射, 就得到
$ K_0 (R) times.o_ZZ K_1 (R)->K_1 (R) $
这与后文 @prop-k0-action-k1 中的 $K_0 (R)$-模结构一致.

回顾群的一阶整数同调满足
$ H_1 (G;ZZ) tilde.eq G^"ab" $
这可以直接从 bar 复形的低次部分看出: 一维链群由符号 $[g]$ 自由生成, 一维边界为零, 二维边界给出关系 $[g h]=[g]+[h]$. 所得 Abel 群恰好是 $G$ 的 Abel 化. 所以下面只需把 $H_1 (Aut_R (P);ZZ)$ 理解为自同构群的 Abel 化.

=== 平移范畴与 Bass 公式

接下来将所有“补一个直和项”的操作放进同一个指标范畴.

#definition(title: [平移范畴])[
  定义 $t #h(0pt) cat("Proj")(R)$ 如下. 对象是有限生成投射右 $R$-模的同构类, 仍简记为 $P$. 从 $P$ 到 $P'$ 的态射是满足
  $ P plus.o Q tilde.eq P' $
  的有限生成投射模 $Q$ 的同构类. 恒等态射由零模给出; 若两个可复合态射的补项分别为 $Q,Q'$, 则复合的补项为 $Q plus.o Q'$.
] <def-k1-translation-category>

这里的态射只记录补项的同构类, 不记录所选的 $P plus.o Q tilde.eq P'$.

#lemma(title: [平移范畴是滤过的])[
  范畴 $t #h(0pt) cat("Proj")(R)$ 是小的滤过范畴.
] <lem-k1-translation-filtered>

#proof[
  有限生成投射模都来自有限阶幂等矩阵, 所以它们的同构类组成一个集合, 态射也组成集合.

  零模给出一个对象. 任意 $P,P'$ 都映向 $P plus.o P'$. 若从 $P$ 到 $P'$ 的两个平行态射分别由 $Q,Q'$ 给出, 则
  $ P plus.o Q tilde.eq P' tilde.eq P plus.o Q' $
  在它们之后接上补项为 $P$ 的态射 $P'->P' plus.o P$, 两个复合的补项分别为 $Q plus.o P$ 和 $Q' plus.o P$, 这两个模同构. 所以两个平行态射被等化, 满足滤过条件.
]

补项 $Q:P->P'$ 还诱导同态
$ H_1 (Aut_R (P);ZZ)->H_1 (Aut_R (P');ZZ) $
具体做法是选一个 $phi:P plus.o Q stretch(->)^~ P'$, 把 $alpha$ 送到 $phi(alpha plus.o id_Q)phi^(-1)$, 再取 Abel 化. 更换 $phi$ 或 $Q$ 的代表只会产生共轭, 所以这个同态与选择无关. 连续补两个直和项与一次补上它们的直和相容, 因而得到函子
$ t #h(0pt) cat("Proj")(R)->Ab, quad P mapsto H_1 (Aut_R (P);ZZ) $

#theorem(title: [Bass 公式])[
  有自然同构
  $ K_1 (R) tilde.eq varinjlim(P in t #h(0pt) cat("Proj")(R)) H_1 (Aut_R (P);ZZ) $
  从右边到左边的映射, 将 $alpha in Aut_R (P)$ 的类送到 $⟨P,alpha⟩$.
] <thm-k1-bass-colimit>

#proof[
  记右边的余极限为 $L_R$. 由 @lem-k1-projective-automorphism, 各个 $H_1 (Aut_R (P);ZZ)->K_1 (R)$ 与补直和项相容, 因而给出同态 $Phi:L_R->K_1 (R)$.

  Abel 化保持余极限. 具体说, 从 $varinjlim(n) GL_n (R)$ 到任意 Abel 群的同态, 恰好是一族与稳定化相容的 $GL_n (R)$ 到该群的同态. 因而
  $ K_1 (R) tilde.eq varinjlim(n>=1) H_1 (GL_n (R);ZZ) $
  将自由模 $R^n$ 看成平移范畴中的对象, 标准稳定化就是补上 $R$. 因此这些对象给出同态 $Psi:K_1 (R)->L_R$.

  在矩阵类上, $Phi compose Psi$ 显然是恒等. 反过来, 对来自 $Aut_R (P)$ 的类, 选择 $P plus.o Q tilde.eq R^n$. 复合 $Psi compose Phi$ 将它送到自由模上 $alpha plus.o id_Q$ 的类; 平移范畴中的态射 $P->R^n$ 已经把这两个类识别起来. 所以这个复合也是恒等.
]

Bass 公式说明, 用投射模的自同构来稳定化, 得到的仍是矩阵定义的 $K_1$. 关键是投射模能补成自由模, 即自由模的共尾性. 参见 @Wei13[III, 推论 1.6.3].

=== 加性函子与 Morita 不变性

#proposition(title: [加性函子诱导的映射])[
  任意加性函子 $T:cat("Proj")(S)->cat("Proj")(R)$ 诱导群同态
  $ K_1 (T):K_1 (S)->K_1 (R), quad
    ⟨P,alpha⟩ mapsto ⟨T(P),T(alpha)⟩ $
  这个构造保持恒等与复合, 自然同构的函子诱导相同的映射, 并且
  $ K_1 (T_1 plus.o T_2)=K_1 (T_1)+K_1 (T_2) $
] <prop-k1-additive-functor>

#proof[
  加性函子保持零对象与有限直和, 所以诱导平移范畴之间的函子. 同时, 它给出群同态 $Aut_S (P)->Aut_R (T(P))$, 且与补直和项相容. 取 Abel 化与余极限, 由 Bass 公式得到所需映射. 恒等与复合的相容性直接来自函子性. 自然同构的分量将对应的自同构共轭起来, 因而诱导相同的 $K_1$ 映射.

  对加性, 在 $T_1 (P) plus.o T_2 (P)$ 上有分解
  $ T_1 (alpha) plus.o T_2 (alpha)
    =(T_1 (alpha) plus.o id)(id plus.o T_2 (alpha)) $
  取 Abel 化后, 乘积成为和. 两个因子的类分别等于 $⟨T_1 (P),T_1 (alpha)⟩$ 与 $⟨T_2 (P),T_2 (alpha)⟩$, 因为补上恒等自同构不改变稳定类. 这就得到最后的等式.
]

#theorem(title: [$K_1$ 的 Morita 不变性])[
  加性范畴的等价 $cat("Proj")(R) tilde.eq cat("Proj")(S)$ 诱导同构
  $ K_1 (R) tilde.eq K_1 (S) $
  特别地, 若 $R,S$ Morita 等价, 即它们的普通右模范畴等价, 则它们的 $K_1$ 同构. 因而 $K_1 (R)$ 只依赖加性范畴 $cat("Proj")(R)$.
] <thm-k1-morita-invariance>

#proof[
  设 $T$ 是给定等价, $U$ 是其拟逆. 由上一个命题,
  $ K_1 (U)K_1 (T)=K_1 (U T)=id, quad
    K_1 (T)K_1 (U)=K_1 (T U)=id $
  因而 $K_1 (T)$ 是同构.

  普通模范畴的等价保持有限生成投射对象: 它们恰是那些 $Hom(P,-)$ 保持满射和滤过余极限的对象, 这些性质在范畴等价下不变. 模范畴的等价也保持由双积确定的加法, 所以限制为 $cat("Proj")(R) tilde.eq cat("Proj")(S)$ 的加性等价. 应用第一部分即可.
]

例如取 $S=M_r (R)$ 与矩阵单位 $e=E_(1 1)$. 标准 Morita 等价为
$ cat("Proj")(S)->cat("Proj")(R), quad Q mapsto Q e $
其拟逆把 $P$ 送到右 $S$-模 $P^(plus.o r)$, 右作用按行向量的矩阵乘法给出. 因为 $S^m e tilde.eq R^(r m)$, 自由 $S$-模的自同构在此等价下恰好变成展开分块后的矩阵. 所以它给出的 $K_1 (M_r (R)) tilde.eq K_1 (R)$ 就是 @prop-k1-matrix-invariance 中的同构. 参见 @Wei13[III, 命题 1.6.4 与引理 1.7].

=== 转移映射与 $K_0$ 的作用

限制标量给出转移映射. 要描述它与扩张标量的复合, 先写出前面外积在同一个交换环上的形式, 即 $K_0$ 对 $K_1$ 的作用.

#proposition(title: [$K_0$ 对 $K_1$ 的作用])[
  若 $R$ 交换, 则 $K_1 (R)$ 自然是 $K_0 (R)$-模. 对有限生成投射模 $P,Q$, 作用由
  $ [P] dot ⟨Q,alpha⟩:=⟨Q times.o_R P,alpha times.o id_P⟩ $
  确定, 再对 $[P]$ 作群化延拓.
] <prop-k0-action-k1>

#proof[
  对每个 $P$, 张量积给出加性自函子 $T_P:Q mapsto Q times.o_R P$, 因而给出 $K_1 (R)$ 的自同态. 由
  $ T_(P plus.o P') tilde.eq T_P plus.o T_(P') $
  与 @prop-k1-additive-functor, $P mapsto K_1 (T_P)$ 对直和可加, 所以通过 $K_0 (R)$ 的群化延拓. 张量积的结合律, 对称性与单位同构又给出
  $ T_P compose T_(P') tilde.eq T_(P times.o_R P'), quad T_R tilde.eq id $
  因而 $[P times.o_R P']$ 的作用是两个作用的复合, $[R]$ 的作用是恒等. 这正是模的公理.
]

#corollary(title: [转移映射])[
  设 $f:R->S$ 是含幺环同态, 且 $S$ 通过 $f$ 成为有限生成投射右 $R$-模. 忘却函子诱导*转移映射* (transfer)
  $ f_*:K_1 (S)->K_1 (R) $
  若进一步 $R$ 交换且 $f(R)$ 位于 $S$ 的中心, 则
  $ f_* compose f^*=[S] dot (-):K_1 (R)->K_1 (R) $
  其中 $f^*=K_1 (f)$, $[S] in K_0 (R)$. 特别地, 这适用于交换环之间的有限投射扩张.
] <cor-k1-transfer>

#proof[
  若 $P$ 是有限生成投射右 $S$-模, 它是某个 $S^m$ 的直和项. 忘却到 $R$ 后, $S^m$ 有限生成投射, 所以 $P$ 仍有限生成投射. 因而忘却给出加性函子
  $ f_*:cat("Proj")(S)->cat("Proj")(R) $
  由 @prop-k1-additive-functor 得到转移映射. 在自同构类上, 它把 $S$-线性自同构看成同一个模上的 $R$-线性自同构.

  另一方面, 扩张标量 $Q mapsto Q times.o_R S$ 总把有限生成投射 $R$-模送到有限生成投射 $S$-模. 对自由模的自同构, 它就是逐项施加 $f$, 因而诱导前面定义的 $f^*$. 在中心作用的假设下, 先扩张再忘却的复合正是 $R$-模上的张量函子
  $ Q mapsto Q times.o_R S $
  由 $K_0$ 作用的定义, 它诱导乘以 $[S]$ 的映射.
]

若 $S$ 作为 $R$-模自由且秩为 $d$, 则 $[S]=d[R]$, 上述复合就是 $x mapsto d x$. 一般有限投射情形应保留 $[S]$ 的整个 $K_0$ 类.

#example(title: [域的有限扩张与范数])[
  对域的有限扩张 $f:F->L$, 利用 $K_1 (L)=L^times$ 与 $K_1 (F)=F^times$, 转移映射就是经典范数
  $ f_*(u)=N_(L slash F) (u):=det_F (m_u:L->L), quad m_u (v)=u v $
  因为单位 $u$ 代表一维 $L$-空间上的乘法自同构, 忘却标量后, 它成为有限维 $F$-空间上的同一个自同构; 到 $K_1 (F)$ 的类由行列式给出. 若 $[L:F]=d$, 对 $u in F^times$ 就有 $N_(L slash F) (u)=u^d$, 与上面的乘以 $d$ 相符.
] <ex-k1-transfer-field-norm>

这里的转移映射与范数例子见 @Wei13[III, 推论 1.7.1].

=== Eilenberg 消去法

#definition(title: [Flasque 环])[
  若存在加性自函子 $T:cat("Proj")(R)->cat("Proj")(R)$ 以及自然同构
  $ id plus.o T tilde.eq T $
  则称 $R$ 为 *flasque 环*. 也就是说, 对每个有限生成投射模 $P$, 有随 $P$ 自然的同构 $P plus.o T(P) tilde.eq T(P)$.
] <def-flasque-ring-k1>

这个条件要求 $T(P)$ 仍是有限生成投射模. 普通模的可数直和通常不满足这个有限性要求.

#corollary(title: [Flasque 环的 $K_1$ 消失])[
  若 $R$ 是 flasque 环, 则 $K_1 (R)=0$.
] <cor-flasque-ring-k1>

#proof[
  自然同构 $id plus.o T tilde.eq T$ 与函子的加性给出
  $ id_(K_1 (R))+K_1 (T)=K_1 (T) $
  所以对每个 $x in K_1 (R)$, 有 $x+K_1 (T)(x)=K_1 (T)(x)$. 在 Abel 群中消去右边的项, 就得到 $x=0$.
]

这与#chapter-ref(<chap-k0>)中 $K_0$ 的 Eilenberg 消去法是同一个论证, 对应 @Wei13[III, 推论 1.7.3].

== 相对 $K_1$ 与基本定理

取商或局部化后, 原来不同的 $K_1$ 类可能变得相同, 也可能出现不能提升的新类. 相对群与边界映射用来描述这两种现象. 下面先建立相应的正合列, 再用它们研究多项式环和 Laurent 多项式环. 本节列出主要结论, 详细证明见 @Wei13[III, §2--§3].

=== 相对 $K_1$

#definition(title: [相对第一 $K$ 群])[
  设 $I$ 是含幺环 $R$ 的双边理想. 定义
  $ GL(R,I):=ker (GL(R)->GL(R slash I)) $
  它由模 $I$ 后成为单位矩阵的稳定可逆矩阵组成. 记 $E(R,I)$ 为所有 $e_(i j)(a)$, $a in I$, 在 $E(R)$ 中生成的*正规闭包*. 定义
  $ K_1 (R,I):=GL(R,I) slash E(R,I) $
] <def-relative-k1>

相对 Whitehead 引理保证 $E(R,I)$ 在 $GL(R,I)$ 中正规, 且包含其交换子子群, 所以这个商是 Abel 群. 环同态 $R->S$ 若将 $I$ 送入理想 $J$, 就诱导 $K_1 (R,I)->K_1 (S,J)$. 参见 @Wei13[III, 引理 2.1 与定义 2.2].

自然映射 $K_1 (R,I)->K_1 (R)$ 的像是 $ker (K_1 (R)->K_1 (R slash I))$, 但它本身可能有核, 因而相对群保留了更多提升信息.

此外, $E(R,I)$ 的正规闭包在整个 $E(R)$ 中取, 所以相对群还可能依赖理想所处的环. 即使环映射将 $I$ 同构地送到另一个环的理想, 也未必诱导相对 $K_1$ 的同构. 这称为*切除性质的失效*, 见 @Wei13[III, 注 2.2.1].

若 $R$ 交换, 记
$ U(R,I):=ker (R^times->(R slash I)^times), quad
  S K_1 (R,I):=ker (det:K_1 (R,I)->U(R,I)) $
与绝对情形一样, 行列式由一阶矩阵分裂, 因而
$ K_1 (R,I) tilde.eq U(R,I) plus.o S K_1 (R,I) $

#proposition(title: [Jacobson 根中的理想])[
  若 $I subset.eq J(R)$, 则 $1+I->K_1 (R,I)$ 满射. 若 $R$ 还交换, 则行列式给出
  $ K_1 (R,I) tilde.eq 1+I, quad S K_1 (R,I)=0 $
  特别地, 这适用于交换环的幂零理想.
] <prop-relative-k1-radical>

这里 $1+I$ 取乘法群结构. 结论来自模 $I$ 为单位矩阵的相对消元, 见 @Wei13[III, 引理 2.4]. 例如 $R=k[epsilon] slash (epsilon^2)$, $I=(epsilon)$ 时,
$ K_1 (R,I) tilde.eq 1+epsilon k tilde.eq (k,+) $
最后一个同构将 $1+a epsilon$ 送到 $a$. 所以 $K_1$ 能检测到这类幂零信息.

=== 相对正合列

为写出连接映射, 先补充相对 $K_0$ 的一个模型. 令
$ D:=R times_(R slash I) R, quad
  K_0 (R,I):=ker (K_0 (D)->^(K_0 (p_1)) K_0 (R)) $
其中 $p_1,p_2:D->R$ 是两个投影. 从 $K_0 (R,I)$ 到 $K_0 (R)$ 的映射由另一个投影 $p_2$ 诱导. 这个相对群也可记为 $K_0 (I)$, 它只依赖非含幺环 $I$, 见 @Wei13[II, §2].

#theorem(title: [理想的正合列])[
  对每个双边理想 $I subset.eq R$, 有自然正合列
  $ &K_1 (R,I)->K_1 (R)->K_1 (R slash I) \
    &quad ->^partial K_0 (R,I)->K_0 (R)->K_0 (R slash I) $
] <thm-relative-k1-k0-sequence>

连接映射 $partial$ 可以用拼接理解: 对 $g in GL_n (R slash I)$, 用 $g$ 将两份 $R^n$ 沿商环识别, 得到 $D$ 上的投射模, 再减去平凡拼接 $D^n$ 的类. 正合性说明, $partial([g])=0$ 恰好表示 $[g]$ 能从 $K_1 (R)$ 提升. 这就是 @Wei13[III, 命题 2.3].

若商映射 $R->R slash I$ 有环同态截面, 则进一步有
$ K_1 (R) tilde.eq K_1 (R slash I) plus.o K_1 (R,I) $
这是 @Wei13[III, 习题 2.7]. 后面的多项式取值映射就是这种情形.

=== 拼接与局部化

若 $f:R->S$ 将 $I$ 同构地送到 $S$ 的一个理想, 则
$ R tilde.eq S times_(S slash I) (R slash I) $
这是一个 *Milnor 方块*. 对应的 Mayer--Vietoris 正合列是
$ &K_1 (R)->K_1 (S) plus.o K_1 (R slash I)->K_1 (S slash I) \
  &quad ->^partial K_0 (R)->K_0 (S) plus.o K_0 (R slash I)->K_0 (S slash I) $
其中到直和的映射由两次基变换给出, 从直和出发的映射取差. 连接映射同样由自由模的拼接产生. 这让我们能从较简单的环计算拼接环的 $K$ 群, 见 @Wei13[III, 定理 2.6].

局部化也有类似的连接映射. 设 $R$ 交换, $T subset.eq R$ 是乘法集. 沿用#chapter-ref(<chap-perfect-complex>)的完美复形, 记
$ cat("Perf")_T (R):={P in cat("Perf")(R) | P times.o_R T^(-1) R tilde.eq 0}, quad
  K_0 (R " on " T):=K_0 (cat("Perf")_T (R)) $
这里的张量积取导出张量积. 这个群记录局部化后消失的完美复形.

#theorem(title: [连接 $K_1$ 与 $K_0$ 的局部化列])[
  有自然正合列
  $ K_1 (R)->K_1 (T^(-1) R)->^partial K_0 (R " on " T)->K_0 (R)->K_0 (T^(-1) R) $
] <thm-k1-localization-overview>

连接映射有一个具体公式. 将 $g in GL_n (T^(-1) R)$ 写成 $a slash s$, 其中 $a in M_n (R)$, $s in T$, 则
$ partial([g])=[cofib (a:R^n->R^n)]-n[cofib (s:R->R)] $
这些余纤维在局部化后都消失, 所以属于 $cat("Perf")_T (R)$. 两端的自由模通常不在这个子范畴中, 因而不能在这里直接把余纤维的类消成零. 例如 $R=ZZ$, $T=ZZ without {0}$ 时, 对素数 $p$ 有 $partial([p])=[ZZ slash p ZZ]$. 参见 @Wei13[III, 引理 3.1 与定理 3.2].

#proposition(title: [局部化边界的两项模型])[
  $K_0 (R " on " T)$ 由两项完美复形 $P_1->P_0$ 的类生成, 其中 $P_0,P_1$ 是有限生成投射模, 且该映射在局部化后成为同构. 映射
  $ K_0 (R " on " T)->K_0 (R) $
  的核由 $[cofib (alpha:R^n->R^n)]$ 生成, 其中 $T^(-1) alpha$ 可逆.

  更一般地, 若 $P,Q in cat("Proj")(R)$, $alpha,beta:P->Q$ 在局部化后都成为同构, 记它们的局部化为 $alpha_T,beta_T$, 则
  $ partial([beta_T^(-1) alpha_T])=[cofib (alpha)]-[cofib (beta)] $
  左边使用投射模自同构在 $K_1 (T^(-1) R)$ 中的类.
] <prop-k1-localization-two-term>

因此, 计算这个边界时可以只处理两个投射模之间的映射. 参见 @Wei13[III, 引理 3.1.5 与习题 3.2].

#corollary(title: [非零因子的余核公式])[
  若 $T$ 中的元素都是非零因子, 记 $cal(H)_T (R)$ 为局部化后消失, 且具有有限生成投射模的有限长分解的 $R$-模范畴. 以短正合列为关系定义其 $K_0$, 则
  $ K_0 (R " on " T) tilde.eq K_0 (cal(H)_T (R)) $
  在这个同构下, 上述 $alpha,beta$ 都是单射, 且
  $ partial([beta_T^(-1) alpha_T])=[coker (alpha)]-[coker (beta)] $
  特别地, $partial([s])=[R slash s R]$ 对每个 $s in T$ 成立.
] <cor-k1-localization-cokernel>

参见 @Wei13[III, 推论 3.1.1]. 这里需要非零因子假设; 一般乘法集仍应使用余纤维.

#theorem(title: [Karoubi 的解析同构正合列])[
  设 $f:A->B$ 是交换环同态, $T subset.eq A$ 是由非零因子组成的乘法集. 若每个 $f(s)$ 仍是非零因子, 且 $f$ 对每个 $s in T$ 都诱导同构
  $ A slash s A tilde.eq B slash f(s) B $
  则称 $f$ 为沿 $T$ 的*解析同构*. 此时有自然正合列
  $ &K_1 (T^(-1) A) plus.o K_1 (B)->K_1 (T^(-1) B) \
    &quad ->K_0 (A)->K_0 (T^(-1) A) plus.o K_0 (B)->K_0 (T^(-1) B) $
  从直和出发的映射取两次基变换之差.
] <thm-k1-analytic-isomorphism>

这个结论说明, 除了 Milnor 方块, 沿所有 $s$ 的商环保持不变也能产生拼接正合列. 见 @Wei13[III, 习题 3.10].

=== 多项式环与幂零自同态 <sec-k1-nil-endomorphisms>

现在考察加入一个多项式变量会增加哪些类. 以下变量都与系数交换. 对 $i=0,1$, 定义
$ N K_i (R):=ker (K_i (R[t])->^(t mapsto 0) K_i (R)) $
常数包含分裂取值映射, 所以
$ K_i (R[t]) tilde.eq K_i (R) plus.o N K_i (R) $
其中 $N K_i (R)$ 衡量加入一个多项式变量后新增的部分. 特别地,
$ N K_1 (R) tilde.eq K_1 (R[t],(t)) $
若 $a$ 是 $R$ 的中心元素, 将取值点从 $0$ 换成 $a$ 也得到
$ N K_i (R) tilde.eq K_i (R[t],(t-a)) quad (i=0,1) $
这些同构由变量平移与分裂取值得到, 见 @Wei13[III, 定义 3.3].

#lemma(title: [Higman 技巧])[
  $N K_1 (R)$ 的每个元素都可由 $I_n-t nu$ 表示, 其中 $nu in M_n (R)$ 是幂零矩阵. 换句话说, 若 $g in GL_m (R[t])$ 且 $g(0)=I_m$, 则稳定化与初等变换可以把 $g(t)$ 的 $K_1$ 类化成这个形式.
] <lem-k1-higman-trick>

见 @Wei13[III, 引理 3.5.1]. 当 $nu^N=0$ 时, 可逆性由有限和直接看出:
$ (I-t nu)^(-1)=I+t nu+dots+t^(N-1) nu^(N-1) $
为了同时记录这些矩阵及其加性关系, 引入下面的范畴.

#definition(title: [幂零自同态的 $K_0$])[
  $cat("Nil")(R)$ 的对象是 $(P,nu)$, 其中 $P in cat("Proj")(R)$, $nu:P->P$ 幂零. 态射 $f:(P,nu)->(Q,mu)$ 是满足 $f nu=mu f$ 的 $R$-线性映射. 一个序列称为短正合列, 如果忘掉自同态后是模的短正合列.

  以对象的同构类为生成元, 并对每个短正合列加入关系
  $ [(P,nu)]=[(P',nu')]+[(P'',nu'')] $
  得到 $K_0 (cat("Nil")(R))$. 定义约化群
  $ op("Nil")_0 (R):=ker (K_0 (cat("Nil")(R))->K_0 (R)) $
  箭头忘掉 $nu$. 截面 $P mapsto (P,0)$ 给出
  $ K_0 (cat("Nil")(R)) tilde.eq K_0 (R) plus.o op("Nil")_0 (R) $
] <def-nilpotent-endomorphism-k0>

底层模的短正合列总能分裂, 但分裂未必与幂零自同态相容. 因而这里的关系包含了自同态的扩张信息.

#theorem(title: [幂零自同态描述 $N K_1$])[
  对每个含幺环 $R$, 有自然同构
  $ op("Nil")_0 (R) tilde.eq N K_1 (R) $
  其具体公式是
  $ [(P,nu)]-[(P,0)] mapsto ⟨P[t],id-t nu⟩ $
  这里 $P[t]=P times.o_R R[t]$, 右边是投射模自同构给出的 $K_1$ 类. 因而
  $ K_0 (cat("Nil")(R)) tilde.eq K_0 (R) plus.o N K_1 (R) $
] <thm-nil0-nk1>

Higman 技巧提供了矩阵代表, 这个同构则识别了代表之间的关系: 它们恰好来自幂零自同态的短正合列. 参见 @Wei13[III, 命题 3.5.3].

#corollary(title: [多项式环嵌入 Laurent 多项式环])[
  对任意含幺环 $R$, 自然映射
  $ K_1 (R[t])->K_1 (R[t,t^(-1)]) $
  是单射. 更精确地, 有自然分裂短正合列
  $ 0->K_1 (R[t])->K_1 (R[t,t^(-1)])->^partial K_0 (cat("Nil")(R))->0 $
  边界满足 $partial([t I_n-nu])=[(R^n,nu)]$.
] <cor-k1-polynomial-laurent-injection>

见 @Wei13[III, 推论 3.5.5 与式 (3.6.2)]. 边界在这里保留完整的幂零自同态; 再忘掉自同态, 才得到基本定理中取值于 $K_0 (R)$ 的边界.

=== Laurent 多项式环的基本定理 <sec-k1-laurent-fundamental>

#theorem(title: [$K_1$ 的基本定理])[
  对任意含幺环 $R$, 有自然分裂正合列
  $ &0->K_1 (R)->^Delta K_1 (R[t]) plus.o K_1 (R[t^(-1)]) \
    &quad ->^d K_1 (R[t,t^(-1)])->^partial K_0 (R)->0 $
  其中 $Delta(x)=(x,x)$, $d$ 取两次包含诱导映射之差. 因而有自然分解
  $ K_1 (R[t,t^(-1)]) tilde.eq K_1 (R) plus.o K_0 (R) plus.o N K_1 (R) plus.o N K_1 (R) $
] <thm-k1-fundamental-overview>

两个 $N K_1$ 项分别来自 $R[t]$ 与 $R[t^(-1)]$. $K_0$ 项则由前面的外积给出: 对有限生成投射模 $P$, 把 $[P]$ 送到 $P times.o_R R[t,t^(-1)]$ 上自同构 $t dot id$ 的类. 其分裂由局部化边界构造, 将上述类送回 $[P]$; 关键计算是 $t:P[t]->P[t]$ 的余核正是 $P$, 其中 $t$ 作用为零. 见 @Wei13[III, 定理 3.6].

把这个公式降低一个次数, 就会出现第一负群 $K_(-1)$. 我们在#link(<sec-negative-k-theory>)[本章最后一节]集中定义它并陈述 $K_0$ 的基本定理. 先看正则性怎样简化上面的公式.

=== 正则性与分次环 <sec-ki-regular-rings>

#definition(title: [$K_i$-正则环])[
  固定 $i=0$ 或 $1$. 若对每个 $m>=1$, 常数包含都诱导同构
  $ K_i (R) tilde.eq K_i (R[t_1,dots,t_m]) $
  则称 $R$ 为 *$K_i$-正则环*. 等价地,
  $ N K_i (R[t_1,dots,t_m])=0 quad (m>=0) $
] <def-ki-regular-ring>

这个条件要求任意多个变量上的同伦不变性. 单独写 $N K_i (R)=0$ 只表达一个变量的情形. 见 @Wei13[III, 定义 3.4].

#corollary(title: [正则环上的同伦不变性])[
  若 $R$ 是交换正则 Noetherian 环, 则
  $ K_1 (R[t]) tilde.eq K_1 (R), quad
    K_1 (R[t,t^(-1)]) tilde.eq K_1 (R) plus.o K_0 (R) $
] <cor-k1-regular-homotopy-invariance>

这时 $N K_1 (R)=0$, 基本定理中的两个额外项消失, 见 @Wei13[III, 定理 3.8]. 对域 $k$, 有 $K_1 (k[t,t^(-1)]) tilde.eq k^times plus.o ZZ$, 两个分量由单位 $a t^n$ 的系数 $a$ 与指数 $n$ 给出.

结合 $K_0$ 的同伦不变性, 交换正则 Noetherian 环同时是 $K_0$-正则与 $K_1$-正则的. 对多项式环反复应用这个结论, 就得到任意有限多个变量的版本. 参见 @Wei13[II, 定理 6.5 与 III, 定理 3.8].

#proposition(title: [分次环的零次部分])[
  设 $R=plus.o.big_(n>=0) R_n$ 是非负分次环, $i=0,1$. 投影 $R->R_0$ 给出的核满足自然嵌入
  $ ker (K_i (R)->K_i (R_0)) arrow.r.hook N K_i (R) $
  特别地, 若 $N K_i (R)=0$, 则 $K_i (R_0)->K_i (R)$ 是同构.
] <prop-ki-graded-ring>

这个嵌入来自环同态 $R->R[t]$, 它将齐次元素 $r_n$ 送到 $r_n t^n$. 在 $t=1$ 处恢复原环, 在 $t=0$ 处只留下零次部分. 见 @Wei13[III, 引理 3.4.1].

#theorem(title: [正则性的局部化])[
  设 $R$ 交换, $s in R$, $i=0,1$. 代换 $t mapsto s t$ 诱导自同态
  $ sigma_s:N K_i (R)->N K_i (R) $
  并且
  $ N K_i (R[1 slash s]) tilde.eq varinjlim(j>=0) (N K_i (R),sigma_s) $
  右边表示沿 $sigma_s$ 反复迭代的序列的余极限.

  因而 $K_i$-正则性在局部化 $R->R[1 slash s]$ 下保持, 也在 Laurent 扩张 $R->R[t,t^(-1)]$ 下保持. 此外, 每个交换 $K_1$-正则环都是 $K_0$-正则环.
] <thm-ki-regular-localization>

$i=0$ 的局部化公式是 Vorst 定理, 见 @Wei13[III, 定理 3.4.3 与推论 3.4.4]; $i=1$ 的版本及最后的蕴含见 @Wei13[III, 习题 3.9]. 这里的 $sigma_s$ 是变量缩放诱导的运算.

=== 系数特征与幂零加厚

#proposition(title: [$N K_i$ 的挠性与可除性])[
  以下 $A$ 是含幺环, $p$ 是素数.

  + 若 $p^r A=0$ 对某个 $r>=1$ 成立, 则 $N K_1 (A)$ 是 $p$-初级挠群. 即每个元素都被某个 $p$ 的幂消去, 这个幂可以依赖于元素.
  + 若 $p$ 在 $A$ 中可逆, 则乘以 $p$ 是 $N K_i (A)$ 的自同构, $i=0,1$.
  + 若 $A$ 是特征零域 $k$ 上的代数, 则 $N K_0 (A)$ 与 $N K_1 (A)$ 都具有 $k$-向量空间结构. 特别地, 它们作为 Abel 群唯一可除.
] <prop-nki-torsion-divisibility>

这些结论见 @Wei13[III, 例 3.3.1, 例 3.3.2 与习题 3.7]. 第一条直接反映了 Higman 代表的性质: 特征 $p$ 时, 对充分大的 $e$, 有 $(I-t nu)^(p^e)=I$.

#example(title: [截断多项式环的幂零项])[
  设 $R$ 是交换正则 Noetherian 环, $A=R[x] slash (x^N)$, $N>=2$. 则自然映射给出
  $ S K_1 (A[t]) tilde.eq S K_1 (A) tilde.eq S K_1 (R) $
  行列式进一步给出
  $ N K_1 (A) tilde.eq 1+x t A[t] $
  右边取乘法群结构. 与 @thm-nil0-nk1 合用时, 这个同构将
  $ [(P,nu)]-[(P,0)] mapsto det(1-t nu) $
  见 @Wei13[III, 例 3.8.1].

  特别地, 对双数环 $A=k[epsilon] slash (epsilon^2)$,
  $ N K_1 (A) tilde.eq 1+epsilon t k[t] tilde.eq (t k[t],+) $
  最后一个同构将 $1+epsilon f(t)$ 送到 $f(t)$. 因而即使约化环 $k$ 的 $N K_1$ 为零, 加入一个平方为零的方向后, 也会出现非零的幂零项.
] <ex-nk1-truncated-polynomial>

== 负 $K$-理论 <sec-negative-k-theory>

#link(<sec-k1-laurent-fundamental>)[Laurent 多项式环的基本定理]从 $K_1$ 接到 $K_0$. 若从 $K_0$ 出发重复同样的构造, 两侧多项式环的类未必覆盖整个 Laurent 环的 $K_0$. 其余核就是第一负群 $K_(-1)$.

#definition(title: [Bass 的第一负 $K$ 群])[
  设 $R$ 是含幺环, 多项式变量与系数交换. 两次包含 $R[t],R[t^(-1)]->R[t,t^(-1)]$ 诱导映射
  $ d:K_0 (R[t]) plus.o K_0 (R[t^(-1)])->K_0 (R[t,t^(-1)]) $
  其中 $d(x,y)$ 是两次扩张标量所得类之差. 定义
  $ K_(-1) (R):=coker (d) $
] <def-negative-k-groups>

也就是说, 从 Laurent 环上的虚投射模类出发, 将来自两侧多项式环的类都视为零, 剩下的群就是 $K_(-1) (R)$. 见 @Wei13[III, 定义 4.1].

#theorem(title: [$K_0$ 的基本定理])[
  对任意含幺环 $R$, 有自然分裂正合列
  $ &0->K_0 (R)->^Delta K_0 (R[t]) plus.o K_0 (R[t^(-1)]) \
    &quad ->^d K_0 (R[t,t^(-1)])->^partial K_(-1) (R)->0 $
  因而有自然分解
  $ K_0 (R[t,t^(-1)]) tilde.eq K_0 (R) plus.o K_(-1) (R) plus.o N K_0 (R) plus.o N K_0 (R) $
] <thm-k0-fundamental-overview>

其中 $Delta(x)=(x,x)$, $d$ 取两次包含诱导映射之差, 与 @thm-k1-fundamental-overview 中相同. 参见 @Wei13[III, 定理 3.7].

#proposition(title: [$K_(-1)$ 的基本性质])[
  + 环同态 $R->S$ 自然诱导 $K_(-1) (R)->K_(-1) (S)$. 它保持有限乘积与 Morita 等价, 特别地,
    $ K_(-1) (R times S) tilde.eq K_(-1) (R) plus.o K_(-1) (S), quad
      K_(-1) (M_n (R)) tilde.eq K_(-1) (R) quad (n>=1) $
  + 若 $I subset.eq R$ 是幂零双边理想, 则商映射诱导 $K_(-1) (R) tilde.eq K_(-1) (R slash I)$.
  + 若 $R$ 是交换正则 Noetherian 环, 则 $K_(-1) (R)=0$. 特别地, 域与 $ZZ$ 的第一负群都为零.
] <prop-negative-k-basic>

函子性, 乘积与幂零不变性直接由 $K_0$ 的相应性质传到余核. Morita 等价也与多项式扩张相容. 正则环的消失结论见 @Wei13[III, 定义 4.1 后的说明].

#theorem(title: [拼接正合列延伸到负一次])[
  若环同态 $R->S$ 将双边理想 $I$ 同构地送到 $S$ 的一个理想, 则 Milnor 方块的正合列继续为
  $ &K_0 (R)->K_0 (S) plus.o K_0 (R slash I)->K_0 (S slash I) \
    &quad ->^partial K_(-1) (R)->K_(-1) (S) plus.o K_(-1) (R slash I)->K_(-1) (S slash I) $
  其中从直和出发的映射取差.
] <thm-negative-k-milnor>

因此, 商环上的类 $x in K_0 (S slash I)$ 能写成两侧限制之差, 当且仅当 $partial(x)=0$. 这说明 $K_(-1)$ 怎样记录 $K_0$ 中的拼接障碍. 定理见 @Wei13[III, 定理 4.3], 这里不证明.

#example(title: [一个非零的第一负群])[
  设 $k$ 是域, 令
  $ R={f in k[t] | f(0)=f(1)} tilde.eq k[t] times_(k times k) k $
  两个映射分别是在 $0,1$ 处取值与对角映射. 几何上, 这是把仿射直线上的两个点粘在一起.

  因为 $K_(-1) (k[t])=K_(-1) (k)=0$, 上述正合列给出
  $ K_0 (k[t]) plus.o K_0 (k)->K_0 (k times k)->K_(-1) (R)->0 $
  第一箭头在秩上是 $(a,b) mapsto (a-b,a-b)$, 所以
  $ K_(-1) (R) tilde.eq (ZZ plus.o ZZ) slash ZZ(1,1) tilde.eq ZZ $
  这里留下的正是两个粘合点上的秩之差.
] <ex-negative-k-node>

本章的矩阵计算最终都围绕 $GL(R) slash E(R)$ 展开. 下一步转向 $E(R)$ 内部, 研究乘积为单位矩阵的初等变换序列. #chapter-ref(<chap-k2>)将从这些序列及其关系定义 $K_2$.
