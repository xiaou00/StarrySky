#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= 模叠 / Moduli Stacks

== 粗模空间

Hilbert与Quot能精确分类族, 但它们还记着嵌入或商映射. 若忘掉这些额外数据, 只分类对象本身, 精模空间就未必存在. 这个困难在线丛上已经出现了.

#block(breakable: false)[
#example(title:[线丛为什么没有精模空间])[
  在域 $k$ 上, 考虑模函子
  $ F_"line" (T)={T "上的线丛"} slash tilde.eq $
  态射上的作用是拉回. 这是让一维向量空间随参数 $T$ 变化, 没有指定基.

  取 $T=PP_k^1$, 它的两个标准仿射开集记为 $U_0,U_1$. 线丛 $cal(O)_T$ 与 $cal(O)_T (1)$ 在每个 $U_i$ 上都平凡, 但在 $T$ 上不同构: 它们的次数分别为 $0$ 与 $1$.

  假如代数空间 $M$ 表示 $F_"line"$, 这两个线丛就对应不同的态射 $f,g:T->M$. 自然性却要求
  $ f|_(U_i)=g|_(U_i), quad i=0,1 $
  由代数空间的层性, 得到 $f=g$, 矛盾. 所以这个函子没有精模空间.
] <ex-line-family-obstruction>
]

问题在于, *局部同构的族可能整体不同构*, 而映向代数空间的态射由局部限制唯一确定. 同样的论证说明: 对任何模函子 $F$ 和自然变换 $F->h_M$, 局部同构的两个族都必须给出同一个 $T->M$. 只要这种族整体不同构, 分类映射就不可能是双射.

因此, 若仍希望用代数空间研究分类, 就必须放宽对族的要求: 每个族给出一个态射, 几何点仍准确记录单个对象的同构类, 但允许不同的族给出同一态射. 寻找这样的空间及其万有性, 就是这里的*粗模问题*.

#block(breakable: false)[
#definition(title:[粗模空间的函子表述])[
  设 $F:(Sch_S)^opp->Set$ 为记录族的同构类的模函子. 一个 $S$-代数空间 $M$ 连同自然变换
  $ eta:F->h_M, quad h_M (T)=Hom_S (T,M) $
  称为 $F$ 的*粗模空间* (coarse moduli space), 若满足:

  + *几何点分类.* 对每个带有 $Spec Omega->S$ 的代数闭域 $Omega$, 映射
    $ eta_(Spec Omega):F(Spec Omega)->M(Omega) $
    是双射.
  + *万有性.* 对任意 $S$-代数空间 $Y$ 和自然变换 $nu:F->h_Y$, 存在唯一的 $S$-态射 $a:M->Y$ 使
    $ nu=h_a compose eta $
    其中 $h_a$ 将 $f:T->M$ 送到 $a compose f:T->Y$.

  函子语言下的定义见 @Hos15[定义 2.24]; 这里允许目标为代数空间, 并对所有代数闭域值点提出要求.
] <def-coarse-moduli>
]

#remark(title:[放宽了什么])[
  自然性保证分类与拉回相容, 万有性保证其他以代数空间为值的分类都经过 $M$. 它也保证粗模空间唯一到与 $eta$ 相容的唯一同构.

  @def-fine-moduli 要求每个 $eta_T$ 都是双射; 粗模空间只要求代数闭域值点上的双射, 一般没有分类所有族的万有族. 这里说明的是放宽要求的必要性, 粗模空间的存在仍需另行证明.
]

#block(breakable: false)[
#example(title:[线丛的粗模空间是一个点])[
  对上面的 $F_"line"$, 取
  $ M=Spec k, quad eta_T:F_"line" (T)->{T->Spec k} $
  域上的一维向量空间只有一个同构类, 所以几何点条件成立.

  再给定 $nu:F_"line" ->h_Y$. 平凡线丛 $k$ 的像给出一点 $y:Spec k->Y$. 由自然性, $nu_T ([cal(O)_T])$ 是复合 $T->Spec k->^y Y$. 任意线丛都局部平凡, 所以层性迫使它的像也是这个复合. 这就证明了万有性.

  这个点记录了每条纤维都是一维空间, 却不能区分 $PP_k^1$ 上的 $cal(O)$ 与 $cal(O)(1)$. 点上的线丛拉回后总是平凡的, 因而无法作为所有线丛的万有族.
]
]

== Picard概形

上一节让一维向量空间随参数变化. 现在固定一个概形 $X$, 研究 *$X$ 上的线丛怎样变化*. 以下取 $k$ 为代数闭域, $X$ 为非空的光滑射影连通 $k$-概形, 并记
$ X_T=X times_k T, quad p_T:X_T->T $

=== 线丛的粗模问题

#definition(title:[线丛模函子])[
  记 $Pic(Y)$ 为 $Y$ 上线丛的同构类组成的群, 群运算是张量积. 定义
  $ F_X:(Sch_k)^opp->Set, quad F_X (T)=Pic(X_T) $
  对 $h:T'->T$, 用 $(id_X times h)^*$ 拉回线丛.

  这个模问题的*粗模空间*是代数空间 $P$ 连同自然变换 $eta:F_X->h_P$, 满足 @def-coarse-moduli: 对每个代数闭扩域 $Omega slash k$, 有双射 $Pic(X_Omega)->P(Omega)$; 任意自然变换 $F_X->h_Y$ 都由唯一的态射 $P->Y$ 诱导.
] <def-picard-coarse-problem>

先看分类中必然丢失什么. 对 $T$ 上的线丛 $cal(N)$, 两个族
$ cal(L), quad cal(L) times.o p_T^* cal(N) $
在 $cal(N)$ 平凡的开集上同构, 因而给出同一个 $T->P$. 它们的每条纤维也同构: 张量一个一维向量空间不改变线丛的同构类. 所以应先识别*从参数空间拉回的扭曲*.

#definition(title:[Picard函子与Picard概形])[
  *相对Picard函子*定义为
  $ frak(Pic)_(X slash k):=a_"fppf" F_X $
  等价地, 它是预层
  $ T |-> Pic(X_T) slash p_T^* Pic(T) $
  的fppf层化. 这里层化针对参数 $T$ 的覆盖. 若有概形表示这个函子, 就称它为 *Picard概形*, 记作 $Pic_(X slash k)$. 参见 @Stacks26[Tag 0B9L].
] <def-picard-functor>

#remark(title:[其实取值于 $Ab$])[
  张量积给出交换群运算, 单位元是结构层, 逆元是对偶线丛; 拉回保持这些运算. 因而 $F_X$ 实际是到交换群范畴 $Ab$ 的函子. 取商与fppf层化也保留这个结构, 所以
  $ F_X, frak(Pic)_(X slash k):(Sch_k)^opp->Ab $
  前面把它们看作集合值函子, 是复合了遗忘函子 $Ab->Set$.
]

#proposition(title:[商掉基底扭曲后的刻画])[
  在本节假设下, 对任意 $T$ 有自然同构
  $ frak(Pic)_(X slash k)(T) tilde.eq Pic(X_T) slash p_T^* Pic(T) $
  选定 $x in X(k)$, 记 $x_T:T->X_T$ 为相应截面. 每个商类都有一个沿 $x_T$ 平凡的代表
  $ cal(L)^"norm":=cal(L) times.o p_T^* (x_T^* cal(L))^or $
  配上典范平凡化 $x_T^* cal(L)^"norm" tilde.eq cal(O)_T$ 后, 这个代表唯一到保持平凡化的唯一同构.
] <prop-picard-quotient>

#proofsketch[
  光滑射影连通性保证 $(p_T)_* cal(O)_(X_T)=cal(O)_T$, 且对所有 $T$ 成立. 所以线丛的自同构都是乘以来自 $T$ 的可逆函数. 固定沿 $x_T$ 的平凡化后, 相容自同构只剩恒等. 于是局部代表之间相容的同构唯一, 自动满足余循环条件, 可以下降. 因而上述商预层已经是fppf层. 详见 @Stacks26[Tag 0B9N].
]

#theorem(title:[Picard概形的存在与粗模性])[
  存在分离且局部有限型的交换群概形 $P=Pic_(X slash k)$, 对每个 $T$ 有自然同构
  $ Hom_k (T,P) tilde.eq frak(Pic)_(X slash k)(T) tilde.eq Pic(X_T) slash p_T^* Pic(T) $
  它是 @def-picard-coarse-problem 的粗模空间. 群乘法来自张量积, 单位元是 $[cal(O)_X]$, 取逆来自对偶线丛. 对任意扩域 $K slash k$, 还有典范同构
  $ Pic_(X slash k) times_k K tilde.eq Pic_(X_K slash K) $
] <thm-picard-representability>

#proofsketch[
  可表性是Grothendieck的Picard存在定理, 这里引用 @Kle05[定理 4.8]. 对代数闭域 $Omega$, $Pic(Spec Omega)=0$, 所以 @prop-picard-quotient 给出几何点上的双射. 又因为代数空间是fppf层, 任意 $F_X->h_Y$ 都唯一经过层化 $frak(Pic)_(X slash k)$; 再用Yoneda引理, 就得到粗模空间的万有性. 群结构与基变换也由所表示的函子得到.
]

#remark(title:[对哪个模问题是精模空间])[
  $Pic_(X slash k)$ 表示的是 $frak(Pic)_(X slash k)$, 因而对这个修正后的模问题是精模空间. 原始函子 $F_X$ 还区分基底扭曲, 所以它得到的是粗模空间. 在本节条件下, 两个族给出同一分类态射, 恰好意味着它们相差一个 $p_T^* cal(N)$.
]

=== Poincaré线丛

固定上面的点 $x$. 可以把一个线丛 $cal(L)$ 连同指定的平凡化 $alpha:x_T^* cal(L)->^~cal(O)_T$ 作为数据, 同构也要求保持 $alpha$. 这称为*沿 $x$ 刚化*. @prop-picard-quotient 的正规化给出这个模函子与 $frak(Pic)_(X slash k)$ 的自然同构.

#proposition(title:[正规化的Poincaré线丛])[
  在 $X times_k P$ 上存在 *Poincaré线丛* $cal(P)$, 配有平凡化
  $ cal(P)|_({x} times_k P) tilde.eq cal(O)_P $
  它是沿 $x$ 刚化的线丛模问题的万有族. 对任意 $X_T$ 上的线丛 $cal(L)$, 存在唯一的分类态射 $g:T->P$, 使
  $ cal(L) tilde.eq (id_X times g)^* cal(P) times.o p_T^* (x_T^* cal(L)) $
  若 $cal(L)$ 已刚化, 最后一个因子随平凡化消去, 所得同构在保持刚化的意义下唯一.
] <prop-picard-poincare>

#proof[
  在刚化后的函子中, 取 $id_P$ 对应的元素, 就得到 $cal(P)$. 将 $cal(L)^"norm"$ 沿分类态射拉回的表达式展开, 即得公式. 这仍是前文的Yoneda论证.
]

因此, 原始线丛族由两部分恢复: 态射 $g:T->P$, 以及 $T$ 上的线丛 $x_T^* cal(L)$. 粗模空间记录前一部分, 刚化则固定了后一部分. 这解释了Poincaré线丛的万有性与粗模性为什么相容.

=== 连通分支与一阶变化

#proposition(title:[单位分支与光滑性])[
  记 $P^0=Pic_(X slash k)^0$ 为包含 $[cal(O)_X]$ 的连通分支. 它是开闭的射影群概形, 每个连通分支都由张量一个固定线丛从 $P^0$ 平移得到.

  若 $"char" k=0$, 则 $P$ 光滑, $P^0$ 是Abel簇, 即光滑射影连通群概形. 在正特征下, $P^0$ 可能非约化; 它的约化概形 $(P^0)_"red"$ 是Abel簇. 参见 @Kle05[定理 5.4, 推论 5.14].
] <prop-picard-components>

#proposition(title:[切空间])[
  对任意线丛 $cal(L)$, 有典范同构
  $ T_([cal(L)]) Pic_(X slash k) tilde.eq H^1 (X,cal(O)_X) $
  若 $H^2 (X,cal(O)_X)=0$, 则Picard概形光滑, 每个分支的维数都是 $dim_k H^1 (X,cal(O)_X)$. 参见 @Kle05[定理 5.11, 命题 5.19].
] <prop-picard-tangent>

#proofsketch[
  用平移归结到 $[cal(O)_X]$. 在双数环 $k[epsilon] slash (epsilon^2)$ 上, 一个平凡线丛的一阶变形由转移函数 $1+epsilon a_(i j)$ 给出. 余循环条件变成 $a_(i j)+a_(j l)=a_(i l)$, 更换平凡化则改变一个余边界, 因而得到 $H^1 (X,cal(O)_X)$. 提升线丛的障碍落在 $H^2$ 中; 该群为零时, 无穷小提升准则给出光滑性. 参见 @Stacks26[Tag 0C6Q].
]

=== 射影空间与曲线

#block(breakable: false)[
#example(title:[射影空间的Picard概形])[
  对 $n>=1$, 有
  $ Pic_(PP_k^n slash k) tilde.eq coprod_(d in ZZ) Spec k $
  第 $d$ 个点对应 $cal(O)(d)$. 确实, 线丛的同构类由整数 $d$ 分类, 而 $H^1 (PP_k^n,cal(O))=0$ 保证这些点没有无穷小方向. 每个分支上的Poincaré线丛就是 $cal(O)(d)$. 这个例子也说明, 完整Picard概形未必有限型.
]
]

#proposition(title:[曲线的Picard概形与Jacobian])[
  设 $C$ 是光滑射影连通曲线, 属为 $g=dim_k H^1 (C,cal(O)_C)$. 则
  $ Pic_(C slash k)=coprod_(d in ZZ) Pic_(C slash k)^d $
  其中 $Pic_(C slash k)^d$ 参数化次数 $d$ 的线丛, 是光滑射影连通的 $g$ 维概形. 群概形
  $ J(C):=Pic_(C slash k)^0 $
  称为 $C$ 的 *Jacobian簇*. 选定 $x in C(k)$ 后, 张量 $cal(O)_C (-d x)$ 给出 $Pic_(C slash k)^d tilde.eq J(C)$. 参见 @Stacks26[Tag 0BA0].
] <prop-picard-curve>

曲线上的次数在族中局部常值, 所以它先把Picard概形分成一层层的 $Pic^d$. 固定次数后, 线丛的变化就在一个Jacobian的平移中进行.

#block(breakable: false)[
#proposition(title:[从Hilbert到Picard的Abel态射])[
  对 $d>=0$, 有态射
  $ A_d:Hilb_(C slash k)^d -> Pic_(C slash k)^d, quad D |-> [cal(O)_C (D)] $
  在 $[cal(L)]$ 上的纤维是线性系
  $ |cal(L)| tilde.eq PP_k (H^0 (C,cal(L))^or) $
  即非零截面相差非零标量后得到的空间. 这里的对偶与前文的射影空间商约定一致. 当 $d>=max(2g-1,0)$ 时, $A_d$ 是纤维为 $PP_k^(d-g)$ 的射影丛. 参见 @Stacks26[Tag 0BA0].
] <prop-picard-abel>
]

#proofsketch[
  非零截面的零点给出有效除子, 相差非零标量时除子相同. 当 $d>=max(2g-1,0)$ 时, Riemann--Roch给出 $H^1 (C,cal(L))=0$ 与 $h^0 (C,cal(L))=d+1-g$. 因而次数 $d$ 部分的Poincaré线丛的直接像局部自由, 并与基变换相容; 其对偶的射影丛正是 $A_d$.
]

这给出了一个具体的用法: 先在Hilbert概形上移动有效除子 $D$, 再用 $D|->[cal(O)(D)]$ 得到Picard概形中的变化. 同一个线性系中的除子给出同一个Picard点. Picard概形由此记录线丛的变化, Abel态射则把它与前文的子概形模问题联系起来.

== 从模问题到DM叠与Artin叠

=== 把同构保留下来

回到本章开头: $PP_k^1$ 上的 $cal(O)$ 与 $cal(O)(1)$ 局部同构, 整体却不同构. 它们的区别藏在粘合时选取的同构里. 如果先取同构类, 这些粘合数据就丢失了. 因此, 我们现在让参数 $T$ 对应一个*群胚*: 对象是 $T$ 上的族, 箭头是族之间的同构.

以下重新允许任意基底概形 $S$, 在 $(Sch_S)_"fppf"$ 上讨论. 拉回给出 @def-groupoid-prestack 中的反变伪函子
$ cal(X):(Sch_S)^opp->Grpd $
若族及其同构满足 @def-groupoid-stack 的下降条件, 就得到一个*模叠*. 例如线丛及其同构满足fppf下降, 因而组成叠. 局部线丛连同转移同构可以粘合; 不同的转移同构, 可以给出不同的整体线丛.

概形或代数空间 $M$ 也看作叠: $M(T)=Hom_S (T,M)$ 中只放恒等箭头. 群胚版本的Yoneda引理仍然成立: 给出 $T->cal(X)$, 就是给出 $cal(X)(T)$ 中的一个族; 两条态射之间的 $2$-同构, 就是两个族之间的同构.

=== 纤维积与同构空间

要给叠配上代数几何的结构, 先要能谈论它的图册和图册之间的重叠. 这里的重叠也要记住同构.

#block(breakable: false)[
#definition(title:[$2$-纤维积])[
  给定叠的态射 $cal(U)->^f cal(X)<-^g cal(V)$, 定义 $cal(U) times_cal(X) cal(V)$ 的 $T$ 上对象为三元组
  $ (u,v,alpha), quad u in cal(U)(T), quad v in cal(V)(T), quad alpha:f(u)->^~g(v) $
  从 $(u,v,alpha)$ 到 $(u',v',alpha')$ 的箭头是一对同构 $a:u->u'$, $b:v->v'$, 满足
  $ g(b) compose alpha=alpha' compose f(a) $
  拉回逐项进行. 下文涉及叠的纤维积, 都按这个意义理解.
] <def-stack-fibre-product>
]

因此, $U times_cal(X) V$ 的点还记录了两边的族*通过哪个同构被识别*. 当所有对象都是代数空间时, 这就回到通常的纤维积.

#definition(title:[由代数空间表示的态射])[
  叠的态射 $f:cal(X)->cal(Y)$ 称为*由代数空间表示*, 若对每个概形 $T$ 及态射 $T->cal(Y)$, 纤维积
  $ cal(X) times_cal(Y) T $
  都等价于一个代数空间. 对这样的 $f$, 称它光滑, 平展, 非分歧或满射, 是指每次基变换得到的代数空间态射 $cal(X) times_cal(Y) T->T$ 都具有相应性质. 参见 @Stacks26[Tag 04SX].
] <def-stack-representable-morphism>

代数空间态射的光滑性与平展性可以在概形图册上检查. 这样, 上面的定义就把熟悉的几何性质带到了叠之间的态射上.

#proposition(title:[对角态射参数化同构])[
  设 $cal(X)$ 为叠. 对 $xi,eta in cal(X)(T)$, 记同构层为
  $ underline("Isom")_T (xi,eta)(T')="Isom"_(cal(X)(T')) (xi|_(T'),eta|_(T')) $
  其中 $T'->T$. 它是对角态射 $Delta_cal(X):cal(X)->cal(X) times_S cal(X)$ 沿 $(xi,eta):T->cal(X) times_S cal(X)$ 的拉回:
  $ underline("Isom")_T (xi,eta) tilde.eq T times_(cal(X) times_S cal(X)) cal(X) $
  因而 $Delta_cal(X)$ 由代数空间表示, 当且仅当所有这些同构层都是代数空间. 参见 @Stacks26[Tag 045G].
] <prop-stack-diagonal-isom>

#proof[
  右边的对象是一个族 $z$ 及同构 $a:z->^~xi$, $b:z->^~eta$. 将它送到 $b compose a^(-1)$, 就得到左边; 反过来取 $z=xi$, $a=id$. 这给出所需等价.
]

特别地, 取 $xi=eta$, 就得到自同构群层 $underline(Aut)_T (xi)$. 所以对角态射的可表性要求: *族之间的同构也能组成代数空间*. 这正是第一章中让箭头本身带上几何结构的想法.

=== 两种图册

#definition(title:[Artin叠与Deligne--Mumford叠])[
  一个fppf叠 $cal(X)$ 称为*代数叠*, 或 *Artin叠*, 若:

  + 对角态射 $Delta_cal(X)$ 由代数空间表示.
  + 存在概形 $U$ 及光滑满射 $p:U->cal(X)$, 称为一个*光滑图册*.

  若图册可以取为平展满射, 则称 $cal(X)$ 为 *Deligne--Mumford叠*, 简称 *DM叠*. 对角条件保证这里的 $p$ 由代数空间表示, 所以这些性质已有意义. 参见 @Stacks26[Tags 026O, 03YO].
] <def-artin-dm-stack>

图册给出一个由概形 $U$ 参数化的族. 满射性意味着: 任何族在适当的覆盖上, 都同构于这个族的拉回. 平展图册更严格, 因而每个DM叠都是Artin叠.

#block(breakable: false)[
#definition(title:[$DMSt$ 与 $ArtSt$])[
  记生象值fppf层组成的无穷意象为
  $ cal(H)_S:=Sh_(Ani) ((Sch_S)_"fppf") $
  定义 $ArtSt_S$ 为其中所有Artin叠组成的*全子范畴*, $DMSt_S$ 为其中所有DM叠组成的全子范畴. 基底明确时可省去下标 $S$. 由第二章的叠与截断的对应, 有
  $ DMSt_S subset.eq ArtSt_S subset.eq (cal(H)_S)_(<=1) subset.eq cal(H)_S $
  特别地, 对 $cal(X),cal(Y) in ArtSt_S$, 有
  $ Map_(ArtSt_S) (cal(X),cal(Y)) tilde.eq Map_(cal(H)_S) (cal(X),cal(Y)) $
  对 $DMSt_S$ 也一样. 也就是说, *叠态射就是这个无穷意象内的态射*. 可表性, 光滑性等是态射的附加性质.
] <def-dm-artin-categories>
]

#remark(title:[也可以看成 $(2,1)$-范畴])[
  上述映射生象都是 $1$-截断的, 因而可用群胚描述. 其中对象是叠的 $1$-态射, 即与拉回相容的函子族 $f_T:cal(X)(T)->cal(Y)(T)$; 箭头是这些函子族之间相容的自然同构, 即 $2$-同构. 所以 $DMSt_S$ 与 $ArtSt_S$ 也可看成 $(2,1)$-范畴. 这里始终保留这些 $2$-同构, 与经典表述一致. 参见 @Stacks26[Tag 03YP].
]

#block(breakable: false)[
#proposition(title:[DM条件的另一种读法])[
  对Artin叠 $cal(X)$, 有
  $ cal(X) "是DM叠" quad <==> quad Delta_cal(X) "非分歧" $
  证明略, 见 @Stacks26[Tag 06N3].
] <prop-dm-diagonal>
]

结合 @prop-stack-diagonal-isom, 这意味着同构的无穷小提升至多有一个. 特别地, DM叠没有非平凡的无穷小自同构. 判断时要检查自同构群的概形结构, 仅看域值点的个数还不够.

图册也把我们带回群胚. 令
$ R:=U times_cal(X) U, quad R pairarrow U $
则 $R$ 是代数空间, 两个投影给出源与靶, 同构的复合给出群胚乘法. 光滑图册使源与靶光滑, 平展图册使它们平展. 将这个群胚逐点取值后叠化, 得到*商叠* $[U slash R]$, 并有
$ cal(X) tilde.eq [U slash R] $
这就是叠的群胚呈示. 反过来, 源与靶光滑的代数空间群胚也给出Artin叠. 参见 @Stacks26[Tags 044O, 04T3, 04TK].

=== 从熟悉的例子认出叠

#example(title:[代数空间与分类叠])[
  每个代数空间都是DM叠, 它原来的平展图册仍可使用. 这时每个对象只有恒等自同构.

  设 $G slash S$ 为光滑仿射群概形. 前文的 $B G$ 把 $T$ 送到 $G_T$-挠子及其等变同构组成的群胚. 平凡挠子给出图册
  $ S->B G, quad S times_(B G) S tilde.eq G $
  沿一个挠子 $E->T$ 拉回这张图册, 得到的就是 $E->T$, 所以图册光滑满射, $B G$ 是Artin叠. 若 $G slash S$ 有限平展, 这张图册也平展, 因而 $B G$ 是DM叠. 参见 @Stacks26[Tags 04UV, 04TK].

  对乘法群 $bb(G)_m$, $B bb(G)_m (T)$ 等价于 $T$ 上的线丛群胚: 线丛的标架组成 $bb(G)_m$-挠子. 它是Artin叠, 但在非空底上不是DM叠. 确实, 自同构群 $bb(G)_m$ 有无穷小变化: 在双数环上, 乘以 $1+epsilon$ 就是约化后变为恒等的非平凡自同构.
] <ex-bg-algebraic-stack>

#proposition(title:[Picard叠与Picard概形])[
  回到上一节关于 $X slash k$ 的假设, 记 $P=Pic_(X slash k)$, 并选定 $x in X(k)$. 令 $underline(Pic)_(X slash k)(T)$ 为 $X_T$ 上的线丛及其同构组成的群胚, 称为*Picard叠*. 则有叠的等价
  $ underline(Pic)_(X slash k) tilde.eq P times_k B bb(G)_m $
  因而Picard叠是Artin叠, 且不是DM叠. 到粗模空间 $P$ 的态射就是第一投影.
] <prop-picard-stack-product>

#proof[
  由 @prop-picard-poincare, 线丛 $cal(L)$ 给出分类态射 $g:T->P$ 及线丛 $cal(N)=x_T^* cal(L)$. 反过来, $(g,cal(N))$ 给出
  $ (id_X times g)^* cal(P) times.o p_T^* cal(N) $
  同构的线丛给出相同的 $g$. 固定 $g$ 后, 正规化部分之间保持刚化的同构唯一, 剩下的正是 $cal(N)$ 的同构数据. 这两种构造互逆且与拉回相容, 得到叠的等价. Poincaré线丛给出光滑图册 $P->underline(Pic)_(X slash k)$, 其重叠是 $P times_k bb(G)_m$; 非DM性由 @prop-dm-diagonal 得到.
]

=== 怎样想象与使用代数叠

可以把图册 $U->cal(X)$ 想成给对象选了一套局部坐标, 也可能是选了一组基, 一个标记或一套生成元. $U$ 记录带着这些选择的对象, $R=U times_cal(X) U$ 记录不同选择之间的同构. 这些同构还可以随参数变化, 并在特殊对象处出现额外的自同构.

因此, 代数叠同时记录*对象怎样变化, 对象有什么对称, 以及局部的族怎样粘合*. 只在每个几何点旁边写一个群还不够, 因为这样没有说明这些信息如何一起变化. 图册通常也不是精模空间: 一个族可能有多种局部提升到 $U$ 的方式, 它们之间由 $R$ 比较.

#proposition(title:[换基与图册上的检验])[
  代数叠的 $2$-纤维积仍是代数叠, DM叠之间的 $2$-纤维积仍是DM叠. 特别地, 对任意 $S'->S$, 基变换 $cal(X) times_S S'$ 保持这两类性质. 参见 @Stacks26[Tag 04TD].

  若 $U->cal(X)$ 是光滑图册, 则 $cal(X)->S$ 光滑, 当且仅当 $U->S$ 光滑. 局部有限表示也可如此检验. 所以"有光滑图册"并不意味着 $cal(X)$ 对底光滑, 还要看图册自身对底的性质. 参见 @Stacks26[Tags 075T, 06FL].
] <prop-stack-atlas-properties>

#definition(title:[惯性叠])[
  *惯性叠* $I_cal(X)$ 的 $T$ 上对象是
  $ (xi,a), quad xi in cal(X)(T), quad a in Aut(xi) $
  从 $(xi,a)$ 到 $(eta,b)$ 的同构 $h:xi->^~eta$ 要满足 $h compose a=b compose h$. 遗忘 $a$ 得到 $I_cal(X)->cal(X)$, 其在族 $xi:T->cal(X)$ 上的拉回是群代数空间 $underline(Aut)_T (xi)$.

  也可以写成
  $ I_cal(X) tilde.eq cal(X) times_(cal(X) times_S cal(X)) cal(X) $
  这里两条态射都是对角态射. 惯性叠把各个对象的自同构组织成了一个整体.
] <def-inertia-stack>

#proposition(title:[何时回到代数空间])[
  代数叠 $cal(X)$ 等价于代数空间, 当且仅当对每个测试概形 $T$ 和每个 $xi in cal(X)(T)$, 都有 $Aut(xi)={id_xi}$. 等价地, $I_cal(X)->cal(X)$ 是等价. 证明略, 见 @Stacks26[Tag 04SZ].
] <prop-stack-trivial-inertia>

#proposition(title:[在图册上做线性代数])[
  设 $cal(X) tilde.eq [U slash R]$. $cal(X)$ 上的拟凝聚层可以描述为 $U$ 上的拟凝聚层 $cal(F)$, 连同同构
  $ s^* cal(F) ->^~ t^* cal(F) $
  它沿单位拉回为恒等, 并与群胚的复合相容. 层态射也要求保持这些同构. 这给出 $QCoh(cal(X))$ 与上述下降数据范畴的等价; 对有限局部自由层同样成立. 参见 @Stacks26[Tag 06WU].
] <prop-stack-qcoh-descent>

例如要在叠上构造一个向量丛, 可以先在 $U$ 上写出向量丛, 再说明它怎样随坐标变换一起变换. 叠的几何由此仍能落到概形和线性代数上计算.

== 商叠

前面的群胚呈示允许一般的箭头空间 $R$. 现在专门看 $R=G times_S U$ 的情形: 所有箭头都来自一个群的作用. 这给出最常见的一批代数叠, 但并非每个代数叠都有这样的全局呈示.

=== 一般群对象的作用商

先暂时离开概形. 取有有限极限的次典范景 $(C,J)$, 即每个表示预层都是层, 并令 $cal(E)=Sh(C,J)$. 设 $g$ 是 $cal(E)$ 中的群对象, 左作用在对象 $x$ 上. 若最初给定的是 $C$ 中的群对象及其作用, 用Yoneda嵌入就得到这里的情形.

#definition(title:[群对象的商叠])[
  对每个 $u in C$, 先取作用群胚 $x(u) slash slash g(u)$, 再作 $J$-叠化, 定义
  $ [x slash g]:=a_1 (u |-> x(u) slash slash g(u)) $
  其中 $a_1$ 表示群胚值预层的叠化.

  等价地, $[x slash g](u)$ 的对象是一对 $(e,phi)$: $e->u$ 是 $g|_u$ 的右挠子, $phi:e->x$ 满足
  $ phi(p dot a)=a^(-1) dot phi(p) $
  这里挠子指覆盖上等变同构于 $u_i times g$ 的层. 同构 $(e,phi)->(e',phi')$ 是右挠子的等变同构 $h:e->^~e'$, 满足 $phi' compose h=phi$. 拉回同时拉回这两项数据.
] <def-quotient-stack-general>

右挠子与左作用并用, 所以公式中出现 $a^(-1)$. 它只是约定. 挠子 $e$ 记录选择局部坐标的各种方式, $phi$ 则在每种坐标下给出一个 $x$ 中的对象.

#proofsketch[
  在覆盖 $u_i->u$ 上选挠子的截面 $p_i$, 写 $p_j=p_i dot g_(i j)$, 并令 $x_i=phi(p_i)$. 那么
  $ x_i=g_(i j) dot x_j, quad g_(i j) g_(j k)=g_(i k) $
  这正是作用群胚中的下降数据. 反过来, 用 $g_(i j)$ 粘合平凡挠子, 再用 $x_i$ 粘合 $phi$, 就恢复 $(e,phi)$. 对同构的构造也相容. 概形情形的详细论证见 @Stacks26[Tag 04UV].
]

因此, $x(u) slash slash g(u)$ 只描述了*挠子已经平凡*的那些对象; 商叠还加入了局部平凡, 整体可能扭曲的族. 若 $g$ 平凡作用在 $x$ 上, 则 $phi$ 下降到 $u->x$, 从而
$ [x slash g] tilde.eq x times B g, quad B g=[1 slash g] $

#remark(title:[与无穷意象中的商相连])[
  在生象值层组成的无穷意象中, 同一个构造是作用群胚的几何实现:
  $ [x slash g] tilde.eq colim_([n] in Delta^opp) (x times g^n) $
  单纯结构来自作用, 乘法与单位. 允许一般的无穷群对象及同伦相容的作用时, 也用这个公式定义商; 本节的 $g,x$ 是集合值层, 所得商是 $1$-截断的, 所以仍是普通群胚值叠.

  若继续取 $0$-截断, 才得到轨道层
  $ tau_(<=0) [x slash g] tilde.eq a_0 (u |-> x(u) slash g(u)) $
  这一步会忘掉自同构. 它也不能直接当作一般粗模空间的构造: 所得层未必是代数空间.
]

=== 概形上的群作用

固定概形 $S$, 设 $G slash S$ 为平坦, 局部有限表示的群概形, 左作用在 $S$-概形 $U$ 上. 取fppf拓扑, @def-quotient-stack-general 给出的商叠记为 $[U slash G]$.

具体地, 一个 $T-> [U slash G]$ 就是一个右 $G_T$-挠子 $E->T$, 连同满足 $phi(e g)=g^(-1) phi(e)$ 的态射 $phi:E->U$. 挠子总可由代数空间表示; 当 $G$ 仿射时, $E$ 也是概形. 给定 $(E,phi)$, 有 $2$-Cartesian方块

#figure(
  book-diagram(
    cell-size: 0pt, node-inset: 7pt,
    {
      edge((0, 0), (1, 0), label: $phi$, marks: "->")
      edge((0, 0), (0, 1), label: [$G_T$-挠子], label-side: right, marks: "->")
      edge((1, 0), (1, 1), marks: "->")
      edge((0, 1), (1, 1), marks: "->")
      node((0, 0), $E$)
      node((1, 0), $U$)
      node((0, 1), $T$)
      node((1, 1), $[U slash G]$)
    },
  ),
  caption: [商叠中的一族. 在挠子 $E$ 上选好局部坐标后, 族就成为映向 $U$ 的态射.],
)

#proposition(title:[可表的覆盖与代数性])[
  商叠 $[U slash G]$ 是Artin叠, 典范态射 $U->[U slash G]$ 由代数空间表示, 平坦, 局部有限表示且满射, 并且
  $ U times_([U slash G]) U tilde.eq G times_S U $
  若 $G slash S$ 光滑, $U->[U slash G]$ 就是光滑图册; 若 $G slash S$ 平展, 它是平展图册, 商叠因而是DM叠. 一般平坦情形的代数性是一个定理, 并不要求这张覆盖本身光滑. 参见 @Stacks26[Tags 06FH, 06FI].
] <prop-quotient-stack-algebraicity>

#proposition(title:[换基, 稳定子与自由作用])[
  对任意 $S'->S$, 有自然等价
  $ [U slash G] times_S S' tilde.eq [U_(S') slash G_(S')] $
  对 $u:T->U$, 它在商叠中所给对象的自同构群层是 $"Stab"_G (u)$.

  若作用自由, 则 $[U slash G]$ 是代数空间, 等于轨道预层的fppf层化. 特别地, 若 $U->M$ 本身是一个 $G$-挠子, 则
  $ [U slash G] tilde.eq M $
  左挠子与右挠子通过 $g |-> g^(-1)$ 转换后使用同一结论.
] <prop-quotient-stack-basic>

#proofsketch[
  换基直接拉回挠子及等变态射. 平凡挠子的相容自同构恰好是固定 $u$ 的群元素; 一般对象局部如此, 其自同构群是相应稳定子的扭曲. 自由作用使这些群都平凡, 再用 @prop-stack-trivial-inertia. 当 $U->M$ 是挠子时, 它的下降群胚正是作用群胚, 所以商恢复 $M$.
]

在代数闭域 $Omega$ 上, 上述挠子有点, 因而可以平凡化. 所以此时几何点确实由轨道给出, 而每个轨道还保留稳定子. 对一般域或一般参数概形, 则必须保留挠子这项数据.

下面的例子在域 $k$ 上讨论, 特殊假设另行说明.

=== 有限群: 对称与覆盖的扭曲

#example(title:[有限群的分类叠])[
  设 $H$ 为有限抽象群, 视为常值群概形. $B H(T)$ 分类有限平展的 $H$-挠子 $E->T$: 每条几何纤维是一个带自由传递 $H$-作用的有限集合, 但没有选定起点. 它不必是连通覆盖.

  例如在 $RR$ 上, $H=ZZ slash 2 ZZ$ 有平凡挠子 $Spec(RR times RR)$, 也有由复共轭作用给出的 $Spec CC$. 两者成为复数上的族后都平凡, 但在实数上不同构. 一个几何点的轨道表看不见这个区别, $B H$ 则能记录它.

  因为常值有限群概形总是平展的, $B H$ 是DM叠, 这里不要求 $|H|$ 在底上可逆. 对一般作用, $[U slash H]$ 分类 $H$-挠子及其到 $U$ 的等变态射: 在一个有限平展覆盖上选对象, 再用 $H$ 的作用把局部选择相容地识别.
]

#example(title:[直线商掉单位根])[
  设 $k$ 为代数闭域, $n>=2$ 在 $k$ 中可逆, 令 $mu_n$ 通过 $z |-> zeta z$ 作用在 $AA_k^1$ 上. 则 $[AA_k^1 slash mu_n](T)$ 等价于以下数据组成的群胚:
  $ (cal(L),alpha,s), quad alpha:cal(L)^(times.o n)->^~cal(O)_T, quad s in Gamma(T,cal(L)) $
  同构要求同时保持 $alpha$ 与 $s$. 确实, 使 $alpha(e^n)=1$ 的局部标架 $e$ 组成 $mu_n$-挠子, $s$ 在这些标架下的坐标给出等变态射.

  粗模空间是 $AA_k^1$, 分类态射由
  $ t=alpha(s^(times.o n)) $
  给出; 在图册上就是 $t=z^n$. 有限群商的粗模性质见 @Con05[第 3 节]. 在 $z!=0$ 处作用自由, 商叠就是穿孔直线; 原点定义的闭子叠却是 $B mu_n$. 这里保留了"开 $n$ 次根"的对称及其在族中的粘合方式.

  还能看到无穷小信息. 当 $n=2$, $T=Spec(k[epsilon] slash (epsilon^2))$ 时, 平凡线丛上的截面 $0$ 与 $epsilon$ 都满足 $t=s^2=0$, 却不同构, 甚至不能在fppf覆盖后同构. 因而同一个粗模态射可以来自不同的叠中族, 轨道层也未必等于粗模空间.
] <ex-root-quotient>

#remark(title:[有限群概形与有限常值群不同])[
  在特征 $p$ 下, $mu_p=Spec(k[z] slash (z^p-1))$ 有非约化结构. 它有限平坦, 所以 $B mu_p$ 仍是Artin叠, 但自同构群 $mu_p$ 非分歧的条件不成立, 因而不是DM叠. $mu_p(k)$ 只有单位元, 正好说明只数域值自同构会漏掉信息.
]

=== 加法群: 允许更换原点

#example(title:[$B bb(G)_a$ 分类什么])[
  加法群 $bb(G)_a$ 的挠子是一族带固定平移方向的仿射直线: 局部可以选原点, 两个选择之间相差一个函数. 在开覆盖上, 转移写成
  $ z_i=z_j+a_(i j), quad a_(i j)+a_(j k)=a_(i k) $
  更换原点改变一个余边界, 因而
  $ pi_0 (B bb(G)_a (T)) tilde.eq H^1 (T,cal(O)_T) $
  每个挠子的自同构群是加法群 $Gamma(T,cal(O)_T)$. 参见 @Stacks26[Tags 03AJ, 03DW].

  若 $T$ 仿射, 所有这些挠子都平凡, 但仍有平移自同构. 若 $T$ 是属大于零的光滑射影曲线, 非零的 $H^1 (T,cal(O)_T)$ 则给出不能选取整体原点的族. 所以 $B bb(G)_a$ 记录的是原点选择的扭曲, 并不是分类线丛.
]

#example(title:[同一个加法群, 不同作用])[
  让 $bb(G)_a$ 通过平移 $a dot z=z+a$ 作用在 $AA^1$ 上. 一个商对象是加法群挠子 $E->T$ 及到 $AA^1$ 的等变态射. 这条态射使 $E$ 平凡化, 连自同构也被固定, 因而
  $ [AA^1 slash bb(G)_a] tilde.eq Spec k $
  若改成平凡作用, 则
  $ [AA^1 slash bb(G)_a] tilde.eq AA^1 times B bb(G)_a $
  此时数据是一个函数 $f in Gamma(T,cal(O)_T)$, 再加一个独立的加法群挠子.
]

#block(breakable: false)[
#example(title:[特殊纤维出现的平移对称])[
  考虑 $a dot (x,y)=(x,y+a x)$. 记商叠为 $cal(Y)=[AA^2 slash bb(G)_a]$, 函数 $x$ 下降为 $cal(Y)->AA^1$. 在 $x!=0$ 处可唯一用平移消去 $y$, 而在 $x=0$ 处整个群都固定 $y$. 因此
  $ cal(Y)|_(x!=0) tilde.eq bb(G)_m, quad cal(Y) times_(AA^1) {0} tilde.eq AA^1 times B bb(G)_a $
  这个族展示了自同构如何在特殊纤维中出现.
]
]

=== 乘法群: 线丛及其截面

#example(title:[仿射直线的伸缩商])[
  让 $bb(G)_m$ 通过 $a dot z=a z$ 作用在 $AA^1$ 上. 则
  $ [AA^1 slash bb(G)_m](T) tilde.eq { (cal(L),s) | cal(L) "为线丛", s in Gamma(T,cal(L)) }_"群胚" $
  箭头是将一个截面送到另一个截面的线丛同构. 这是群胚的等价, 右边没有取同构类. 标架挠子与截面的局部坐标给出这个对应.

  若 $s$ 处处不为零, 它给出 $cal(O)_T->^~cal(L)$, 所以这部分是 $[bb(G)_m slash bb(G)_m] tilde.eq Spec k$. 若 $s$ 恒为零, 则还保留整个线丛及其标量自同构, 得到闭子叠 $B bb(G)_m$.

  这两个部分并不是两个互不相干的分支: 取 $T=AA^1$, $cal(L)=cal(O)_T$, $s=t$, 非零截面会在 $t=0$ 退化成零截面. 若 $s$ 定义单射 $cal(O)_T->cal(L)$, 它还等价于一个有效Cartier除子; 一般截面则允许更退化的情形.

  这里不变多项式只有常数, 所以仿射不变量商是 $Spec k$. 但商叠有零与非零两个几何轨道, 因而这个点不满足粗模空间的几何点条件.
] <ex-line-section-quotient>

#example(title:[射影空间就是没有共同零点的伸缩商])[
  对同时伸缩各坐标的作用, 有
  $ [(AA_k^(n+1) without {0}) slash bb(G)_m] tilde.eq PP_k^n $
  左边的 $T$ 上对象是线丛 $cal(L)$ 及生成它的 $n+1$ 个截面 $s_0,dots,s_n$, 也就是满射
  $ cal(O)_T^(plus.o (n+1))->>cal(L) $
  这正是前文的射影空间模问题. 生成截面也迫使相容自同构为恒等, 所以这里的商叠确实回到了概形.

  若改用正整数权重 $a_0,dots,a_n$, 作用为 $lambda dot z_i=lambda^(a_i) z_i$, 则分类的是线丛 $cal(L)$ 及无共同零点的截面 $s_i in Gamma(T,cal(L)^(times.o a_i))$. 这称为*加权射影叠*. 在几何点 $z$ 处, 稳定子是
  $ mu_(gcd(a_i : z_i!=0)) $
  若所有权重在 $k$ 中可逆, 它是DM叠. 例如权重 $(1,2)$ 在第二个坐标轴上留下 $mu_2$ 自同构, 所以不能只把它当成一个普通射影空间.
]

#example(title:[更换基与Grassmann概形])[
  $B GL_r (T)$ 分类秩 $r$ 的向量丛: 其局部基组成 $GL_r$-挠子. 对 @prop-grassmann-matrix-quotient 中的满秩矩阵空间 $M$, 则有
  $ [M slash GL_(r,S)] tilde.eq Gr_r (cal(E)) $
  这里更换基后仍保留商映射 $cal(E)_T->>cal(Q)$, 它消去了所有相容自同构. 这解释了为何 $B GL_r$ 是叠, 而这个矩阵商却是精模概形.
]

#block(breakable: false)[
=== 商叠上的计算

#proposition(title:[不变量与等变层])[
  对上述 $[U slash G]$ 及任意 $S$-代数空间 $Y$, 有自然双射
  $ Hom_S ([U slash G],Y) tilde.eq {f:U->Y | f(g dot u)=f(u)} $
  此处到代数空间的态射没有非平凡的 $2$-自同构, 因而可以看作集合. 特别地, 若 $U=Spec A$ 且在域 $k$ 上讨论, 则
  $ Gamma([U slash G],cal(O))=A^G $
  参见 @Stacks26[Tag 0DUH].

  同时, @prop-stack-qcoh-descent 给出
  $ QCoh([U slash G]) tilde.eq QCoh^G (U) $
  右边是带 $G$-等变结构的拟凝聚层. 对向量丛同样成立. 在域 $k$ 上, $B G$ 上的向量丛就是 $G$ 的有限维代数表示; 例如 $bb(G)_m$ 的权重 $d in ZZ$ 给出 $B bb(G)_m$ 上的线丛, 沿分类 $cal(L)$ 的态射拉回后成为 $cal(L)^(times.o d)$, 负次幂按对偶理解.
] <prop-quotient-stack-calculation>
]

#remark(title:[维数也要扣除对称的维数])[
  设 $U$ 为纯 $n$ 维的光滑 $k$-概形, $G$ 为 $d$ 维光滑 $k$-群概形. 因为图册 $U->[U slash G]$ 的相对维数是 $d$, 叠的维数为
  $ dim [U slash G]=n-d $
  参见 @Stacks26[Tag 0DRP]. 例如 $dim B bb(G)_a=dim B bb(G)_m=-1$, 而 $dim [AA^1 slash bb(G)_m]=0$. 负号记录了连续自同构的维数; 这里的维数并不是底层轨道拓扑空间的维数.
]

== Picard叠

$B bb(G)_m$ 分类参数空间上的线丛. 若固定 $X->S$, 改为分类 $X_T$ 上的线丛, 就得到Picard叠. 前面已在有基点的情形见过它; 现在把定义与性质整理出来.

=== 定义与函子性

#definition(title:[相对Picard叠])[
  设 $f:X->S$ 为概形态射, 记 $X_T=X times_S T$, $p_T:X_T->T$. *相对Picard叠*定义为
  $ underline(Pic)_(X slash S):(Sch_S)^opp->Grpd $
  其中 $underline(Pic)_(X slash S)(T)$ 的对象是 $X_T$ 上的线丛, 箭头是线丛的同构. 对 $h:T'->T$, 用 $(id_X times h)^*$ 拉回对象与同构. 拉回之间的典范同构给出所需的相容性.

  这里保留线丛本身及其同构, 也保留从 $T$ 拉回的扭曲. 参见 @Stacks26[Tag 0372].
] <def-relative-picard-stack>

#proof[
  对fppf覆盖 $T_i->T$, 拉回得到 $X_(T_i)->X_T$ 的fppf覆盖. 线丛与同构都能沿它下降, 所以这个群胚值预层已经是叠.
]

#remark(title:[映向 $B bb(G)_m$ 的叠])[
  在 @def-dm-artin-categories 的无穷意象 $cal(H)_S$ 中, 有
  $ underline(Pic)_(X slash S) tilde.eq underline(Map)_(cal(H)_S) (X,B bb(G)_(m,S)) $
  这里 $underline(Map)$ 是*内部映射对象*: 它在 $T$ 上的取值是 $Map_(cal(H)_S) (X_T,B bb(G)_(m,S))$, 正是 $X_T$ 上的线丛群胚. 特别地,
  $ underline(Pic)_(S slash S) tilde.eq B bb(G)_(m,S) $
]

#proposition(title:[张量积, 拉回与换基])[
  张量积给出叠态射
  $ underline(Pic)_(X slash S) times_S underline(Pic)_(X slash S)->underline(Pic)_(X slash S), quad (cal(L),cal(M)) |-> cal(L) times.o cal(M) $
  单位是 $cal(O)_(X_T)$, 逆元是对偶线丛. 结合律与交换律由线丛的典范同构实现, 所以它是无穷意象中的交换群对象. 每个取值群胚也称为*Picard群胚*: 带对称张量积, 且每个对象都有张量逆元.

  对 $S$-态射 $a:Y->X$, 拉回给出 $a^*:underline(Pic)_(X slash S)->underline(Pic)_(Y slash S)$. 对任意 $S'->S$, 则有自然等价
  $ underline(Pic)_(X slash S) times_S S' tilde.eq underline(Pic)_(X_(S') slash S') $
  这些对应都保持张量积. 取同构类后才得到 $Ab$-值预层 $T|->Pic(X_T)$.
] <prop-picard-stack-functoriality>

=== 代数性与自同构

#theorem(title:[Picard叠的代数性])[
  若 $f:X->S$ 紧合, 平坦且有限表示, 则 $underline(Pic)_(X slash S)$ 是Artin叠, 对 $S$ 局部有限表示, 且对角态射仿射, 有限表示.

  证明略. 代数性见 @Stacks26[Tag 0D04], 后两项见 @Stacks26[Tags 0DMB, 0DMA].
] <thm-picard-stack-algebraicity>

对角态射的结论说的是: 两个 $X_T$ 上的线丛之间的同构, 形成一个对 $T$ 仿射的概形. 它不意味着同构唯一, 也不意味着Picard叠光滑.

以下保留这个定理的假设, 并进一步要求对所有 $T->S$ 都有
$ cal(O)_T ->^~ (p_T)_* cal(O)_(X_T) $
直观上, $X_T$ 上的整体函数都来自参数空间. 前面讨论的非空光滑射影连通 $X slash k$, $k$ 代数闭, 就满足这个条件.

#proposition(title:[标量自同构与惯性])[
  对任意 $cal(L) in underline(Pic)_(X slash S)(T)$, 有
  $ Aut(cal(L))=Gamma(X_T,cal(O)_(X_T))^times=Gamma(T,cal(O)_T)^times $
  同样的等式对所有 $T'->T$ 成立, 因而
  $ underline(Aut)_T (cal(L)) tilde.eq bb(G)_(m,T), quad I_(underline(Pic)_(X slash S)) tilde.eq bb(G)_(m,S) times_S underline(Pic)_(X slash S) $
  若 $S$ 非空, Picard叠就不是DM叠. 参见 @Stacks26[Tag 0DM9, 引理 108.8.4].
] <prop-picard-stack-inertia>

#proof[
  线丛的自同态都是乘以函数, 可逆时就是自同构. 再用上面的整体函数条件. 最后, $bb(G)_m$ 不是非分歧的, 由 @prop-dm-diagonal 得到非DM性.
]

=== 到Picard空间的映射

#proposition(title:[取 $0$-截断得到Picard空间])[
  在上述假设下, fppf层
  $ frak(Pic)_(X slash S):=a_"fppf" (T |-> Pic(X_T)) $
  由一个代数空间 $P$ 表示. 存在典范叠态射
  $ q:underline(Pic)_(X slash S)->P, quad P tilde.eq tau_(<=0) underline(Pic)_(X slash S) $
  它把线丛送到相应的局部同构类, 也是Picard叠的粗模空间态射. 若 $P$ 是概形, 就是前面的Picard概形. 可表性见 @Stacks26[Tag 0D2C].
] <prop-picard-stack-truncation>

#proofsketch[
  $0$-截断就是先逐点取同构类再层化, 所以得到上述函子. 映向任意代数空间的态射都唯一经过它. 对代数闭域 $Omega$, 可在 $X_Omega$ 上选一个点作刚化, 此时与 @prop-picard-quotient 一样, $P(Omega)$ 恰好分类线丛的同构类. 这就给出了粗模性.
]

#remark(title:[局部是一份 $B bb(G)_m$])[
  一个 $T->P$ 在fppf覆盖后可以由线丛表示; 给出同一个 $T->P$ 的两个代表, 也在覆盖后同构. 选定一个代表 $cal(L)_0$ 后, 其他代表由
  $ cal(N) |-> cal(L)_0 times.o p_T^* cal(N) $
  描述, 其中 $cal(N)$ 是 $T$ 上的线丛. 同构也恰好对应. 因此 $q$ 在底的fppf覆盖上形如 $T times B bb(G)_m->T$; 这称为一个 *$bb(G)_m$-gerbe*. 参见 @Stacks26[Tag 0DME].

  所以Picard叠可以想成Picard空间上每个位置都保留了线丛的伸缩对称, 并允许这些数据一起扭曲. 一般不能直接写成全局乘积.
]

#proposition(title:[选基点后的乘积分解])[
  若还给定截面 $x:S->X$, 沿 $x$ 刚化便得到
  $ underline(Pic)_(X slash S) ->^~ P times_S B bb(G)_(m,S), quad cal(L) |-> (q(cal(L)),x_T^* cal(L)) $
  在这个等价下, $q$ 是第一投影. 这就是 @prop-picard-stack-product 的相对版本, 证明仍用正规化
  $ cal(L)^"norm"=cal(L) times.o p_T^* (x_T^* cal(L))^or $
  此时 $P$ 本身分类沿 $x$ 刚化的线丛, 从而在 $X times_S P$ 上有正规化的Poincaré线丛. 分解依赖于选定的 $x$.
] <prop-picard-stack-rigidification>

=== 叠上的万有线丛

#proposition(title:[万有线丛始终存在])[
  记 $cal(B)=underline(Pic)_(X slash S)$. 在 $X times_S cal(B)$ 上有典范的万有线丛 $cal(U)$. 对一个分类线丛 $cal(L)$ 的态射 $ell:T->cal(B)$, 有相容的同构
  $ (id_X times ell)^* cal(U) tilde.eq cal(L) $
  而且态射之间的 $2$-同构恰好对应线丛之间的同构. 换言之, 拉回万有线丛给出群胚的等价
  $ Map_S (T,cal(B)) tilde.eq {X_T "上的线丛及其同构"}_"群胚" $
] <prop-picard-stack-universal>

#proof[
  对每个 $ell:T->cal(B)$, 直接取它所分类的 $cal(L)$. 叠中的箭头已经给出了这些线丛在拉回下的识别, 且满足余循环条件, 所以它们定义了 $X times_S cal(B)$ 上的线丛. 这正是群胚版本的Yoneda论证.
]

#remark(title:[与Poincaré线丛的区别])[
  $cal(U)$ 的存在不需要选基点. 而在 $X times_S P$ 上选一条代表所有Picard类的Poincaré线丛, 等价于给 $q$ 选一个截面; 一般未必能做到. 选定 $x$ 时, @prop-picard-stack-rigidification 保证它存在.

  即使如此, $cal(U)$ 也不是Poincaré线丛沿 $id_X times q$ 的直接拉回: 对象的标量自同构在 $cal(U)$ 上按同一标量作用, 而从代数空间拉回的线丛上惯性作用平凡. 在乘积分解下, $cal(U)$ 还要张量 $B bb(G)_m$ 上的万有线丛因子. 这个因子正好保存了参数空间上的扭曲.
]

=== 无穷小变化与例子

#proposition(title:[变形, 自同构与障碍])[
  设 $T subset T'$ 是仿射 $S$-概形的平方零增厚, 理想为 $cal(I)$, 并给定 $X_T$ 上的线丛 $cal(L)$. 记 $cal(J)=p_T^* cal(I)$. 则:

  + 提升 $cal(L)$ 到 $X_(T')$ 的障碍在 $H^2 (X_T,cal(J))$ 中; 障碍为零当且仅当提升存在.
  + 若提升存在, 带有指定限制同构的提升的同构类组成一个 $H^1 (X_T,cal(J))$-挠子.
  + 一个提升上限制为恒等的自同构组成加法群 $H^0 (X_T,cal(J))$.

  所以 $H^1$ 记录线丛怎么动, $H^0$ 记录不改变约化族的自同构, $H^2$ 记录提升能否继续.
] <prop-picard-stack-deformation>

#proofsketch[
  平坦性把 $X_T subset X_(T')$ 的理想识别为 $cal(J)$, 而乘法群 $1+cal(J)$ 通过 $1+a |-> a$ 变成加法群 $cal(J)$. 提升转移函数时, 三重交上的不相容给出 $H^2$ 中的障碍; 两个提升之差给出 $H^1$, 保持提升的坐标变换给出 $H^0$. 参见 @Stacks26[Tag 0C6Q].
]

以下令 $k$ 为代数闭域.

#example(title:[射影空间: 每个次数上一份 $B bb(G)_m$])[
  对 $n>=1$, 选定 $PP_k^n$ 上的一点后, 有
  $ underline(Pic)_(PP_k^n slash k) tilde.eq coprod_(d in ZZ) B bb(G)_m $
  在第 $d$ 部分, 一个族就是 $cal(O)_(PP_T^n) (d) times.o p_T^* cal(N)$, 其中 $cal(N)$ 是 $T$ 上的线丛. Picard概形只记录局部常值的次数 $d$, Picard叠还记录 $cal(N)$ 及其同构.
]

#block(breakable: false)[
#example(title:[曲线: Jacobian上的伸缩对称])[
  设 $C slash k$ 是属 $g$ 的光滑射影连通曲线. 次数给出开闭分解
  $ underline(Pic)_(C slash k)=coprod_(d in ZZ) underline(Pic)_(C slash k)^d $
  选定 $x in C(k)$ 后, 由 @prop-picard-curve 与 @prop-picard-stack-rigidification 得到
  $ underline(Pic)_(C slash k)^d tilde.eq Pic_(C slash k)^d times B bb(G)_m tilde.eq J(C) times B bb(G)_m $
  每个次数部分都是光滑Artin叠, 且
  $ dim underline(Pic)_(C slash k)^d=g-1 $
  这里 $g$ 是线丛的变化维数, 减去的 $1$ 来自标量自同构. 光滑性也可以从曲线上 $H^2=0$ 看出; 相对曲线情形见 @Stacks26[Tag 0DM9, 引理 108.8.5].
]
]

实际使用时, 给出 $X_T$ 上的一族线丛, 就给出 $T->underline(Pic)_(X slash S)$. 若只关心相对Picard类, 复合 $q$ 即可; 若还要拉回万有线丛, 比较族的同构或研究变形, 就保留这个叠态射. 选定基点时, 则可把计算拆成Picard空间上的分类态射与 $T$ 上的一条线丛.

== 叠 $cal(M)_g$

在曲线的Picard叠中, 我们固定曲线, 让线丛变化. 现在让曲线本身变化. 以下固定整数 $g>=2$, 测试对象取任意概形 $T$.

=== 光滑曲线的模问题

#definition(title:[光滑曲线的模群胚])[
  对概形 $T$, 定义群胚 $cal(M)_g (T)$. 其对象是概形态射
  $ pi:C->T $
  满足 $pi$ 光滑, 紧合, 几何纤维是连通的一维曲线, 且对每个 $t in T$ 有
  $ dim_(kappa(t)) H^1 (C_t,cal(O)_(C_t))=g $
  两个对象之间的箭头是 $T$-同构. 对 $f:T'->T$, 用纤维积定义拉回
  $ f^* (C->T):=(C times_T T'->T') $
  连同拉回之间的典范同构, 这给出一个反变函子
  $ cal(M)_g:Sch^opp->Grpd $
  参见 @Stacks26[Tag 0E82]. 这里分类的是曲线本身, 射影嵌入不是数据的一部分.
] <def-smooth-curve-moduli-groupoid>

=== 取同构类会丢失什么

#proposition(title:[同构类预层不满足层性])[
  集合值预层
  $ F_g (T):=pi_0 (cal(M)_g (T)) $
  不是平展层, 因而不能由概形或代数空间表示.
] <prop-curve-isoclasses-not-sheaf>

#proof[
  在 $CC$ 上取一条属为 $g$ 的光滑射影超椭圆曲线 $C$, 记其非平凡超椭圆对合为 $iota$. 考虑有限平展覆盖
  $ U=Spec CC[s,s^(-1)]->T=Spec CC[t,t^(-1)], quad t=s^2 $
  在 $C times U$ 上令
  $ sigma(c,s)=(iota(c),-s), quad C':=(C times U) slash lr(⟨sigma⟩) $
  这个作用自由, 而 $C times U$ 对 $T$ 射影, 所以商 $C'$ 是概形, 见 @Stacks26[Tag 07S7]. 它沿 $U->T$ 拉回后同构于 $C times U$, 因而 $C'->T$ 也是光滑紧合的属 $g$ 曲线族.

  假如 $C' tilde.eq C times T$ 是 $T$-同构, 拉回到 $U$ 后就得到一族自同构
  $ a:U->underline(Aut)(C) $
  这里先用下文的 @cor-curve-aut-finite-etale: $g>=2$ 时, $underline(Aut)(C)$ 是有限平展的群概形. 因为 $U$ 连通, $a$ 必须为常值. 但它要与下降相容, 就必须满足
  $ a_(-s) compose iota=a_s $
  常值情形变成 $a compose iota=a$, 这迫使 $iota=id_C$, 矛盾. 因而
  $ [C']!=[C times T] "在" F_g (T) "中", quad [C']|_U=[C times T]|_U $
  局部相等的两个截面整体不同, 所以 $F_g$ 不是层.
]

这与本章开头线丛的例子是同一个现象: *局部同构类相同, 还没有告诉我们用哪些同构粘合*. 这里每条几何纤维都同构于 $C$, 两个族的区别却保存在下降同构中.

=== 保留同构就能下降

#proposition(title:[曲线模群胚满足下降])[
  $cal(M)_g$ 是fppf叠, 它满足fpqc下降.
] <prop-smooth-curves-descent>

#proof[
  给定fpqc覆盖 $T_i->T$. 先看同构: 两个全局曲线族之间的相容局部同构, 连同它们的逆, 都由概形态射的fpqc下降唯一下降. 两个复合在覆盖后为恒等, 整体也为恒等, 所以得到的仍是同构. 参见 @Stacks26[Tag 040L].

  再看对象. 给定局部曲线 $pi_i:C_i->T_i$ 及重叠上的同构
  $ phi_(i j):C_i|_(T_(i j))->^~C_j|_(T_(i j)), quad T_(i j)=T_i times_T T_j $
  假设它们满足 $phi_(j k) compose phi_(i j)=phi_(i k)$. 我们要把这些曲线连同给定的同构一起下降.

  取曲线自带的线丛
  $ cal(L)_i:=omega_(C_i slash T_i)^(times.o 3), quad omega_(C_i slash T_i)=Omega^1_(C_i slash T_i) $
  先算清楚它在几何纤维 $D$ 上的次数. 由连通性与紧合性, $h^0 (D,cal(O)_D)=1$, 而属的定义给出 $h^1 (D,cal(O)_D)=g$. Serre对偶于是给出 $h^0 (D,omega_D)=g$ 与 $h^1 (D,omega_D)=1$. 对 $omega_D$ 用Riemann--Roch, 得到
  $ g-1=deg omega_D+1-g $
  所以 $deg omega_D=2g-2$, 见 @Stacks26[Tag 0B5B]. 次数对张量积相加, 因而三次张量幂满足
  $ deg omega_D^(times.o 3)=3 deg omega_D=3(2g-2)=6g-6 $
  因为 $g>=2$, 这个次数至少是 $2g+1$, 达到光滑曲线上线丛极丰沛的次数界, 故 $omega_D^(times.o 3)$ 极丰沛. 另外, Serre对偶给出
  $ H^1 (D,omega_D^(times.o 3)) tilde.eq H^0 (D,omega_D^(-2))^or=0 $
  最后为零, 是因为 $omega_D^(-2)$ 的次数为 $-4g+4<0$, 负次数线丛没有非零整体截面. 这两项结论也见 @Stacks26[Tag 0E8X]. 上同调与基变换于是给出有限局部自由层
  $ cal(E)_i:=(pi_i)_* cal(L)_i $
  其形成与任意基变换相容. 评价映射在每条纤维上满射, 由Nakayama引理, 整体也满射, 从而给出 $j_i:C_i->PP_(T_i) (cal(E)_i)$. 因 $C_i->T_i$ 紧合而射影丛对 $T_i$ 分离, $j_i$ 也紧合. 它在每条几何纤维上都是闭嵌入, 因而拟有限, 所以有限. 再对 $cal(O)->(j_i)_* cal(O)_(C_i)$ 的余核用Nakayama引理, 得到 $j_i$ 是闭嵌入.

  关键是这些构造都与曲线同构相容. 因此 $phi_(i j)$ 使 $cal(E)_i$ 带有下降数据, 由有限局部自由层的fpqc下降, 得到 $T$ 上的向量丛 $cal(E)$. 记
  $ Q:=PP_T (cal(E)), quad Q_i=Q times_T T_i $
  在这些识别下, $j_i:C_i arrow.r.hook Q_i$ 彼此相容. 它们的理想层连同单射 $cal(I)_i->cal(O)_(Q_i)$, 由拟凝聚层的下降得到 $cal(I)->cal(O)_Q$. 单射性和理想条件都可忠实平坦地检验, 所以 $cal(I)$ 是理想层. 参见 @Stacks26[Tag 023R]. 令
  $ C:=V(cal(I)) subset Q $
  则 $C times_T T_i tilde.eq C_i$, 而且重叠上的同构正是给定的 $phi_(i j)$.

  最后检查 $C->T$ 的条件. 光滑性与紧合性都可在fpqc覆盖后检验. 对每个 $t in T$, 选一个映到它的 $t_i in T_i$; $C_t$ 扩张到 $kappa(t_i)$ 后就是 $(C_i)_(t_i)$. 几何连通性, 维数与属都可在域扩张后检验, 所以 $C->T$ 属于 $cal(M)_g (T)$. 对象因此可以下降, 相容同构又能唯一下降, 这就证明了fpqc下降, 特别也证明了fppf叠性.
]

#remark(title:[先解决下降, 再构造图册])[
  现在可以称 $cal(M)_g$ 为*属 $g$ 光滑曲线的模叠*. 上面的论证给出了叠性; 要进一步证明它是代数叠乃至DM叠, 还需要构造概形图册并研究对角态射.
]

=== 统一多重典范嵌入

刚才用三重典范线丛把曲线放进射影丛. 现在把这个构造统一起来, 再借助Hilbert概形给曲线族提供参数. 以下固定整数 $m>=3$.

#lemma(title:[多重典范线丛的统一性质])[
  设 $C slash k$ 是属 $g>=2$ 的光滑, 几何连通射影曲线. 则 $omega_C^(times.o m)$ 极丰沛, 且
  $ H^1 (C,omega_C^(times.o m))=0, quad h^0 (C,omega_C^(times.o m))=(2m-1)(g-1) $
] <lem-pluricanonical-uniform>

#proof[
  @prop-smooth-curves-descent 的证明已算出 $deg omega_C=2g-2$. Serre对偶给出
  $ H^1 (C,omega_C^(times.o m)) tilde.eq H^0 (C,omega_C^(times.o (1-m)))^or=0 $
  因为右边线丛的次数 $(1-m)(2g-2)<0$. 再用Riemann--Roch,
  $ h^0 (C,omega_C^(times.o m))=m(2g-2)+1-g=(2m-1)(g-1) $
  另一方面, $deg omega_C^(times.o m)=m(2g-2)>=2g+1$, 所以它极丰沛. 这里用的是曲线上极丰沛的次数判据, 见 @Stacks26[Tag 0H2V].
]

记
$ r:=(2m-1)(g-1), quad N:=r-1 $
选取整体截面的一组基, 就得到 $C arrow.r.hook PP_k^N$. 嵌入后 $cal(O)_C (1)=omega_C^(times.o m)$, 所以再由Riemann--Roch, 它的Hilbert多项式为
$ P_(g,m) (t):=m(2g-2)t+1-g=(2m t-1)(g-1) $
特别地, $m=3$ 时,
$ r=5g-5, quad N=5g-6, quad P_(g,3) (t)=(6g-6)t+1-g $
这些数只依赖 $g,m$, 因而所有这些曲线都能进入同一个Hilbert概形.

#proposition(title:[相对多重典范嵌入])[
  对任意曲线族 $pi:C->T$ 属于 $cal(M)_g (T)$, 记
  $ cal(E)_m:=pi_* omega_(C slash T)^(times.o m) $
  则 $cal(E)_m$ 是秩 $r$ 的有限局部自由层, 其形成与任意基变换相容. 评价满射
  $ pi^* cal(E)_m->omega_(C slash T)^(times.o m) $
  给出闭嵌入
  $ j_m:C arrow.r.hook PP_T (cal(E)_m), quad j_m^* cal(O)(1) tilde.eq omega_(C slash T)^(times.o m) $
  这里仍用线商约定: $PP_T (cal(E)_m)$ 参数化 $cal(E)_m$ 的秩 $1$ 商.
] <prop-relative-pluricanonical>

#proof[
  相对典范线丛与基变换相容. 由 @lem-pluricanonical-uniform, 每条纤维上的 $H^1$ 都为零; 上同调与基变换于是给出局部自由性, 秩以及任意基变换相容性, 参见 @Stacks26[Tag 0B91]. 纤维上的整体生成性给出评价满射. 纤维上的极丰沛性再给出闭嵌入, 论证与 @prop-smooth-curves-descent 中的 $j_i$ 完全相同.
]

所以曲线自身就带有一个统一可用的极化. 在 $cal(E)_m$ 平凡的开集上选基, 就把整族曲线嵌入固定的 $PP^(r-1)$; 接下来要准确描述这些嵌入在Hilbert概形中占据哪一部分.

=== Hilbert概形中的多重典范参数

由 @thm-hilbert-projective-space, 存在射影概形
$ cal(H):=Hilb_(PP_ZZ^N slash ZZ)^(P_(g,m)) $
我们要从中取出由*完整 $m$-典范线性系*嵌入的光滑曲线. 为了定义它的概形结构, 先处理一个线丛条件.

#lemma(title:[相对平凡性是可表条件])[
  设 $f:C->B$ 是紧合, 平坦, 有限表示的曲线族, 几何纤维约化且连通, 并给定 $C$ 上的线丛 $cal(L)$. 则存在局部闭子概形 $Z_cal(L) arrow.r.hook B$, 使任意 $T->B$ 满足
  $ T->B "经过" Z_cal(L) quad <=> quad cal(L)_T tilde.eq f_T^* cal(M) $
  其中右边要求存在 $T$ 上的线丛 $cal(M)$. 若几何纤维还整, 则 $Z_cal(L)$ 在 $B$ 中是闭的.
] <lem-relative-line-triviality-locus>

#proof[
  由纤维的假设, $cal(O)_T tilde.eq (f_T)_* cal(O)_(C_T)$ 对任意 $T->B$ 成立, 见 @Stacks26[Tag 0E0L]. 因而 @prop-picard-stack-truncation 给出相对Picard空间 $P=Pic_(C slash B)$. 取线丛的分类截面 $[cal(L)]:B->P$ 与零截面 $e:B->P$ 的等值子空间 $Z_cal(L)$.

  先说明这个等值条件恰好是题中的条件. 若 $[cal(L)_T]=0$, 则在某个fppf覆盖 $T_i->T$ 上, $cal(L)_(T_i)$ 平凡. 重叠上的转移函数是 $C_(T_i times_T T_j)$ 上的单位; 由上述结构层同构, 它们唯一来自 $T_i times_T T_j$ 上的单位, 且仍满足余循环条件. 因而它们粘成 $T$ 上的线丛 $cal(M)$, 并有 $cal(L)_T tilde.eq f_T^* cal(M)$. 反方向直接由 $cal(M)$ 局部平凡得到.

  最后, $Z_cal(L)->B$ 是 $P->B$ 的对角态射的基变换. 该对角是浸入, 所以 $Z_cal(L)$ 是局部闭子概形; 几何纤维整时 $P->B$ 分离, 因而它是闭子概形. 参见 @Stacks26[Tags 0DMF, 0DNJ].
]

#block(breakable: false)[
#remark(title:[不能只检查几何纤维])[
  条件 $[cal(L)_T]=0$ 比每条几何纤维上的线丛都平凡更强. 例如在代数闭域 $k$ 上取一条正属光滑射影曲线 $C$, 令 $T=Spec(k[epsilon] slash (epsilon^2))$. 由 @prop-picard-stack-deformation, $H^1 (C,cal(O)_C)$ 中的非零类给出 $cal(O)_C$ 的非平凡一阶变形. 它在唯一的几何纤维上平凡, 却不来自 $T$ 上的线丛, 因为 $Pic(T)=0$. 上面的等值子概形也记录了这种无穷小信息.
]
]

#proposition(title:[多重典范Hilbert子概形])[
  存在局部闭子概形
  $ H_(g,m) arrow.r.hook cal(H) $
  它参数化闭子概形 $C arrow.r.hook PP_T^(r-1)$, 其中 $pi:C->T$ 属于 $cal(M)_g (T)$, 并满足:

  + 对某条 $T$ 上的线丛 $cal(M)$, 有
    $ cal(O)_C (1) tilde.eq omega_(C slash T)^(times.o m) times.o pi^* cal(M) $
  + 坐标截面给出的限制映射是同构:
    $ cal(O)_T^(plus.o r)->^~pi_* cal(O)_C (1) $

  第一项只要求这样的 $cal(M)$ 存在, 不把 $cal(M)$ 或同构的选择作为额外数据.
] <prop-pluricanonical-hilbert-locus>

#proof[
  *先选光滑曲线.* 在 $cal(H)$ 中取万有族光滑且几何连通的开子概形 $B$. 这些是开条件: 光滑轨迹是开集, 再用万有族紧合排除含非光滑点的纤维; 光滑紧合族的几何连通分支数局部常值. Hilbert多项式的次数为 $1$, 常数项为 $1-g$, 所以这里的纤维恰好是一维, 属 $g$ 的曲线.

  *再选典范极化.* 在 $B$ 上的万有曲线 $pi:C_B->B$ 上取
  $ cal(L):=cal(O)_(C_B) (1) times.o omega_(C_B slash B)^(times.o (-m)) $
  对它应用 @lem-relative-line-triviality-locus, 得到 $Z_cal(L) subset B$. 光滑连通的几何曲线是整的, 所以这是闭子概形, 并且在任意基变换后都恰好刻画第一项条件.

  *最后选完整线性系.* 在 $Z_cal(L)$ 上, 由 @prop-relative-pluricanonical 和投影公式,
  $ pi_* cal(O)_C (1) tilde.eq cal(E)_m times.o cal(M) $
  是秩 $r$ 的局部自由层, 并与任意基变换相容. 因而限制映射 $cal(O)^(plus.o r)->pi_* cal(O)_C (1)$ 成为同构, 恰好是它的行列式可逆的开条件. 取这个开子概形为 $H_(g,m)$ 即可. 三步都刻画任意测试概形上的条件, 所以这也证明了所述参数化性质.
]

#remark(title:[它参数化带射影标架的曲线])[
  第二项保证坐标截面给出全部典范截面, 即使用完整线性系. 第一项中的底上线丛 $cal(M)$ 也必须保留, 因为
  $ PP_T (cal(E)_m) tilde.eq PP_T (cal(E)_m times.o cal(M)) $
  局部向量标架在重叠上相差一个共同的伸缩, 就给出同一个射影标架. 所以射影丛平凡, 并不要求 $cal(E)_m$ 本身平凡.

  更内在地, $H_(g,m)$ 表示的函子是
  $ H_(g,m) (T) tilde.eq {(C slash T,alpha)} slash tilde.eq $
  其中 $C slash T in cal(M)_g (T)$, 而
  $ alpha:PP_T (cal(E)_m)->^~PP_T^(r-1) $
  是 $T$ 上的射影丛同构, 称为一个*射影标架*. 两对数据同构, 是指曲线同构与射影标架相容.
]

#block(breakable: false)[
#proofsketch[
  命题中的嵌入给出 $cal(E)_m times.o cal(M) tilde.eq cal(O)_T^(plus.o r)$, 射影化便得到 $alpha$. 改变所选线丛同构只会乘以底上的单位, 射影化后不变.

  反过来, 给定 $alpha$, 将 @prop-relative-pluricanonical 的嵌入与它复合. 记 $p:PP_T (cal(E)_m)->T$. 线丛 $cal(N):=alpha^* cal(O)(1) times.o cal(O)(-1)$ 在每条射影空间纤维上平凡, 因而纤维上 $h^0=1$, 高阶上同调为零. 上同调与基变换说明 $cal(M):=p_* cal(N)$ 是线丛, 评价映射给出 $p^* cal(M) tilde.eq cal(N)$. 这就得到所需的底上扭曲; 推前后也得到完整线性系条件.

  两种构造互逆且与拉回相容. 而保持射影标架的曲线自同构在嵌入后必须为恒等, 所以这里确实得到一个集合值模函子.
]
]

=== 取商叠: 忘掉射影标架

以下简记
$ H:=H_(g,m), quad G:=op("PGL")_(r,ZZ) $
这里 $G$ 是射影线性群, 也就是 $GL_r slash bb(G)_m$ 的fppf层商. 它通过改变射影坐标左作用在 $H$ 上; 在带标架的描述中, 作用为
$ a dot (C slash T,alpha)=(C slash T,a compose alpha) $
这个作用保持光滑性, 典范极化及完整线性系条件, 因而确实限制到 $H$.

#definition(title:[多重典范参数的商叠])[
  按 @def-quotient-stack-general, $[H slash G](T)$ 的对象是
  $ (P->T, quad phi:P->H) $
  其中 $P->T$ 是右 $G_T$-挠子, 且
  $ phi(p dot a)=a^(-1) dot phi(p) $
  同构是与 $phi$ 相容的挠子等变同构, 拉回同时拉回这两项数据.
] <def-pluricanonical-quotient-stack>

一个挠子记录如何在覆盖上选坐标, 再在重叠上换坐标. 因而 $[H slash G](T)$ 不能写成轨道集合 $H(T) slash G(T)$: 后者只收录射影标架能在 $T$ 上整体选出的族, 还忘掉了同构箭头. 参见 @Stacks26[Tag 04UV].

#theorem(title:[曲线模叠的商叠表示])[
  有与任意基变换相容的典范叠等价
  $ cal(M)_g tilde.eq [H_(g,m) slash op("PGL")_(r,ZZ)] $
] <thm-smooth-curves-quotient>

#proof[
  *从曲线到商叠.* 给定 $C slash T$, 取射影标架层
  $ P_C:=underline("Isom")_T (PP_T (cal(E)_m),PP_T^(r-1)) $
  在 $cal(E)_m$ 平凡的开集上, 它就是 $G_T$. 规定右作用 $alpha dot a:=a^(-1) compose alpha$, 则 $P_C->T$ 是Zariski局部平凡的 $G_T$-挠子, 并由对 $T$ 仿射的概形表示. 在 $P_C$ 上有万有射影标架, 因而 @prop-pluricanonical-hilbert-locus 给出
  $ phi_C:P_C->H $
  改变标架正好改变射影坐标, 所以 $phi_C$ 满足上述等变公式. 曲线同构也自然诱导这两项数据的同构.

  *从商叠到曲线.* 给定 $(P,phi)$, 沿 $phi$ 拉回Hilbert万有曲线, 得到 $C_P->P$. 在 $P times_T P tilde.eq P times G$ 上, $phi$ 的等变性给出两次拉回之间的曲线同构, 群作用律保证余循环条件. 由 @prop-smooth-curves-descent, 它们下降为 $T$ 上的曲线 $C->T$. 挠子的相容同构也下降为曲线同构.

  这两个方向互逆: 从 $C$ 出发, 在 $P_C$ 上只是给原曲线加上标架, 下降后仍是 $C$. 从 $(P,phi)$ 出发, $P$ 上的标架给出等变态射 $P->P_C$; 两者都是 $G_T$-挠子, 这个态射局部为同构, 因而整体为同构, 并保持到 $H$ 的映射. 对同构也一样, 因为完整典范线性系使曲线同构诱导唯一的射影坐标变换. 所以得到的是群胚的等价, 且所有构造都与拉回相容.
]

=== 光滑图册与万有曲线

#corollary(title:[代数性与有限型])[
  忘掉标架的态射
  $ q:H_(g,m)->cal(M)_g $
  概形可表, 光滑且满射, 相对维数为 $r^2-1$. 而且有
  $ H times_(cal(M)_g) H tilde.eq G times_ZZ H $
  其两个投影分别对应 $(a,h)|->h$ 与 $(a,h)|->a dot h$. 因而 $cal(M)_g$ 是有限型的 $ZZ$-Artin叠.
] <cor-smooth-curves-atlas>

#proof[
  沿一个曲线族 $T->cal(M)_g$ 拉回 $q$, 得到的正是 $P_C->T$. 这是局部形如 $G times T->T$ 的仿射态射. 群 $G$ 光滑, 相对维数为 $r^2-1$: 可把它写成射影矩阵空间 $PP_ZZ^(r^2-1)$ 中行列式可逆的开子概形. 因而 $q$ 具有所述性质, 纤维积公式及代数性也由 @prop-quotient-stack-algebraicity 得到.

  由 @prop-pluricanonical-hilbert-locus, $H$ 是射影Hilbert概形的局部闭子概形, 所以对 $ZZ$ 有限型. 沿光滑满射 $q$ 检验局部有限型性与拟紧性, 就得到 $cal(M)_g$ 有限型.
]

#proposition(title:[模叠上的万有曲线])[
  记 $Z_H arrow.r.hook PP_H^(r-1)$ 为Hilbert万有曲线在 $H$ 上的限制. 射影坐标变换给出相容的 $G$-作用, 从而定义
  $ pi:cal(C)_g:=[Z_H slash G]->[H slash G] tilde.eq cal(M)_g $
  它概形可表, 光滑, 紧合且相对维数为 $1$. 对任意由 $C slash T$ 给出的分类态射 $f:T->cal(M)_g$, 有与基变换相容的同构
  $ C tilde.eq T times_(cal(M)_g) cal(C)_g $
] <prop-universal-smooth-curve>

#proof[
  坐标变换同时作用在 $PP^(r-1)$ 及 $H$ 上, 并把万有曲线送到自身. 按 @thm-smooth-curves-quotient 的下降构造, 沿 $f$ 拉回这个商正好得到 $C slash T$. 所以纤维积是概形, 且 $pi$ 的各项性质都化为曲线族定义中的性质.
]

#remark(title:[图册的维数与作用群])[
  $q$ 的相对维数 $r^2-1>0$, 因而这张图册是光滑的, 并非平展的. 要证明 $cal(M)_g$ 是DM叠, 还需检查对角态射.

  若把这里的 $G$ 直接换成通过射影化作用的 $GL_r$, 中心 $bb(G)_m$ 会固定所有嵌入, 并在商叠中成为每个对象的额外自同构. 所以这样的商分类了不同的模问题; 曲线的射影坐标变换群应取 $op("PGL")_r$.
]

=== 对角态射与Deligne--Mumford性质

#block(breakable: false)[
#proposition(title:[曲线之间的同构概形])[
  对 $C slash T,D slash T in cal(M)_g (T)$, 函子
  $ I:=underline("Isom")_T (C,D) $
  由对 $T$ 仿射, 有限表示的概形表示, 并且是 $cal(M)_g$ 的对角态射沿 $(C,D)$ 的拉回.
] <prop-smooth-curves-isom>
]

#proof[
  关于对角的解释就是 @prop-stack-diagonal-isom. 对可表性, 可在 $T$ 上局部选取两个曲线族的射影标架, 得到 $h_C,h_D:T->H$. 完整典范线性系把曲线同构唯一延拓为射影坐标变换, 因而
  $ I(T')={a in G(T') | a dot h_C|_(T')=h_D|_(T')} $
  这给出 $G_T$ 的闭子概形: 它是 $H$ 的对角沿 $a|->(a dot h_C,h_D)$ 的拉回. 由于 $H$ 对 $ZZ$ 分离且有限表示, 该闭嵌入也有限表示. 再用 $G_T$ 仿射且有限表示, 得到局部的断言. 这些表示同一个同构层的仿射概形在重叠上典范相容, 因而粘成所需的 $I$.
]

#lemma(title:[没有无穷小自同构])[
  设 $C slash k$ 是属 $g>=2$ 的光滑, 几何连通紧合曲线. 则
  $ op("Lie") underline(Aut)(C) tilde.eq H^0 (C,cal(T)_(C slash k))=0 $
] <lem-smooth-curve-no-infinitesimal-aut>

#proof[
  一个在模 $epsilon$ 后为恒等的 $k[epsilon] slash (epsilon^2)$ 上自同构, 在函数上形如
  $ a |-> a+epsilon D(a) $
  乘法相容恰好要求 $D$ 是 $k$-导子, 逆由 $-D$ 给出. 这样的整体导子就是切丛的整体截面, 这解释了第一个同构, 参见 @Stacks26[Tag 0E6G]. 而光滑曲线上
  $ cal(T)_(C slash k) tilde.eq omega_C^(-1), quad deg cal(T)_(C slash k)=2-2g<0 $
  负次数线丛没有非零整体截面, 所以它为零.
]

#corollary(title:[自同构群有限平展])[
  在上述假设下, $underline(Aut)(C)$ 是有限平展的 $k$-群概形.
] <cor-curve-aut-finite-etale>

#proof[
  由 @prop-smooth-curves-isom, 它是射影线性群中固定曲线的闭子群, 因而仿射且有限型. 扩张到代数闭域后, 群的平移把每一点的切空间移到单位元; @lem-smooth-curve-no-infinitesimal-aut 说明这些切空间全为零. 所以它零维且非分歧. 零维有限型仿射概形对域有限, 而域上的非分歧态射又平坦, 故有限平展. 这项性质可沿域扩张下降, 所以对原来的 $k$ 也成立.
]

#theorem(title:[光滑曲线模叠是DM叠])[
  对任意 $g>=2$, $cal(M)_g$ 是有限型的 $ZZ$-Deligne--Mumford叠.
] <thm-smooth-curves-dm>

#proof[
  由 @cor-smooth-curves-atlas, 它已是有限型Artin叠. 只需按 @prop-dm-diagonal 证明对角非分歧.

  取 @prop-smooth-curves-isom 中的 $I->T$. 它的每条几何纤维要么为空, 要么选定一个同构后就与相应曲线的自同构群同构, 因而由 @cor-curve-aut-finite-etale 知非分歧. 有限表示态射的非分歧性可在几何纤维上检查, 见 @Stacks26[Tag 05W2]. 所以 $I->T$ 非分歧, 从而对角非分歧, 得到DM性.
]

#remark(title:[正特征下仍要保留的区别])[
  上面的证明在任意特征下成立. 关键是自同构群的*切空间*为零, 仅数出有限多个几何自同构还不够: 非约化群概形也可能只有有限多个几何点.

  DM也不自动意味着tame. 例如特征 $p$ 上的常值群 $ZZ slash p ZZ$ 仍有限平展, 所以它的分类叠是DM叠, 却不是tame. 对有限惯性的DM叠, tame还要求几何稳定子的阶在剩余域中可逆, 等价地这些群线性约化. 参见 @AOV07[定理 3.2].
]

== 主丛模叠 $op("Bun")_G$

现在固定曲线, 让曲线上的主丛变化. 以下设 $X slash k$ 是光滑, 几何连通的射影曲线, $G slash k$ 是光滑仿射有限型群概形. 例如 $GL_n$, $bb(G)_m$ 和 $bb(G)_a$ 都在讨论范围内.

=== 模问题与例子

#definition(title:[$G$-主丛的模叠])[
  对 $k$-概形 $T$, 令 $X_T=X times_k T$. 定义群胚
  $ op("Bun")_G (X)(T):={X_T "上的右" G "-主丛及其等变同构"} $
  这里主丛指fppf局部平凡的 $G_(X_T)$-挠子 $P->X_T$, 同构固定 $X_T$. 沿 $T'->T$ 拉回主丛, 就定义了函子在态射上的作用. 曲线固定时简记为 $op("Bun")_G$.

  用分类叠的语言, 等价地有
  $ op("Bun")_G (X)(T) tilde.eq Map_k (X_T,B G) $
  所以 $B G$ 分类参数空间上的主丛, $op("Bun")_G (X)$ 则分类整条曲线上的主丛如何随参数变化.
] <def-bun-g>

这确实是fppf叠, 并满足fpqc下降: $G$ 仿射, 所以 $P->X_T$ 仿射; 仿射概形连同群作用和相容同构都可下降, 挠子条件又可在覆盖后检验. 主丛与分类叠的对应见 @Stacks26[Tag 0CQJ].

#example(title:[熟悉的模问题])[
  + $G=GL_n$: 主丛就是秩 $n$ 向量丛的标架丛, 因而 $op("Bun")_(GL_n)$ 分类 $X$ 上的秩 $n$ 向量丛.
  + $G=bb(G)_m$: 得到前面的Picard叠,
    $ op("Bun")_(bb(G)_m) (X) tilde.eq underline(Pic)_(X slash k) $
  + $G=op("SL")_n$: 分类秩 $n$ 向量丛 $cal(E)$, 连同一个指定的同构 $det cal(E) tilde.eq cal(O)$.
  + $G=bb(G)_a$: 分类加法群挠子. 在 $k$ 上, 其同构类组成 $H^1 (X,cal(O)_X)$, 局部粘合是把纤维坐标加上一个函数.
]

#remark(title:[关联丛与万有主丛])[
  一个表示 $rho:G->GL(V)$ 将 $P$ 送到关联向量丛 $P times^G V$: 把 $(p h,v)$ 与 $(p,rho(h)v)$ 识别即可. 这使主丛问题可以借助向量丛来研究.

  在 $X times_k op("Bun")_G$ 上始终有万有主丛 $cal(P)_"univ"$: 沿一个分类态射 $T->op("Bun")_G$ 拉回, 就得到它所分类的 $P->X_T$. 这与前面万有线丛的Yoneda解释相同.
]

=== 自同构就是规范变换

#proposition(title:[主丛的自同构群])[
  对 $P->X_T$, 用 $G$ 对自身的共轭作用构造群丛
  $ op("Ad")(P):=P times^G G $
  则对任意 $T'->T$, 有自然群同构
  $ underline(Aut)_T (P)(T') tilde.eq Gamma(X_(T'),op("Ad")(P_(T'))) $
  右边指群丛的截面群. 因而自同构是沿曲线相容地改变主丛标架, 也称*规范变换* (gauge transformation); 它不移动曲线上的点.
] <prop-bun-g-automorphisms>

#proof[
  在平凡化覆盖上选截面 $s_i$, 写 $s_j=s_i g_(i j)$. 一个等变自同构由 $s_i|->s_i a_i$ 决定, 重叠上的相容条件恰好是
  $ a_j=g_(i j)^(-1) a_i g_(i j) $
  这正是 $op("Ad")(P)$ 的截面粘合条件. 反过来, 满足此条件的 $a_i$ 给出相容局部自同构, 从而粘成全局自同构.
]

例如, 向量丛 $cal(E)$ 的规范变换是可逆的丛自同态, 所以
$ Aut_X (cal(E))=H^0 (X,underline("End")(cal(E)))^times $
若 $G$ 交换, 共轭作用平凡, 因而 $op("Ad")(P)=X_T times_k G$. 又因 $G$ 仿射且 $Gamma(X_(T'),cal(O))=Gamma(T',cal(O))$, 上述自同构群层就是 $G_T$. 特别地, 每条线丛有 $bb(G)_m$ 的伸缩自同构, 每个加法群挠子有 $bb(G)_a$ 的平移自同构.

记 $frak(g)=op("Lie")(G)$ 及 $op("ad")(P):=P times^G frak(g)$. 把规范变换线性化, 得到
$ op("Lie") underline(Aut)(P) tilde.eq H^0 (X,op("ad")(P)) $
这里 $P$ 是 $X$ 上的主丛. 对平凡主丛, 自同构群就是 $G$; 因而 $dim G>0$ 时, $op("Bun")_G$ 已有非零的无穷小自同构, 不会是DM叠.

=== Artin性

证明仍用前面的Hilbert与Quot构造. 先引用截面函子的一个标准结论.

#lemma(title:[截面函子的可表性])[
  若 $Y->X_T$ 有限表示且相对拟射影, 则函子
  $ T' |-> {s:X_(T')->Y_(T') | s "是截面"} $
  由局部有限表示的 $T$-概形表示. 若 $Y->X_T$ 仿射且有限表示, 则这个截面概形对 $T$ 仿射且有限表示.
] <lem-bun-section-scheme>

#proofsketch[
  把截面看成 $Y$ 中的图像, 便得到Hilbert概形中投影到 $X_T$ 为同构的开部分. 仿射情形还可用代数的有限生成元及关系, 把截面写成整体截面空间上的有限个方程. 详见 @Wan11[定理 3.1.1, 引理 3.1.4]; 整体截面的可表性也见 @Stacks26[Tag 08K6].
]

#theorem(title:[主丛模叠的代数性])[
  在本节假设下, $op("Bun")_G (X)$ 是局部有限表示的 $k$-Artin叠, 对角态射仿射且有限表示. 它还对 $k$ 光滑.

  一般不能把局部有限表示加强为有限型: 例如 $G=bb(G)_m$ 时, 线丛的次数可以任意大或小.
] <thm-bun-g-artin>

#proof[
  *先看对角.* 给定 $X_T$ 上的两个主丛 $P,Q$, 它们的局部等变同构组成 $X_T$ 上的仿射有限表示概形 $Y=underline("Isom")_(G,X_T) (P,Q)$; 在同时平凡化两者的覆盖 $U->X_T$ 上, 它形如 $G times_k U->U$. 整体同构就是 $Y->X_T$ 的截面. 由 @lem-bun-section-scheme, 其函子对 $T$ 仿射且有限表示, 这正是对角的断言.

  *先给向量丛造图册.* 固定 $X$ 上的极丰沛线丛 $cal(O)_X (1)$. 对秩 $n$ 向量丛的Hilbert多项式 $Phi$, 取整数 $m>=0$, 令 $r=Phi(m)>0$. 在 @thm-quot-representability 给出的Quot概形中取开子概形 $Q_(m,Phi)$, 参数化
  $ cal(O)_(X_T) (-m)^(plus.o r)->>cal(E) $
  其中 $cal(E)$ 局部自由且秩为 $n$, 纤维上的 $H^1 (cal(E)(m))=0$, 并且诱导同构
  $ cal(O)_T^(plus.o r)->^~(p_T)_* cal(E)(m), quad p_T:X_T->T $
  这些是开条件, 后一个同构条件由上同调与基变换及行列式检验. 忘掉商映射, 就是忘掉 $(p_T)_* cal(E)(m)$ 的一组基. 因而 $Q_(m,Phi)$ 到相应开子叠的映射是 $GL_r$-挠子, 光滑且满射. Serre消失保证每个向量丛族在参数局部都能如此表示, 所以所有 $Q_(m,Phi)$ 的不交并给出 $op("Bun")_(GL_n)$ 的光滑图册.

  #block(breakable: false)[
  *再把结构群约化到 $G$.* 选一个闭嵌入 $G arrow.r.hook GL_n$. 给定向量丛 $cal(E)$, 记其标架丛为 $F$. 给 $F$ 一个 $G$-约化, 等价于给商丛
  $ F slash G->X_T $
  一个截面: 拉回 $F->F slash G$ 就恢复这个 $G$-主丛. 齐次空间 $GL_n slash G$ 带有等变丰沛线丛, 所以 $F slash G->X_T$ 有限表示且相对拟射影, 见 @Wan11[引理 2.4.1]. 由 @lem-bun-section-scheme, 忘掉约化的态射
  $ op("Bun")_G->op("Bun")_(GL_n) $
  概形可表且局部有限表示. 沿它拉回刚才的图册, 得到概形
  $ R_(m,Phi):=op("Bun")_G times_(op("Bun")_(GL_n)) Q_(m,Phi) $
  由基变换, 所有 $R_(m,Phi)->op("Bun")_G$ 联合构成光滑满射. 这就证明了Artin性, 图册对 $k$ 局部有限表示也给出相同的有限性结论.
  ]

  最后补充光滑性. 对仿射参数的平方零增厚, 利用 $G$ 光滑, 可在平展覆盖上提升主丛的转移函数. 三重交上的误差给出 $op("ad")(P)$ 张量增厚理想的 $H^2$ 障碍. 曲线族在仿射底上的这个 $H^2$ 为零, 所以提升存在. 结合局部有限表示性, 得到光滑性; 详见 @Wan11[第 6 节].
]
