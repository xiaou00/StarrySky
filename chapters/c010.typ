#import "../template.typ":*

#show: doc => conf(easy: true, doc,)

= $K_2$ 群 / The Group $K_2$ <chap-k2>

在#chapter-ref(<chap-k1>)中, 我们用可逆矩阵定义了 $K_1 (R)$, 并证明
$ K_1 (R)=GL(R) slash E(R) $
这里 $E(R)$ 由初等矩阵生成. 现在把这些矩阵换成抽象生成元, 只规定它们的基本关系, 得到 Steinberg 群. 它仍然映满 $E(R)$, 而这个映射的核就是 $K_2 (R)$.

本章先说明这个核为什么是 Abel 群, 再用泛中心扩张解释它的意义. 转向域后, Matsumoto 定理把 $K_2$ 写成单位符号, 留数和范数随之成为计算工具. 最后把符号推广到任意次数, 得到 Milnor $K$ 群, 并介绍它与微分形式, Galois 上同调和二次型的联系.

主要参考 @Wei13[III, §5--§7]. Matsumoto 呈示, Hilbert 90 与比较定理等深结果注明出处后引用, 各项构造和主要推论则给出证明.

== $K_2$ 的定义与基本性质 <sec-k2-steinberg>

以下 $R$ 是含幺结合环. 回顾 @def-elementary-matrix-groups, $e_(i j) (r)=I+r E_(i j)$, 而 $E_n (R)$ 是这些矩阵生成的子群.

#definition(title: [Steinberg 群])[
  对 $n>=3$, 定义 $"St"_n (R)$ 为由符号 $x_(i j) (r)$ 生成的群, 其中 $i!=j$, $r in R$, 关系为
  $ x_(i j) (r)x_(i j) (s)&=x_(i j) (r+s), \
    [x_(i j) (r),x_(k l) (s)]&=1 quad (j!=k, i!=l), \
    [x_(i j) (r),x_(j k) (s)]&=x_(i k) (r s) quad (i,j,k "互异") $
  沿保持下标的同态定义*稳定 Steinberg 群*
  $ "St"(R):=varinjlim(n>=3) "St"_n (R) $
  初等矩阵满足这些关系, 因而有自然满射
  $ phi:"St"(R)->E(R), quad x_(i j) (r) mapsto e_(i j) (r) $
] <def-steinberg-group>

这里用余极限定义 $"St"(R)$, 不预先要求 $"St"_n (R)->"St"_(n+1) (R)$ 单射. 每个元素都能用有限多个生成元写出, 所以证明中总能另选没有出现过的下标. 此外, 第一条关系给出 $x_(i j) (0)=1$ 与 $x_(i j) (r)^(-1)=x_(i j) (-r)$.

#definition(title: [环的第二 $K$ 群])[
  定义
  $ K_2 (R):=ker (phi:"St"(R)->E(R)) $
  因而有自然正合列
  $ 1->K_2 (R)->"St"(R)->GL(R)->K_1 (R)->1 $
] <def-ring-k2>

$K_2$ 的元素由一串 $x_(i j) (r)$ 表示, 要求对应初等矩阵的乘积为单位矩阵. 两串表达式在能用 Steinberg 关系互相变换时代表同一元素. 因而 $K_2$ 保留了这类初等变换序列在矩阵乘积之外的信息.

#lemma(title: [Steinberg 群是完美群])[
  $n>=3$ 时 $"St"_n (R)$ 是完美群, 稳定群 $"St"(R)$ 也是完美群.
] <lem-steinberg-perfect>

#proof[
  对每个生成元另选 $k!=i,j$, 就有
  $ x_(i j) (r)=[x_(i k) (r),x_(k j) (1)] $
  所以全部生成元都属于交换子子群.
]

#theorem(title: [$K_2$ 是 Steinberg 群的中心])[
  对任意含幺环 $R$, 有
  $ K_2 (R)=Z("St"(R)) $
  特别地, $K_2 (R)$ 是 Abel 群.
] <thm-k2-central>

#proof[
  先看 $E(R)$ 的中心. 若 $g$ 支持在左上角的 $m times m$ 块, 选 $N>m$. 与每个 $e_(i N) (1)$ 交换意味着 $g$ 固定第 $i$ 个标准基向量. 因而 $g=I$, 所以 $Z(E(R))=1$. 满射 $phi$ 将中心送到中心, 于是 $Z("St"(R)) subset.eq K_2 (R)$.

  反过来, 设 $y in K_2 (R)$, 选 $N$ 大于表示 $y$ 的全部下标. 在 $"St"(R)$ 中考虑
  $ U_N:=⟨x_(i N) (r) | i<N, r in R⟩ $
  同一列的这些生成元两两交换, 第一条关系合并相同下标. 比较它们在矩阵群中的像可知
  $ U_N tilde.eq (R^(N-1),+), quad phi|_(U_N) "是单射" $
  前 $N-1$ 个下标上的生成元正规化 $U_N$: 共轭公式只会再乘一个同列生成元. 因而 $[y,x_(i N) (r)] in U_N$. 这个交换子在矩阵群中为 $1$, 由单射性, 它在 $"St"(R)$ 中也为 $1$.

  对同一行的群 $⟨x_(N j) (r)⟩$ 重复论证, 得到 $y$ 也与这些生成元交换. 现在用
  $ x_(i j) (r)=[x_(i N) (r),x_(N j) (1)] $
  得到 $y$ 与任意 $x_(i j) (r)$ 交换. 对给定的 $i,j$, 将 $N$ 取得更大即可. 所以 $y$ 属于中心.
]

从现在起将 $K_2 (R)$ 写成加法群. 在 $"St"(R)$ 内部计算时仍用乘法, 因而一个核元素等于 $1$ 就表示其 $K_2$ 类为 $0$.

#proposition(title: [函子性与有限乘积])[
  环同态 $f:R->S$ 诱导 $K_2 (f):K_2 (R)->K_2 (S)$. 此外,
  $ K_2 (R times S) tilde.eq K_2 (R) plus.o K_2 (S) $
  $K_2$ 也保持滤过余极限.
] <prop-k2-functor-products>

#proof[
  将 $x_(i j) (r)$ 送到 $x_(i j) (f(r))$, 保持所有关系, 并与到初等矩阵群的映射交换, 所以限制到核给出函子性.

  对乘积环, 每个生成元分解为 $x_(i j) (r,0)x_(i j) (0,s)$. 两类生成元彼此交换. 除了相反根的位置, 这直接来自关系; 对相反根, 把其中一个生成元写成经由新下标的交换子, 再用两系数理想的乘积为零即可. 因而 $"St"(R times S) tilde.eq "St"(R) times "St"(S)$, 对 $E$ 也成立, 取核得到结论.

  最后, 一个群元素, 一个矩阵等式或一次由关系得到的等式都只涉及有限多个系数. 在滤过系统中, 它们会在某一共同阶段出现或成立. 所以构造 $"St"$, $E$ 及其核均与滤过余极限相容.
]

=== 泛中心扩张

刚才证明了 $K_2$ 是中心核. 下面进一步说明, $"St"(R)->E(R)$ 在所有中心扩张中满足一个泛性质. 为此先回顾一般群的情形.

#definition(title: [泛中心扩张])[
  群的正合列 $1->A->U->^q G->1$ 称为*中心扩张*, 如果 $A subset.eq Z(U)$.

  如果对每个中心扩张 $V->G$, 都存在唯一同态 $U->V$ 与到 $G$ 的映射交换, 就称 $q$ 为 $G$ 的*泛中心扩张*.
] <def-universal-central-extension>

#lemma(title: [中心扩张的两个判据])[
  + 若 $U$ 完美, 则到一个中心扩张 $V->G$ 的两个同态只要在 $G$ 中相同, 就彼此相同.
  + 中心扩张 $U->G$ 是泛的, 当且仅当 $U$ 完美且 $U$ 的每个中心扩张都分裂.
] <lem-universal-central-criterion>

#proof[
  第一条中, 两个提升在每个元素上的差都落在中心核. 因而它们在交换子上的值相同. 完美性保证交换子生成 $U$.

  对第二条的充分性, 将 $V->G$ 沿 $U->G$ 拉回, 得到 $U$ 的中心扩张. 取截面并投影到 $V$ 给出所需提升, 第一条保证唯一.

  再证必要性. 泛性质首先强迫 $U$ 完美: 到 $U^"ab" times G$ 的两个映射 $u mapsto (0,q(u))$ 与 $u mapsto ([u],q(u))$ 必须相同.

  给定 $U$ 的中心扩张 $V->U$, 完美性保证 $[V,V]->U$ 满射. 若 $v in V$ 在 $G$ 中的像为 $1$, 则 $[v,w]$ 对任意 $w in V$ 都落在 $ker(V->U)$, 因而是中心元素. 于是 $v$ 与 $[V,V]$ 交换. 所以 $[V,V]->G$ 是中心扩张. 泛性质给出 $U->[V,V]$, 其到 $U$ 的复合由第一条必为恒等. 这就给出了原扩张的截面.
]

#theorem(title: [自由群模型与 Hopf 公式])[
  群 $G$ 存在泛中心扩张, 当且仅当 $G$ 完美. 若 $G=F slash N$ 是自由群呈示且 $G$ 完美, 则其泛中心扩张为
  $ [F,F] slash [F,N] -> G $
  核由 Hopf 公式识别为
  $ H_2 (G;ZZ) tilde.eq (N inter [F,F]) slash [F,N] $
  这里 $H_2$ 是群同调的第二群.
] <thm-hopf-universal-central>

#proof[
  完美性给出 $F=N[F,F]$. 在 $F slash [F,N]$ 中, $N$ 的像是中心, 所以 $[F,F] slash [F,N]$ 映满 $G$, 且核在中心. 同一个等式还说明这个源群完美: 计算交换子时可以删去来自 $N$ 的中心因子.

  给定中心扩张 $V->G$, 自由群 $F$ 的生成元可逐一提升到 $V$, 得到 $F->V$. $N$ 映到中心, 因而 $[F,N]$ 映为 $1$. 限制到 $[F,F]$ 就得到要求的同态; 唯一性来自完美性. 反过来, 泛中心扩张的源群完美, 其商群 $G$ 也完美.

  核的表达式直接由商群得到. 将这个表达式识别为群同调 $H_2$ 是 Hopf 公式, 见 @Wei13[III, §5 的泛中心扩张讨论]. 上面的泛性质证明只用群的呈示, 不依赖同调语言.
]

#theorem(title: [Kervaire–Steinberg 定理])[
  $"St"(R)->E(R)$ 是泛中心扩张. 因而自然地
  $ K_2 (R) tilde.eq H_2 (E(R);ZZ) $
] <thm-k2-universal-central>

#proof[
  已知 $"St"(R)$ 完美, 核在中心. 按 @lem-universal-central-criterion, 只需证明每个中心扩张 $pi:Y->"St"(R)$ 分裂.

  先证明交换根的任意提升仍然交换. 设 $y,z$ 分别提升 $x_(i j) (r),x_(k l) (s)$, 且 $j!=k$, $i!=l$. 选不在这四个下标中的 $t$, 将 $x_(i j) (r)$ 写成 $[x_(i t) (1),x_(t j) (r)]$. 两个因子的任意提升与 $z$ 的交换子都在中心. 所以 $z$ 与这两个提升的交换子交换, 也就与 $y$ 交换.

  对两两不同的 $i,j,k,l$, 取 $u,v,w$ 分别提升 $x_(i j) (1),x_(j k) (a),x_(k l) (b)$. 刚才的结论给出 $[u,w]=1$, 且这些根所产生的交换子彼此交换. 展开交换子, 或使用 Hall–Witt 恒等式, 得到
  $ [[u,v],w]=[u,[v,w]] $
  这里所有换序都由前一步的交换根结论保证. 取 $a=1$, 可知
  $ y_(i l) (r):=[tilde(x)_(i j) (1),tilde(x)_(j l) (r)] $
  与中间下标 $j$ 无关. 中心核也保证它与两次提升的选择无关.

  这些 $y_(i j) (r)$ 满足 Steinberg 关系. 交换根的关系已经证明; 上面的三重交换子恒等式给出
  $ [y_(i j) (r),y_(j k) (s)]=y_(i k) (r s) $
  最后, 固定一个中间下标, 将 $x_(k j) (r+s)$ 的提升取成两个提升的乘积. 利用
  $ [a,b c]=[a,b] b[a,c]b^(-1) $
  以及 $[a,c]$ 与 $b$ 对应交换根, 得到
  $ y_(i j) (r+s)=y_(i j) (r)y_(i j) (s) $
  因而 $x_(i j) (r) mapsto y_(i j) (r)$ 定义同态 $"St"(R)->Y$, 显然是 $pi$ 的截面. 最后应用 @thm-hopf-universal-central 即得同调表达式. 参见 @Wei13[III, 定理 5.5].
]

至此, $K_2$ 有了两种相容的描述: 它既是 Steinberg 群到初等矩阵群的核, 也是完美群 $E(R)$ 的二次同调. 后一种描述适合用来证明 Morita 不变性与构造转移.

=== Morita 不变性与转移

沿用#chapter-ref(<chap-k1>)的投射模范畴 $cat("Proj") (R)$ 与平移范畴 $t #h(0pt) cat("Proj") (R)$. 我们仍用补直和项来稳定化自同构, 但这次需要二次同调. 为消去补模选择造成的共轭, 对群 $G$ 记
$ H'_2 (G):=H_2 ([G,G];ZZ)_G $
下标 $G$ 表示取共轭作用的余不变量, 即再商去所有 $g z-z$. 这样内自同构在 $H'_2$ 上就成为恒等.

#proposition(title: [Bass 的范畴表达式])[
  存在自然同构
  $ K_2 (R) tilde.eq varinjlim(P in t #h(0pt) cat("Proj") (R)) H'_2 (Aut_R (P)) $
  因而 $K_2 (R)$ 只依赖 $cat("Proj") (R)$ 的加性范畴结构.
] <prop-k2-bass-category>

#proof[
  直和 $P mapsto P plus.o Q$ 给出自同构群之间的映射. 改变所选同构只会造成共轭, 所以取 $H'_2$ 后成为良定义的函子. 自由模在平移范畴中共尾, 故右边等于
  $ varinjlim(n) H'_2 (GL_n (R)) tilde.eq H'_2 (GL(R)) $
  群同调的链只用有限多个群元素, 所以它与滤过余极限相容.

  $GL(R)$ 在 $H_2 (E(R);ZZ)$ 上的共轭作用是平凡的. 事实上, 对一个给定的同调类及给定的 $g$, 先让代表链与 $g$ 都处于有限矩阵块中. 在更大的块中, $op("diag") (g,g^(-1)) in E(R)$ 与 $g$ 对这条链有相同的共轭作用. 前者是 $E(R)$ 的内自同构, 所以在同调上作用平凡. 因而
  $ H'_2 (GL(R))=H_2 (E(R);ZZ)=K_2 (R) $
  见 @Wei13[III, 命题 5.6].
]

#corollary(title: [加性函子与 Morita 不变性])[
  加性函子 $T:cat("Proj") (S)->cat("Proj") (R)$ 诱导 $K_2 (T):K_2 (S)->K_2 (R)$. 自然同构的函子给出相同映射, 且
  $ K_2 (T_1 plus.o T_2)=K_2 (T_1)+K_2 (T_2) $
  特别地, Morita 等价的环有同构的 $K_2$, 并且
  $ K_2 (M_n (R)) tilde.eq K_2 (R) $
] <cor-k2-morita>

#proof[
  对自同构群施加 $T$, 再对 @prop-k2-bass-category 的余极限取函子性即可. 加法来自块直和. 在稳定完美群上, Künneth 公式给出
  $ H_2 (E times E;ZZ) tilde.eq H_2 (E;ZZ) plus.o H_2 (E;ZZ) $
  因为 $H_1 (E;ZZ)=0$, 没有交叉项. 块直和在两个因子上的限制都是稳定化, 因而诱导求和. 加性等价与其逆函子随即给出互逆同构.
]

这里的矩阵环同构由 Morita 等价给出. 标量同态 $R->M_n (R)$, $r mapsto r I_n$, 在这个同构下诱导的是乘以 $n$: 对应的投射模函子是 $P mapsto P^n$.

#corollary(title: [有限转移与投影公式])[
  设 $f:R->S$, 且 $S$ 作为右 $R$-模有限生成投射. 忘却函子给出
  $ f_*:K_2 (S)->K_2 (R) $
  若 $R$ 交换, 张量函子使 $K_2 (R)$ 成为 $K_0 (R)$-模. 若还要求 $f(R) subset.eq Z(S)$, 则
  $ f_* f^*(x)=[S] dot x $
  特别地, 若 $F subset.eq L$ 是 $d$ 次域扩张, 则范数 $N_(L slash F):=f_*$ 满足
  $ N_(L slash F) f^*=d dot id $
] <cor-k2-transfer>

#proof[
  有限生成投射 $S$-模是某个 $S^n$ 的直和项, 限制标量后仍为有限生成投射 $R$-模. 因而限制标量是加性函子. 对交换 $R$, 将投射模 $P$ 送到函子 $Q mapsto Q times.o_R P$, 加性保证这一作用通过 $K_0 (R)$. 复合 $f_* f^*$ 对应 $Q mapsto Q times.o_R S$, 正好是乘以 $[S]$. 域上的类 $[L]$ 等于维数 $d$.
]

同样, 若存在加性自函子 $T$ 满足 $id plus.o T tilde.eq T$, 则 $id+K_2 (T)=K_2 (T)$, 从而 $K_2 (R)=0$. 这就是 Eilenberg 消去法在 $K_2$ 上的应用.

=== 相对群与边界映射 <sec-relative-k2>

下面将#chapter-ref(<chap-k1>)的相对正合列向左延长. 商环上的一条初等关系, 提升到 $R$ 后可能不再乘成单位矩阵, 但其乘积模 $I$ 仍为单位矩阵. 这个乘积给出相对 $K_1$ 的类, 从而产生边界映射 $K_2 (R slash I)->K_1 (R,I)$.

#definition(title: [相对 Steinberg 群与相对 $K_2$])[
  设 $I$ 是 $R$ 的双边理想. 在 Abel 群 $D=R plus.o I$ 上定义乘法
  $ (r,u) (s,v)=(r s,r v+u s+u v) $
  两个环同态为 $p(r,u)=r$ 与 $a(r,u)=r+u$. 记
  $ "St"' (R,I):=ker ("St"(D)->^("St"(p)) "St"(R)) $
  它由 $x_(i j) (0,u)$, $u in I$, 正规生成. 在 $"St"(D)$ 中取交叉交换子
  $ [x_(i j) (0,u),x_(k l) (v,-v)] quad (u,v in I) $
  的正规闭包 $C$, 定义
  $ "St"(R,I):="St"' (R,I) slash C, quad
    K_2 (R,I):=ker ("St"(R,I)->E(R,I)) $
  最后的满射由 $a$ 诱导, $E(R,I)$ 见 @def-relative-k1.
] <def-relative-k2>

这一定义中, $C$ 确实包含于 $"St"' (R,I)$, 而且被 $"St"(a)$ 消去. 矩阵层面, 两个理想 $0 plus.o I$ 与 ${ (v,-v) | v in I }$ 彼此相乘为零, 所以上述交叉交换子映为单位矩阵. 这个商将两种提升的相容性加入关系. 一般不能把相对 $K_2$ 直接定义为 $ker (K_2 (R)->K_2 (R slash I))$.

#theorem(title: [从 $K_2$ 接到相对 $K_1$])[
  存在自然正合列
  $ K_2 (R,I)->K_2 (R)->K_2 (R slash I)->^partial K_1 (R,I) \
    ->K_1 (R)->K_1 (R slash I)->K_0 (R,I) $
  并继续接上 @thm-relative-k1-k0-sequence.
] <thm-relative-k2-sequence>

#proof[
  商映射在 Steinberg 群上满射, 因为每个生成元的系数都可提升. 从呈示可知
  $ "St"(R,I)->"St"(R)->"St"(R slash I)->1 $
  正合: 令所有来自 $I$ 的生成元为 $1$, 就得到商环的呈示.

  给定 $z in K_2 (R slash I)$, 选提升 $tilde(z) in "St"(R)$. 矩阵 $phi(tilde(z))$ 模 $I$ 为单位矩阵, 定义
  $ partial(z):=[phi(tilde(z))] in K_1 (R,I) $
  两个提升之差来自 $"St"(R,I)$, 其矩阵像属于 $E(R,I)$, 所以此类与选择无关. 乘积的提升可取提升的乘积, 因而它是群同态.

  若 $partial(z)=0$, 可乘上一个来自 $"St"(R,I)$ 的元素, 把 $tilde(z)$ 的矩阵像消去. 修改后的提升就在 $K_2 (R)$ 中. 这证明在 $K_2 (R slash I)$ 处正合.

  若 $K_1 (R,I)$ 中的类在 $K_1 (R)$ 中为零, 取代表 $g in GL(R,I)$, 则 $g in E(R)$. 将它提升到 $"St"(R)$, 再模 $I$, 得到 $K_2 (R slash I)$ 的元素, 边界正是原类. 这证明下一处正合.

  最后, $z in K_2 (R)$ 若模 $I$ 为 $1$, 它来自某个 $w in "St"(R,I)$. 因为 $z$ 的矩阵像为 $1$, $w$ 属于 $K_2 (R,I)$. 余下部分已在#chapter-ref(<chap-k1>)证明. 参见 @Wei13[III, 定义 5.7 与定理 5.7.1].
]

#theorem(title: [双满射方块的 Mayer–Vietoris 列])[
  设 $I,J$ 是 $R$ 的双边理想且 $I inter J=0$. 对拉回方块
  $ R tilde.eq (R slash I) times_(R slash (I+J)) (R slash J) $
  有正合列
  $ &K_2 (R)->K_2 (R slash I) plus.o K_2 (R slash J)->K_2 (R slash (I+J)) \
    &quad ->K_1 (R)->K_1 (R slash I) plus.o K_1 (R slash J) \
    &quad ->K_1 (R slash (I+J))->K_0 (R)->dots $
  从直和出发的映射取差.
] <thm-k2-milnor-two-surjections>

#proof[
  记 $R'=R slash J$, $Q=R slash (I+J)$. 因为 $I inter J=0$, 可将 $I$ 同时看作 $R'$ 的理想. 相对一般线性群由矩阵 $1+A$, $A$ 的系数属于 $I$, 组成, 所以 $GL(R,I)->GL(R',I)$ 是同构. 商映射在初等矩阵上满射, 因而这个同构也识别两个相对初等子群. 所以
  $ K_1 (R,I) tilde.eq K_1 (R',I) $
  相对 Steinberg 群的系数都能沿 $R->R'$ 提升, 从其呈示得到 $"St"(R,I)->"St"(R',I)$ 满射. 因为相对初等群已被识别, 对核也有满射
  $ K_2 (R,I)->K_2 (R',I) $

  将 $(R,I)$ 与 $(R',I)$ 的两条 @thm-relative-k2-sequence 叠在一起. 对 $z in K_2 (Q)$, 先取下行边界到 $K_1 (R',I)$, 通过上述同构返回 $K_1 (R,I)$, 再映到 $K_1 (R)$, 就定义了方块的边界.

  若这个边界为零, 上行正合性使其相对类来自 $K_2 (R slash I)$. 从 $z$ 减去这个元素在 $Q$ 上的像后, 下行边界变为零, 所以差来自 $K_2 (R')$. 这证明在 $K_2 (Q)$ 处正合.

  若 $a in K_2 (R slash I)$ 与 $b in K_2 (R')$ 在 $Q$ 上相同, 相对 $K_1$ 的同构说明 $a$ 的上行边界为零. 先提升 $a$ 到 $c in K_2 (R)$. 此时 $c$ 在 $R'$ 上的像与 $b$ 之差来自 $K_2 (R',I)$. 利用相对 $K_2$ 的满射将这个差提升回来并修正 $c$, 就得到同时提升 $a,b$ 的元素. 这证明前一处正合. 余下部分是#chapter-ref(<chap-k1>)的 Milnor 拼接列. 参见 @Wei13[III, 定理 5.8 与习题 5.10].
]

这里两条到共同商环的映射都满射. 这个假设保证证明中的相对群可以比较; #chapter-ref(<chap-k1>)的一般 Milnor 方块并不自动满足同样的高阶正合性.

== Steinberg 符号与计算 <sec-k2-symbols>

Steinberg 群适合定义 $K_2$, 实际计算时则希望有更短的代表. 两个交换矩阵的提升未必交换, 它们的交换子恰好落在 $K_2$ 中. 这就给出了符号.

#definition(title: [交换矩阵的符号])[
  若 $A,B in E(R)$ 交换, 选提升 $a,b in "St"(R)$, 定义
  $ A star B:=[a,b] in K_2 (R) $
] <def-k2-commuting-symbol>

此交换子确实在核中. 改变提升只会乘上中心元素, 所以结果不变. 交换子的恒等式还给出
$ A star B=-(B star A), quad (A_1 A_2) star B=A_1 star B+A_2 star B $
第二式要求 $A_1,A_2$ 都与 $B$ 交换. 同时共轭两个矩阵也不改变符号: 对 $P in GL(R)$, 先补块, 再用 $op("diag") (P,P^(-1)) in E(R)$ 的提升作共轭即可.

#definition(title: [Steinberg 符号])[
  对 $R$ 中两个交换的单位 $r,s$, 定义
  $ {r,s}:=op("diag") (r,r^(-1),1) star op("diag") (s,1,s^(-1)) $
  两个对角矩阵都在 $E(R)$ 中. 更具体地, 令
  $ w_(i j) (r)&:=x_(i j) (r)x_(j i) (-r^(-1))x_(i j) (r), \
    h_(i j) (r)&:=w_(i j) (r)w_(i j) (-1) $
  则 $phi(h_(i j) (r))$ 在第 $i,j$ 个对角位置分别为 $r,r^(-1)$, 其余为 $1$, 而
  $ {r,s}=[h_(1 2) (r),h_(1 3) (s)] $
] <def-steinberg-symbol>

这些符号对环同态自然. 对两两交换的单位, 它们满足双线性与反对称性
$ {r s,t}={r,t}+{s,t}, quad {r,s t}={r,s}+{r,t}, quad {r,s}=-{s,r} $
反对称性还用到同时交换第 $2,3$ 个坐标: 它把定义中的两个对角块互换.

#proposition(title: [Steinberg 关系])[
  若 $r$ 与 $1-r$ 都可逆, 则
  $ {r,1-r}=0, quad {r,-r}=0 $
  特别地, 对域 $F$ 的所有 $a,b in F^times$, 有
  $ {a,-a}=0, quad {a,a}={a,-1}={-1,a}, quad 2{a,-1}=0 $
] <prop-steinberg-symbol-relations>

#proof[
  先记录 Steinberg 关系的一个计算结果. 对交换单位 $r,s$, 有
  $ {r,s}=h_(1 2) (r s)h_(1 2) (s)^(-1)h_(1 2) (r)^(-1) $
  右边作为 $"St"(R)$ 中的乘积解释. 计算时将 $x_(1 2) (a)$ 写成 $[x_(1 3) (a),x_(3 2) (1)]$, 用三下标关系移过 $w$ 的三个因子, 再合并同根项; 得到的共轭公式为
  $ w_(1 2) (r)x_(2 1) (u)w_(1 2) (r)^(-1)=x_(1 2) (-r u r) $
  以及交换 $1,2$ 下标后的公式. 将它们代入两个 $h$ 的乘积, 就得到上式. 这些呈示计算也见 @Wei13[III, 习题 5.8–5.9].

  现在令 $s=1-r$. 利用 $w_(1 2) (-1)=x_(2 1) (1)x_(1 2) (-1)x_(2 1) (1)$, 上述共轭公式给出
  $ w_(1 2) (r)w_(1 2) (-1)w_(1 2) (s)
    &=x_(1 2) (-r^2)w_(1 2) (r)x_(1 2) (-1)w_(1 2) (s)x_(1 2) (-s^2) \
    &=x_(1 2) (r s)x_(2 1) (-r^(-1))x_(2 1) (-s^(-1))x_(1 2) (r s) \
    &=w_(1 2) (r s) $
  这里用了 $r+s=1$ 与 $r^(-1)+s^(-1)=(r s)^(-1)$. 右乘 $w_(1 2) (-1)$, 得到 $h(r)h(s)=h(r s)$, 所以 ${r,1-r}=0$.

  接着 $-r=(1-r) slash (1-r^(-1))$, 故双线性与两次 Steinberg 关系给出 ${r,-r}=0$. 域中只剩 $r=1$ 的情况, 它由 ${1,b}=0$ 得到. 展开 ${a,-a}=0$ 得到 ${a,a}=-{a,-1}$, 而 $2{a,-1}={a,1}=0$, 因而负号可以去掉.
]

=== Matsumoto 呈示

#theorem(title: [Matsumoto 定理])[
  对域 $F$, 映射 $a times.o b mapsto {a,b}$ 给出自然同构
  $ K_2 (F) tilde.eq (F^times times.o_ZZ F^times) slash
    ⟨a times.o (1-a) | a in F backslash {0,1}⟩ $
  换言之, $K_2 (F)$ 由 ${a,b}$ 生成, 全部关系由双线性和 ${a,1-a}=0$ 生成.
] <thm-matsumoto>

上面已经构造了从右边到 $K_2 (F)$ 的自然同态. Matsumoto 定理进一步保证它满射且没有额外关系, 所以域上的计算可以完全转为符号运算. 这里引用 @Wei13[III, 定理 6.1]; 完整证明见该处转引的 Milnor _Introduction to Algebraic K-Theory_, §12.

因此, 要从 $K_2 (F)$ 构造到 Abel 群 $A$ 的同态, 只需给出对两变量双线性的函数 $c:F^times times F^times->A$, 再检验 $c(a,1-a)=0$. 这样的函数通常也称 Steinberg 符号. 特别地, 反对称性实际上可以由呈示推出: 先推出 ${a,-a}=0$, 再展开 ${a b,-a b}=0$, 消去两项对角关系即可.

#example(title: [有限域的 $K_2$])[
  对有限域 $bb(F)_q$, 有
  $ K_2 (bb(F)_q)=0 $

  取乘法群生成元 $g$. 双线性说明整个群由 $c={g,g}$ 生成. 若 $q$ 为偶数, 则 $-1=1$, 所以 $c={g,-1}=0$.

  若 $q$ 为奇数, 则 $2c=0$. 在 $bb(F)_q backslash {0,1}$ 中有 $(q-1) slash 2$ 个非平方元, 但只有 $(q-3) slash 2$ 个平方元. 因而存在 $u$, 使 $u$ 与 $1-u$ 都不是平方元. 写 $u=g^a$, $1-u=g^b$, 则 $a,b$ 都是奇数. 于是
  $ 0={u,1-u}=a b c=c $
  因而所有符号都为零.
] <ex-k2-finite-field>

#example(title: [实数中的符号])[
  定义 $epsilon(a,b) in ZZ slash 2$ 为 $1$, 当且仅当 $a<0$ 且 $b<0$. 符号的乘法规律说明 $epsilon$ 双线性, 而 $a$ 与 $1-a$ 不可能同时为负. 所以它诱导
  $ epsilon:K_2 (RR)->ZZ slash 2, quad {-1,-1} mapsto 1 $
  因为 $2{-1,-1}=0$, 这给出一个直和项 $ZZ slash 2$. 一个回到单位矩阵的初等变换序列, 在 $K_2$ 中确实可能非零.
] <ex-k2-real-sign>

#example(title: [整数环与四次旋转])[
  在 $"St"(ZZ)$ 中取
  $ w=x_(1 2) (1)x_(2 1) (-1)x_(1 2) (1), quad
    phi(w)=mat(0,1;-1,0) $
  所以 $phi(w)^4=I$, $w^4$ 给出 $K_2 (ZZ)$ 的元素. Steinberg 符号的计算将它识别为 ${-1,-1}$. 经典计算为
  $ K_2 (ZZ) tilde.eq ZZ slash 2 $
  生成元就是这个类, 见 @Wei13[III, 例 5.2.2]. 上界的证明使用整数上的 Euclidean 消元, 这里引用该计算; 非零性已经可由 $ZZ->RR$ 和#link(<ex-k2-real-sign>)[实数符号的例子]检验.

  矩阵 $phi(w)$ 是平面上的四分之一圈旋转. 四次旋转回到同一矩阵, 而抽象初等关系仍能记录这一次完整绕行.
] <ex-k2-integers>

多项式环还满足同伦不变性 $K_2 (F[t]) tilde.eq K_2 (F)$, 见 @Wei13[III, 例 5.2.3]. 更一般地, 对交换正则 Noetherian 环 $R$, 有 $K_2 (R[t]) tilde.eq K_2 (R)$. 这延续了#link(<sec-ki-regular-rings>)[$K_0,K_1$ 的正则性结论]; 其高阶形式将在#chapter-ref(<chap-higher-k-theory>)统一陈述.

=== 环上的 Dennis–Stein 符号与乘积

域中每个非零元素可逆. 对一般环, 还希望使用非单位作参数, 尤其是理想中的元素.

#definition(title: [Dennis–Stein 符号])[
  设 $R$ 交换, $r,s in R$, 且 $u=1-r s$ 可逆. 定义
  $ ⟨r,s⟩:=x_(j i) (-s u^(-1))x_(i j) (-r)x_(j i) (s)x_(i j) (u^(-1)r)h_(i j) (u)^(-1) $
  这是 $K_2 (R)$ 的元素. 若 $r$ 可逆, 则
  $ ⟨r,s⟩={r,1-r s} $
] <def-dennis-stein-symbol>

直接乘四个初等矩阵, 得到对角块 $op("diag") (u,u^(-1))$, 所以最后乘 $h_(i j) (u)^(-1)$ 后的矩阵像为 $1$. 符号与下标选择无关, 因为可用稳定初等矩阵同时共轭这两个坐标. 第二个公式由同样的 $w,h$ 共轭计算得到.

#theorem(title: [Dennis–Stein 呈示])[
  若 $R$ 是交换局部环, 则 $K_2 (R)$ 由上述符号生成, 关系为
  $ ⟨r,s⟩+⟨s,r⟩&=0, \
    ⟨r,s⟩+⟨r,t⟩&=⟨r,s+t-r s t⟩, \
    ⟨r,s t⟩&=⟨r s,t⟩+⟨t r,s⟩ $
  每条关系都要求出现的符号有定义.

  若 $I subset.eq J(R)$, 则 $K_2 (R,I)$ 由至少一个参数属于 $I$ 的符号生成. 关系仍为前两式, 加上第三式中 $r,s,t$ 至少一个属于 $I$ 的情形.
] <thm-dennis-stein-presentation>

这是 @Wei13[III, 定理 5.11.1] 的呈示定理, 此处引用. 它把含非单位的计算也变成符号计算. 例如对 $R=k[epsilon] slash (epsilon^2)$, 每个 $1-epsilon a$ 都是单位, 所以 $⟨epsilon,a⟩$ 总有定义, 并且属于 $K_2 (R,(epsilon))$. 若 $a$ 可逆, 可改写成 $- {a,1-a epsilon}$.

#example(title: [模 $4$ 的整数])[
  取 $R=ZZ slash 4$. 此时 $⟨r,s⟩$ 有定义当且仅当 $r s$ 为偶数. 关系给出 $⟨r,0⟩=⟨r,1⟩=0$, 再用反对称性, 只剩
  $ c=⟨2,2⟩, quad ⟨2,3⟩=c, quad ⟨3,2⟩=-c, quad 2c=0 $
  例如第二个等式来自 $⟨2,1⟩+⟨2,2⟩=⟨2,3⟩$.

  为检查 $c$ 非零, 对 $r,s$ 取 $0,1,2,3$ 中的代表, 定义
  $ chi(⟨r,s⟩)=floor(r slash 2)floor(s slash 2) quad mod 2 $
  在允许的参数上, 逐项代入可验证 Dennis–Stein 的三条关系都保持, 而 $chi(c)=1$. 因而
  $ K_2 (ZZ slash 4) tilde.eq ZZ slash 2 $
  与 $K_2 (bb(F)_2)=0$ 比较可知, $K_2$ 一般不具有幂零不变性. 这里平方为零的理想 $(2)$ 确实贡献了信息.
] <ex-k2-integers-mod-four>

#theorem(title: [两个 $K_1$ 类的乘积])[
  对交换环 $R$, 存在自然的反对称双线性配对
  $ K_1 (R) times.o_ZZ K_1 (R)->K_2 (R) $
  在单位给出的类上, 它将 $[r] times.o [s]$ 送到 ${r,s}$.
] <thm-k1-k1-product>

构造如下. 对 $g in GL_m (R)$ 与 $h in GL_n (R)$, 两个自同构 $g times.o 1$ 和 $1 times.o h$ 在 $R^m times.o_R R^n tilde.eq R^(m n)$ 上交换. 令
$ A=ZZ[x,x^(-1),y,y^(-1)] $
将 $x,y$ 分别送到这两个自同构, 把 ${x,y}$ 映入 $K_2 (M_(m n) (R))$, 再用 Morita 等价映回 $K_2 (R)$. 这就是配对的值.

补单位块只增加含恒等自同构的项, 同时共轭不改变符号, 因而构造与所选基和稳定化无关. 对矩阵乘法的双线性则使用 @Wei13[III, 定理 5.12.2] 的乘积定理. 它保证交换子映为零, 使这个配对通过 $K_1$.

== 留数与域扩张 <sec-k2-tame>

符号给出了 $K_2$ 的代表, 留数则提供检测这些类的方法. 一个离散赋值把域中的零点与极点变成整数, 相应的 tame symbol 把 $K_2$ 类送到剩余域的单位群.

#definition(title: [离散赋值与剩余域])[
  域 $F$ 上的离散赋值是满射 $v:F^times->ZZ$, 满足 $v(a b)=v(a)+v(b)$ 与 $v(a+b)>=min(v(a),v(b))$, 约定 $v(0)=infinity$.

  相应的赋值环, 极大理想与剩余域为
  $ cal(O)_v={a | v(a)>=0}, quad frak(m)_v={a | v(a)>0}, quad k_v=cal(O)_v slash frak(m)_v $
  满足 $v(pi)=1$ 的元素称为一致化参数. 每个非零元素唯一写成 $a=pi^m u$, 其中 $u in cal(O)_v^times$.
] <def-discrete-valuation-k2>

#proposition(title: [Tame symbol])[
  存在自然满射
  $ partial_v:K_2 (F)->k_v^times $
  在符号上的公式为
  $ partial_v {a,b}=(-1)^(v(a)v(b)) overline(b^(v(a)) slash a^(v(b))) $
  括号内是赋值为零的单位. 特别地,
  $ partial_v {pi,u}=overline(u), quad
    partial_v {u,pi}=overline(u)^(-1), quad
    partial_v {u,w}=1 $
  其中 $u,w$ 是赋值环的单位.
] <prop-tame-symbol>

#proof[
  写 $a=pi^m u$, $b=pi^n w$, 公式成为
  $ (-1)^(m n) overline(w)^m overline(u)^(-n) $
  所以它对两变量乘法均为乘法同态. 只需检验 Steinberg 关系.

  若 $v(a)>0$, 则 $1-a$ 是剩余值为 $1$ 的单位, 公式给出 $1$. 若 $v(a)=0$, 则 $v(1-a)>=0$; 两者均为单位时结论显然, 否则 $overline(a)=1$, 仍然得到 $1$.

  若 $m=v(a)<0$, 则 $v(1-a)=m$, 且 $(1-a) slash a$ 的剩余值为 $-1$. 公式等于 $(-1)^(m^2+m)=1$. 因而由 Matsumoto 定理得到同态. 每个 $k_v^times$ 的元素可提升为单位 $u$, 然后由 ${pi,u}$ 映到它, 所以满射.
]

这里源群用加法, 目标单位群用乘法: $partial_v (z+z')=partial_v (z)partial_v (z')$. 本章统一使用 $partial_v {pi,u}=overline(u)$ 的约定; 另一些文献采用其逆.

#example(title: [用留数检测非零符号])[
  在 $QQ(t)$ 中取 $t=0$ 的赋值. 则
  $ partial_0 {t,2}=2 in QQ^times $
  因而 ${t,2}$ 有无限阶. 更一般地, 对任意域 $k$ 和 $a in k^times$, ${t,a}$ 在 $K_2 (k(t))$ 中的阶与 $a$ 在 $k^times$ 中的阶相同: 留数给出一个方向, 双线性给出另一个方向.
] <ex-k2-rational-tame>

#proposition(title: [赋值扩张下的相容性])[
  若 $F subset.eq L$, 且 $w|_(F^times)=e v$, 剩余域映射记为 $i:k_v->k_w$, 则
  $ partial_w (op("res") (z))=i(partial_v (z))^e $
] <prop-tame-ramification>

#proof[
  对 ${a,b}$ 代入公式即可. 两侧的单位部分相同, 符号部分相差 $(-1)^((e^2-e)v(a)v(b))=1$. 符号生成整个 $K_2$, 所以公式对所有元素成立.
]

=== 有理函数域与互反律

对有理函数域, 可以同时取各不可约多项式处的留数. 先用首项系数分离常数域的部分, 再由这些留数描述其余部分.

#lemma(title: [首项系数给出的分裂])[
  对 $f in F(t)^times$, 记 $ell(f)$ 为分子首项系数除以分母首项系数. 则
  $ lambda:K_2 (F(t))->K_2 (F), quad {f,g} mapsto {ell(f),ell(g)} $
  是同态, 并且分裂常数域的映射 $K_2 (F)->K_2 (F(t))$.
] <lem-k2-leading-coefficient>

#proof[
  $ell$ 对乘法为同态. 检验 $f$ 与 $1-f$: 若 $deg(f)>0$, 两个首项系数为 $a,-a$, 符号为零; 若 $deg(f)<0$, 后者为 $1$; 若 $deg(f)=0$, 则首项系数为 $a,1-a$, 除非 $a=1$, 此时第一个参数已经是 $1$. 所以 Steinberg 关系仍然成立. 对常数 $ell$ 是恒等, 得到分裂.
]

#theorem(title: [有理函数域的 Bass–Tate 正合列])[
  令 $p$ 遍历 $F[t]$ 的首一不可约多项式, 记 $F_p=F[t] slash (p)$. 则有分裂正合列
  $ 0->K_2 (F)->K_2 (F(t))->^(plus.o.big_p partial_p) plus.o.big_p F_p^times->0 $
  因而, 以变量 $t$ 为给定坐标时,
  $ K_2 (F(t)) tilde.eq K_2 (F) plus.o plus.o.big_p F_p^times $
] <thm-k2-bass-tate>

一个符号只在分子分母的有限多个不可约因子处有非平凡留数, 所以映射确实落在直和中. 核与满射性将在 @thm-milnor-bass-tate 中统一证明, 这里是其次数 $2$ 的情形. 首项系数映射给出左端的收缩, 从而短正合列分裂.

#example(title: [有限域上的函数域])[
  由#link(<ex-k2-finite-field>)[有限域的计算]与上述正合列,
  $ K_2 (bb(F)_q (t)) tilde.eq plus.o.big_p bb(F)_(q^(deg p))^times $
  因而它是有限循环群的直和, 每个因子阶为 $q^(deg p)-1$. 有限域本身的 $K_2$ 为零, 加入一个变量后, 每个闭点的单位群都贡献一部分.
] <ex-k2-finite-rational>

#theorem(title: [有理函数的互反律])[
  在 $F(t)$ 上令 $v_infinity (f)=-deg(f)$. 对每个 $z in K_2 (F(t))$, 有
  $ partial_infinity (z) dot product_p N_(F_p slash F) (partial_p (z))=1 in F^times $
  这里只有有限多个因子不为 $1$, $N$ 为普通域范数.
] <thm-k2-weil-reciprocity>

#proof[
  $F(t)^times$ 由常数与首一不可约多项式生成, 所以只需检验两类生成元组成的符号. 两个常数的所有留数为 $1$. 对常数 $a$ 与首一多项式 $p$, 令 $d=deg(p)$, 则 ${p,a}$ 在 $p$ 处的范数为 $a^d$, 在无穷远处为 $a^(-d)$.

  对不同的首一不可约多项式 $p,q$, 令其次数为 $d,e$. 在 $p,q$ 处的留数分别为 $q mod p$ 与 $(p mod q)^(-1)$. 它们的范数之比为
  $ op("Res") (p,q) slash op("Res") (q,p)=(-1)^(d e) $
  这里 $op("Res")$ 是结式, 等式来自交换两组根. 无穷远处的留数也为 $(-1)^(d e)$, 所以乘积为 $1$. 若 $p=q$, 用 ${p,p}={p,-1}$ 化归常数情形. 双线性完成证明.
]

例如 ${t,a}$ 在 $0$ 与无穷远处的留数分别是 $a$ 与 $a^(-1)$. 互反律说明所有点的局部数据相互约束. Bass–Tate 正合列只列有限点, 无穷远处的那一项正由它们决定.

#theorem(title: [Dedekind 环的局部化列])[
  设 $R$ 是 Dedekind 环, $F$ 是分式域, $p$ 遍历非零素理想, $k(p)=R slash p$. 则有正合列
  $ plus.o.big_p K_2 (k(p))->K_2 (R)->K_2 (F)
    ->^(plus.o.big_p partial_p) plus.o.big_p k(p)^times->S K_1 (R)->0 $
] <thm-k2-dedekind-localization>

这里引用 @Wei13[III, §6] 使用的局部化定理, 其一般形式见#chapter-ref(<chap-higher-k-theory>)的#link(<sec-higher-k-basic-theorems>)[常用定理]. 若所有 $k(p)$ 都是有限域, 左端为零, 因而 $K_2 (R)$ 正好是分式域中在全部有限素点留数平凡的子群.

#example(title: [有理数的 $K_2$])[
  $S K_1 (ZZ)=0$, 而 $K_2 (bb(F)_p)=0$, 所以
  $ 0->K_2 (ZZ)->K_2 (QQ)->plus.o.big_(p "素数") bb(F)_p^times->0 $
  经 $QQ->RR$ 后取符号 $epsilon$, 它在 $K_2 (ZZ)$ 的生成元上为 $1$, 从而给出收缩. 因而
  $ K_2 (QQ) tilde.eq ZZ slash 2 plus.o plus.o.big_(p "素数") bb(F)_p^times $
  这里 $p=2$ 的因子是平凡群.
] <ex-k2-rationals>

=== Hilbert 90 与挠元 <sec-k2-field-extensions>

普通 Hilbert 90 说, 若 $L slash F$ 是有限循环 Galois 扩张, 生成元为 $sigma$, 则范数为 $1$ 的元素都形如 $b slash sigma(b)$. 加法写法下, 这是 $ker(N)=im(1-sigma)$.

#theorem(title: [$K_2$ 的 Hilbert 90])[
  设 $L slash F$ 是素数次循环 Galois 扩张, 生成元为 $sigma$. 则
  $ K_2 (L)->^(1-sigma) K_2 (L)->^(N_(L slash F)) K_2 (F) $
  正合.
] <thm-k2-hilbert90>

这里引用 @Wei13[III, 定理 6.6]. 范数由 @cor-k2-transfer 的限制标量函子诱导. 定理识别了范数的核, 并不要求范数满射. 下面用它研究 $K_2$ 的挠元.

#proposition(title: [特征 $p$ 时没有 $p$-挠元])[
  若 $op("char") (F)=p>0$, 则
  $ p z=0 "且" z in K_2 (F) quad ==> quad z=0 $
] <prop-k2-no-characteristic-torsion>

#proof[
  令 $L=F(t)$, $E=F(t^p-t)$. 则 $L slash E$ 是 $p$ 次循环扩张, 生成元满足 $sigma(t)=t+1$. 把 $z$ 看作 $K_2 (L)$ 中的常数类. 投影公式给出 $N_(L slash E) (z)=p z=0$, 所以 Hilbert 90 给出 $z=v-sigma(v)$.

  平移变量不改变首项系数, 因而 @lem-k2-leading-coefficient 中的收缩满足 $lambda sigma=lambda$. 施加 $lambda$ 就得到
  $ z=lambda(v)-lambda(sigma(v))=0 $
]

#theorem(title: [单位根生成相应的挠元])[
  设 $n$ 与 $op("char") (F)$ 互素, 且 $F$ 含一个本原 $n$ 次单位根 $zeta$. 则每个被 $n$ 消去的 $K_2 (F)$ 元素都形如
  $ {zeta,a} quad (a in F^times) $
] <thm-k2-root-of-unity-torsion>

#proof[
  先设 $n=p$ 为素数. 令 $L=F(t)$, $E=F(t^p)$, $sigma(t)=zeta t$. 对 $p z=0$ 的常数类, Hilbert 90 同样给出 $z=v-sigma(v)$. 若 $f$ 的次数为 $d$, 则
  $ ell(sigma(f))=zeta^d ell(f) $
  因此对任意符号 ${f,g}$, $lambda(sigma{f,g})-lambda{f,g}$ 由双线性展开后, 每一项都含参数 $zeta$. 反对称性可以把它移到第一位, 双线性再把和合成一个 ${zeta,a}$. 应用 $lambda$ 就得到 $z$ 的这种表达式.

  一般情形对 $n$ 的素因子数归纳. 写 $n=p m$. 因为 $m(p z)=0$, 归纳假设给出
  $ p z={zeta^p,a}=p{zeta,a} $
  所以 $z-{zeta,a}$ 被 $p$ 消去, 素数情形又将其写成 ${zeta^m,b}$. 合并得到 $z={zeta,a b^m}$.
]

这些挠元结论让我们进一步算出代数闭域与实数的 $K_2$ 结构.

#corollary(title: [代数闭域的 $K_2$])[
  若 $F$ 代数闭, 则 $K_2 (F)$ 唯一可除, 因而是 $QQ$-向量空间.
] <cor-k2-algebraically-closed>

#proof[
  给任意符号 ${a,b}$ 及正整数 $n$, 取 $c^n=a$, 就有 ${a,b}=n{c,b}$, 所以群可除.

  对不同于特征的素数 $p$, 若 $p z=0$, 则上一定理给出 $z={zeta,a}$. 再取 $b^p=a$, 得到 $z=p{zeta,b}={1,b}=0$. 特征本身的挠元由 @prop-k2-no-characteristic-torsion 排除. 所以群无挠, 乘以任意正整数均为同构.
]

#example(title: [代数闭不意味着 $K_2$ 消失])[
  $K_2 (overline(bb(F)_p))=0$, 因为代数闭包是有限域的滤过并, 而各有限域的 $K_2$ 都为零.

  但 $K_2 (CC)$ 非零. 取在 $QQ$ 上代数独立的 $s,t in CC$. #link(<sec-milnor-differentials>)[后面的微分符号]把 ${s,t}$ 送到
  $ (dif s slash s) and (dif t slash t) !=0 $
  因而“唯一可除”并不等于“零”.
] <ex-k2-algebraic-closed-different>

#proposition(title: [实数的 $K_2$ 分解])[
  令 $D=ker (epsilon:K_2 (RR)->ZZ slash 2)$. 则
  $ K_2 (RR) tilde.eq ZZ slash 2 plus.o D $
  第一因子由 ${-1,-1}$ 生成, $D$ 唯一可除.
] <prop-k2-real-decomposition>

#proof[
  每个实数单位是正数乘以一个符号. 双线性说明任意元素都是 ${-1,-1}$ 的倍数, 加上至少一个参数为正的符号之和. 后一类符号生成 $D$. 正数有任意次数的正根, 所以 $D$ 可除.

  若 $z in D$ 是挠元, 它在 $K_2 (CC)$ 中为零. 再用二次扩张 $CC slash RR$ 的转移可知 $2z=0$. 由 @thm-k2-root-of-unity-torsion, $z={-1,a}$. 若 $a>0$, 它是平方, 故此符号为零; 若 $a<0$, 此符号等于 ${-1,-1}$, 与 $z in D$ 矛盾. 所以 $D$ 无挠, 从而唯一可除.
]

#theorem(title: [局部域的结构])[
  设 $F$ 是非 Archimedean 局部域, $mu(F)$ 为其有限单位根群. 则
  $ K_2 (F) tilde.eq D_F plus.o mu(F) $
  其中 $D_F$ 唯一可除. 到 $mu(F)$ 的商映射由局部范数留数符号给出.
] <thm-k2-local-field>

这是 Moore 的结构定理及其无挠性补充, 见 @Wei13[III, 定理 6.2.4], 这里不证明. 它与实数的分解很相似: 一个可用符号检测的有限部分, 加上唯一可除部分. 例如 $QQ_2$ 的有限部分为 $ZZ slash 2$, 由 ${-1,-1}$ 生成.

== Milnor $K$ 群 <sec-milnor-k-theory>

Matsumoto 定理用两个单位和 Steinberg 关系描述了域的 $K_2$. 允许符号有任意多个参数, 并保留这条关系, 就得到 Milnor $K$ 理论. 以下 $F$ 仍是域, 所有次数一起组成一个分次环.

#definition(title: [Milnor $K$ 环])[
  将乘法 Abel 群 $F^times$ 看作 $ZZ$-模, 记其次数 $1$ 的元素为 $l(a)$, 所以 $l(a b)=l(a)+l(b)$. 定义
  $ K_*^M (F):=T_ZZ (F^times) slash ⟨l(a)l(1-a) | a in F backslash {0,1}⟩ $
  这里 $T_ZZ$ 是张量代数, 分母为齐次双边理想. 次数 $n$ 的部分记为 $K_n^M (F)$, 并记
  $ {a_1,dots,a_n}:=l(a_1) dots l(a_n) $
  空符号是 $1 in K_0^M (F)=ZZ$.
] <def-milnor-k-ring>

乘法就是串接符号. 因而构造从 Milnor $K$ 环出发的分次环同态时, 只需在次数 $1$ 给出群同态, 并检验它满足次数 $2$ 的 Steinberg 关系.

#proposition(title: [低次数与分次交换律])[
  有自然同构
  $ K_0^M (F)=ZZ, quad K_1^M (F)=F^times, quad K_2^M (F) tilde.eq K_2 (F) $
  此外, $K_*^M (F)$ 分次交换:
  $ x y=(-1)^(r s)y x quad (x in K_r^M (F), y in K_s^M (F)) $
  相邻的重复参数满足
  $ {dots,a,a,dots}={dots,a,-1,dots} $
] <prop-milnor-k-basic>

#proof[
  理想生成元都在次数 $2$, 所以次数 $0,1$ 不变; 次数 $2$ 的结论正是 Matsumoto 定理. 在次数 $2$ 中, @prop-steinberg-symbol-relations 给出反对称性与重复参数公式. 对任意符号, 将这两条关系乘上其余参数即可. 把一个 $r$ 重符号移过一个 $s$ 重符号, 共交换 $r s$ 次, 所以出现 $(-1)^(r s)$.
]

重复参数的符号仍可能非零, 例如 ${-1,-1}$. 还要保留记号中的上标 $M$: Milnor 群与一般代数 $K$ 群在次数 $0,1,2$ 相同, 更高次则各有自己的定义.

#example(title: [有限域与实数的 Milnor 群])[
  对有限域, $K_n^M (bb(F)_q)=0$ 对所有 $n>=2$ 成立. 因为任意长符号都包含一个次数 $2$ 的因子, 而这个因子已经为零.

  对实数, 模平方后只有 $-1$ 这一生成元, 因而
  $ K_*^M (RR) slash 2 tilde.eq (ZZ slash 2)[eta], quad deg(eta)=1 $
  其中 $eta={-1}$. 证明非零性也很直接: 将 $l(a)$ 送到 $eta$, 当 $a<0$; 正数送到 $0$. 因为 $a$ 与 $1-a$ 不同时为负, 这是到 $(ZZ slash 2)[eta]$ 的分次环同态, 并将 ${-1,dots,-1}$ 送到 $eta^n$.
] <ex-milnor-finite-real>

=== 留数与 Bass–Tate 定理

#theorem(title: [Milnor 留数与特殊化])[
  设 $v$ 是 $F$ 上的离散赋值, 剩余域为 $k$, 一致化参数为 $pi$. 存在唯一同态
  $ partial_v:K_n^M (F)->K_(n-1)^M (k) quad (n>=1) $
  满足
  $ partial_v {u_1,dots,u_n}&=0, \
    partial_v {pi,u_2,dots,u_n}&={overline(u)_2,dots,overline(u)_n} $
  这里所有 $u_i$ 都是单位. 它与 $pi$ 的选择无关, 且为满射.

  给定 $pi$ 后, 还有分次环同态
  $ s_pi:K_*^M (F)->K_*^M (k), quad
    {pi^(r_1)u_1,dots,pi^(r_n)u_n} mapsto {overline(u)_1,dots,overline(u)_n} $
  称为特殊化. 一般来说, $s_pi$ 依赖参数.
] <thm-milnor-residue-specialization>

#proof[
  令 $A=K_*^M (k)$. 加入次数 $1$ 的形式符号 $Pi$, 构造分次环
  $ L=A plus.o Pi A, quad Pi a=(-1)^(deg(a))a Pi, quad Pi^2=Pi {-1} $
  所以 $L_n=A_n plus.o Pi A_(n-1)$. 关系的相容性来自 $2{-1}=0$.

  定义乘法群到 $L_1$ 的同态
  $ pi^r u mapsto {overline(u)}+r Pi $
  它满足 Steinberg 关系. 若 $v(a)>0$, 则 $1-a$ 剩余为 $1$; 若 $v(a)=0$, 按 $v(1-a)$ 是否为零检验. 若 $m=v(a)<0$, 令 $alpha={overline(pi^(-m)a)}$, 则两因子分别映到
  $ alpha+m Pi, quad alpha+{-1}+m Pi $
  它们的乘积为零: 交叉的 $alpha,Pi$ 项抵消, $alpha^2=alpha{-1}$ 且该项被 $2$ 消去, 剩余项为 $m(m+1)Pi{-1}=0$.

  因而得到分次环映射 $K_*^M (F)->L$. 取常数项给出 $s_pi$, 取 $Pi$ 的系数给出 $partial_v$. 任何符号展开后, 由 ${pi,pi}={pi,-1}$ 都可化成至多含一个 $pi$ 的符号之和. 这证明上述两个公式决定 $partial_v$. 将 $pi$ 换成 $u pi$ 只增加全为单位的符号, 其留数为零, 所以 $partial_v$ 与参数无关. 提升剩余域单位, 再在第一位放 $pi$, 就证明满射性.
]

次数 $1$ 的留数就是赋值 $F^times->ZZ$. 次数 $2$ 的留数就是 @prop-tame-symbol. 因而 $K_2$ 的 tame symbol 是同一构造在低次数中的表现.

#example(title: [两次留数])[
  对 $F=k(s,t)$, 先取 $s=0$ 的留数, 再取 $t=0$ 的赋值, 得到
  $ K_2^M (k(s,t))->^(partial_s) k(t)^times->^(v_t) ZZ, quad {s,t} mapsto t mapsto 1 $
  所以 ${s,t}$ 有无限阶. 类似地, 对 $n$ 个独立变量反复取留数, ${t_1,dots,t_n}$ 映到 $1 in ZZ$, 因而 $K_n^M (k(t_1,dots,t_n))$ 非零.
] <ex-milnor-iterated-residue>

#proposition(title: [完备离散赋值域模 $m$ 的分解])[
  若 $F$ 对 $v$ 完备, 且 $m$ 在 $k$ 中可逆, 则给定 $pi$ 后有同构
  $ K_n^M (F) slash m tilde.eq K_n^M (k) slash m plus.o K_(n-1)^M (k) slash m $
  两个分量分别由 $s_pi$ 与 $partial_v$ 给出.
] <prop-milnor-complete-valuation>

#proof[
  Hensel 引理说明每个主单位 $1+a$, $a in frak(m)_v$, 都有 $m$ 次根: 将多项式 $X^m-(1+a)$ 在剩余根 $1$ 处提升即可. 所以含主单位参数的符号模 $m$ 为零.

  提升 $k$ 的单位来定义右边到左边的映射, 再将第二分量的符号前面加上 $pi$. 不同提升之比是主单位, 因而映射与选择无关. 乘法关系由同样的理由保持; Steinberg 关系则可将 $overline(u),1-overline(u)$ 同时提升为 $u,1-u$. 每个 $F$ 中的符号都能展开成全单位项与一个 $pi$ 项, 所以上述映射与 $(s_pi,partial_v)$ 互逆.
]

例如对 $F=bb(F)_q ((t))$, $m$ 与 $q$ 互素, 有
$ K_2 (F) slash m tilde.eq bb(F)_q^times slash (bb(F)_q^times)^m $
它是阶为 $gcd(m,q-1)$ 的循环群. 对 $n>=3$, $K_n^M (F) slash m=0$.

有了高次数留数, 现在可以统一证明前面使用的有理函数正合列.

#theorem(title: [Milnor 群的有理函数正合列])[
  对 $n>=1$, 有分裂正合列
  $ 0->K_n^M (F)->K_n^M (F(t))
    ->^(plus.o.big_p partial_p) plus.o.big_p K_(n-1)^M (F[t] slash (p))->0 $
  其中 $p$ 遍历首一不可约多项式. 首项系数映射给出左端的收缩.
] <thm-milnor-bass-tate>

#proof[
  首项系数满足 Steinberg 关系, 已在 @lem-k2-leading-coefficient 中检验. 因而它延伸为分次环映射 $lambda:K_*^M (F(t))->K_*^M (F)$, 所以常数域映射是单射.

  固定 $n$, 令 $L_d$ 为由每个参数都是次数不超过 $d$ 的非零多项式的符号所生成的子群. 分解多项式并用双线性展开后, 可以等价地只用常数和次数不超过 $d$ 的首一不可约多项式. 有
  $ L_0=K_n^M (F), quad union.big_(d>=0) L_d=K_n^M (F(t)) $

  先看相同次数的两个首一多项式 $p,q$. 若 $p=q$, 用 ${p,p}={p,-1}$. 若 $p!=q$, 令 $h=q-p$, 则 $deg(h)<deg(p)$. 展开 $0={p slash q,h slash q}$ 得到
  $ {p,q}={p,h}+{-h,q} $
  所以在一个符号中, 可以逐次减少最高次数参数的个数. 因而 $L_d slash L_(d-1)$ 由
  $ {p,a_2,dots,a_n}, quad deg(p)=d, quad deg(a_i)<d $
  生成, 其中 $p$ 首一不可约.

  对固定的 $p$, 每个非零剩余类都有唯一的次数小于 $d$ 的多项式代表. 用这些代表定义
  $ h_p:K_(n-1)^M (F[t] slash (p))->L_d slash L_(d-1), \
  h_p {overline(a)_2,dots,overline(a)_n}=[{p,a_2,dots,a_n}] $
  检验多线性是关键. 设 $a'b' mod p$ 的代表为 $c$, 写 $a'b'-c=p f$. 若 $f=0$ 无需检验. 否则 $deg(f)<d$, 而
  $ (a'b' slash c)+( -p f slash c)=1 $
  Steinberg 关系给出
  $ {a'b' slash c,p}=-{a'b' slash c,-f slash c} $
  右边展开后所有参数的不可约因子次数都小于 $d$, 所以属于 $L_(d-1)$. 反对称后得到
  $ {p,a'b'}={p,c} quad mod L_(d-1) $
  乘上其余参数便证明每个位置的多线性. 若两个剩余参数和为 $1$, 它们的低次代表的和也等于 $1$, 所以 Steinberg 关系同样保持. 因而 $h_p$ 良定义.

  次数 $d$ 的各留数在 $L_(d-1)$ 上为零, 并满足 $partial_q h_p=0$ 当 $q!=p$, $partial_p h_p=id$. 上面的生成性说明
  $ L_d slash L_(d-1) tilde.eq plus.o.big_(deg(p)=d) K_(n-1)^M (F[t] slash (p)) $
  若所有留数为零, 这个同构使一个 $L_d$ 中的元素下降到 $L_(d-1)$; 归纳得到它属于 $L_0$. 这证明核恰好是常数项.

  对任意有限支撑的剩余数据, 先用 $h_p$ 提升最高次数部分, 再逐次消去较低次数处产生的多余留数. 次数严格下降, 过程有限终止, 所以总留数映射满射. 次数 $n=1$ 时同一论证就是有理函数的不可约因式分解, $h_p (1)$ 由 $p$ 表示. 最后用 $lambda$ 分裂短正合列.
]

这个证明同时解释了为什么多项式的次数是有效工具: Steinberg 关系能把两个最高次数因子改写成只含一个最高次数因子的项, 然后逐层用留数检测它们.

=== 范数与互反律

#definition(title: [单扩张的 Milnor 范数])[
  设 $L=F(alpha)$, $p in F[t]$ 为 $alpha$ 的首一最小多项式. 对 $x in K_n^M (L)$, 由 @thm-milnor-bass-tate 选
  $ y in K_(n+1)^M (F(t)), quad partial_p (y)=x, quad partial_q (y)=0 quad (q!=p) $
  定义
  $ N_(alpha slash F) (x):=-partial_infinity (y) in K_n^M (F) $
] <def-milnor-norm>

这个定义与 $y$ 的选择无关. 两个选择之差来自 $K_(n+1)^M (F)$, 而常数符号在无穷远处的留数为零. 因而范数是群同态.

#proposition(title: [范数的低次数与投影公式])[
  若 $d=[L:F]$, 则 $N_(alpha slash F)$ 在次数 $0$ 上为乘以 $d$, 在次数 $1$ 上为普通域范数. 对 $x in K_r^M (F)$ 与 $z in K_s^M (L)$, 有
  $ N_(alpha slash F) (op("res") (x)z)=x N_(alpha slash F) (z) $
  特别地,
  $ N_(alpha slash F) op("res")=d dot id $
] <prop-milnor-norm-projection>

#proof[
  次数 $0$ 中, $1 in K_0^M (L)$ 可用 $p(t) in K_1^M (F(t))$ 提升. 因为 $v_infinity (p)=-d$, 范数就是 $d$.

  次数 $1$ 中, 取只有 $p$ 处留数为 $z$ 的 $y in K_2 (F(t))$. @thm-k2-weil-reciprocity 说明
  $ partial_infinity (y) N_(L slash F) (z)=1 $
  所以定义中的负号, 用单位群乘法写, 正好给出通常的范数.

  证明投影公式时, 取 $z$ 的提升 $y$. 常数符号的留数为零, 分次交换律给出
  $ partial_v (op("res") (x)y)=(-1)^r op("res") (x)partial_v (y) $
  所以 $(-1)^r op("res") (x)y$ 是 $op("res") (x)z$ 的提升. 在无穷远处再用一次同样的公式, 两个符号抵消, 得到投影公式. 取 $z=1$ 即得最后一式.
]

#theorem(title: [Kato 的范数独立性])[
  对域的有限扩张 $L slash F$, 将 $L$ 写成有限个单扩张组成的塔, 并复合上述范数. 所得
  $ N_(L slash F):K_n^M (L)->K_n^M (F) $
  与生成元及扩张塔的选择无关. 它满足塔式公式与投影公式. 在次数 $2$, 它与 @cor-k2-transfer 的转移相同.
] <thm-milnor-kato-norm>

前面的定义已经消去了提升 $y$ 的选择, Kato 定理进一步消去生成元和扩张塔的选择. 这里引用 @Wei13[III, 定理 7.6]; 次数 $2$ 与转移的比较见该书 §6 与 §7 的范数讨论. 因而可以统一写成 $N_(L slash F)$. 它是分次群同态, 也是基域 Milnor 环的模同态, 一般不是保单位的环同态.

#corollary(title: [有限扩张的核与互反律])[
  + $K_n^M (F)->K_n^M (L)$ 的核被 $[L:F]$ 消去. 特别地, 有理化后该映射是单射.
  + 对 $z in K_(n+1)^M (F(t))$, 有
    $ partial_infinity (z)+sum_p N_((F[t] slash (p)) slash F) (partial_p (z))=0 $
] <cor-milnor-norm-reciprocity>

#proof[
  第一条来自 $N op("res")=[L:F]$. 第二条中, 将 $z$ 的各有限留数分别提升, 减去这些提升后得到常数类. 对它取无穷远留数为零, 再用范数的定义就得到等式. 当 $n=1$ 时, 加法写法转换回单位群乘法, 正是 @thm-k2-weil-reciprocity.
]

例如设 $op("char") (F)!=2$, $d in F^times$ 不是平方, $L=F(sqrt(d))$ 是相应二次扩张. 若 $a,b,c in F$ 且 $a!=0$, $b+c sqrt(d)!=0$, 则
$ N_(L slash F) {a,b+c sqrt(d)}={a,b^2-d c^2} $
这是投影公式在 $K_2$ 中最直接的计算. 取 $F=RR$, $d=-1$, $b^2+c^2=1$, 就得到 $N_(CC slash RR) {a,b+c i}=0$.

== Milnor 群的比较定理 <sec-milnor-comparisons>

前面的留数和范数在不同域的 Milnor 群之间传递信息. 现在转向另外三类目标: 微分形式, Galois 上同调与二次型的不变量. 每个映射都先由单位定义, 再检验 $a$ 与 $1-a$ 的像相乘为零. 比较定理则说明这些映射在什么条件下是同构.

=== 对数微分 <sec-milnor-differentials>

#proposition(title: [对数微分符号])[
  记 $Omega_F^n=Lambda_F^n Omega_(F slash ZZ)^1$. 则有自然分次环同态
  $ op("dlog"):K_*^M (F)->Omega_F^*, quad
    {a_1,dots,a_n} mapsto (dif a_1 slash a_1) and dots and (dif a_n slash a_n) $
] <prop-milnor-dlog>

#proof[
  Leibniz 公式给出 $dif(a b) slash (a b)=dif a slash a+dif b slash b$, 所以次数 $1$ 的映射保持群运算. 而
  $ (dif a slash a) and (dif(1-a) slash (1-a))
    =-(dif a and dif a) slash (a(1-a))=0 $
  因而满足 Steinberg 关系, 延伸到整个商环.
]

例如在 $F=k(s,t)$ 中, ${s,t}$ 的像为 $(dif s and dif t) slash (s t)$, 它在相对微分 $Omega_(F slash k)^2$ 中非零, 从而在绝对微分中也非零. 这和#link(<ex-milnor-iterated-residue>)[两次留数的例子]提供了两个不同的检测方法: 一个提取各点的阶数, 一个提取独立的微分方向.

#definition(title: [特征 $p$ 的对数微分群])[
  设 $op("char") (F)=p>0$. Cartier 理论给出加性算子
  $ ℘:Omega_F^n->Omega_F^n slash dif Omega_F^(n-1) $
  在对数形式上的公式为
  $ ℘(x (dif a_1 slash a_1) and dots and (dif a_n slash a_n))
    =(x^p-x) (dif a_1 slash a_1) and dots and (dif a_n slash a_n) quad mod dif Omega_F^(n-1) $
  定义 $nu(n)_F:=ker (℘)$. 这里 $℘$ 是加性的, 一般不是 $F$-线性的.
] <def-logarithmic-differentials>

#theorem(title: [Bloch–Gabber–Kato 与 Izhboldin 定理])[
  对特征 $p>0$ 的域及 $n>=1$, 有
  $ op("dlog"):K_n^M (F) slash p tilde.eq nu(n)_F $
  而且 $K_n^M (F)$ 没有非零的 $p$-挠元.
] <thm-milnor-characteristic-p>

这两条深结果引用 @Wei13[III, 定理 7.7.2 与定理 7.8]. 从定义已能看出, 对数微分消去 $p$ 倍元素, 且像落在 $ker(℘)$ 中. 定理进一步保证模 $p$ 后的映射恰好给出整个核, 并且是单射. 次数 $2$ 的无 $p$-挠性已在 @prop-k2-no-characteristic-torsion 中由 Hilbert 90 推出.

例如 $op("char") (k)=p$ 时, $k(s,t)$ 中的 ${s,t}$ 模 $p$ 仍然非零, 因为其对数微分非零. 这与“没有 $p$-挠元”并不冲突: 后者说乘以 $p$ 是单射, 并未要求它满射.

=== Galois 符号与 Brauer 群

#definition(title: [Galois 符号])[
  设 $m$ 与 $op("char") (F)$ 互素, $G_F=op("Gal") (F^"sep" slash F)$, $mu_m subset.eq (F^"sep")^times$ 为 $m$ 次单位根群. 记 $H^n (F,M)$ 为 $G_F$ 对离散模 $M$ 的连续群上同调.

  Kummer 正合列给出
  $ F^times slash (F^times)^m tilde.eq H^1(F,mu_m), quad a mapsto (a) $
  对应的 *Galois 符号*定义为
  $ h_(m,n):K_n^M (F) slash m->H^n (F,mu_m^(times.o n)), \
    {a_1,dots,a_n} mapsto (a_1) union dots union (a_n) $
  张量幂在 $ZZ slash m$ 上取, 并约定 $mu_m^(times.o 0)=ZZ slash m$.
] <def-milnor-galois-symbol>

#proposition(title: [Galois 符号良定义])[
  上述杯积满足 Steinberg 关系, 因而确实定义了自然的分次环同态
  $ K_*^M (F) slash m->plus.o.big_(n>=0) H^n (F,mu_m^(times.o n)) $
] <prop-galois-symbol-well-defined>

#proof[
  杯积双线性, 所以只需证明 $(a) union (1-a)=0$. 将可分多项式 $T^m-a$ 分解成首一不可约多项式的乘积, 各因子对应域 $F_i=F(alpha_i)$. 在 $T=1$ 处取值给出
  $ 1-a=product_i N_(F_i slash F) (1-alpha_i) $
  Galois 上同调的转移与普通范数相容, 杯积满足投影公式. 因而
  $ (a) union (1-a)=sum_i op("cor")_(F_i slash F)
    (op("res")_(F_i slash F) (a) union (1-alpha_i)) $
  在 $F_i$ 中 $a=alpha_i^m$, 所以 $op("res") (a)=0$. 每一项都为零, 得到 Steinberg 关系. 参见 @Wei13[III, 命题 6.10.3 与定理 7.11].
]

#theorem(title: [范数留数定理])[
  对域 $F$, 与其特征互素的正整数 $m$, 以及任意 $n>=0$, Galois 符号是同构:
  $ K_n^M (F) slash m tilde.eq H^n (F,mu_m^(times.o n)) $
  次数 $1$ 是 Kummer 理论, 次数 $2$ 是 Merkurjev–Suslin 定理; 全部次数的结论称为范数留数定理.
] <thm-norm-residue-isomorphism>

这里引用范数留数定理, 见 @Wei13[III, 注 6.10.4 与注 7.11.1, VI, 定理 3.1.1]. 上面的证明只负责构造 Galois 符号, 同构性是这个深定理的内容.

回顾#chapter-ref(<chap-k0>)中的 Brauer 群: 它由中心单代数在矩阵扩张下的等价类组成, 加法由张量积给出.

#proposition(title: [$K_2$ 与循环代数])[
  假设 $F$ 含本原 $m$ 次单位根 $zeta$, 且 $m$ 与特征互素. 对 $a,b in F^times$, 定义循环代数
  $ A_zeta (a,b):=F⟨x,y⟩ slash (x^m-a,y^m-b,y x-zeta x y) $
  它是维数 $m^2$ 的中心单代数. 选定 $zeta$ 后, 上述 Galois 符号识别为
  $ K_2 (F) slash m tilde.eq op("Br") (F)[m], quad {a,b} mapsto [A_zeta (a,b)] $
  其中 $op("Br") (F)[m]=ker (m:op("Br") (F)->op("Br") (F))$.
] <prop-k2-brauer-symbol>

这里使用标准的 Kummer 识别 $H^2(F,mu_m) tilde.eq op("Br") (F)[m]$, 并用 $zeta$ 将 $mu_m^(times.o 2)$ 识别为 $mu_m$. 循环代数的类对应两个 Kummer 类的杯积; 其同构性是 @thm-norm-residue-isomorphism 的次数 $2$. 选择单位根是把带张量幂的 Galois 符号写成上述 Brauer 群公式所需的数据.

#example(title: [Hamilton 四元数])[
  取 $m=2$, $a=b=-1$, 得到
  $ A_(-1) (-1,-1)=F⟨i,j⟩ slash (i^2+1,j^2+1,j i+i j) $
  在 $F=RR$ 时就是 Hamilton 四元数 $bb(H)$. 非零元素的范数是四个坐标平方之和, 所以每个非零元素可逆; 它是除环, 不同构于 $M_2 (RR)$. 因而 ${-1,-1}$ 的非零性, 也可以理解为这个四元数代数不能分裂.

  Steinberg 关系则对应 $A_(-1) (a,1-a)$ 分裂. 若 $a$ 不是平方, 在二次域 $F(sqrt(a))$ 中有
  $ N_(F(sqrt(a)) slash F) (1+sqrt(a))=1-a $
  四元数代数的范数判据便给出分裂. 若 $a$ 已是平方, 分裂更是直接的.
] <ex-k2-quaternion>

=== 二次型与 Stiefel–Whitney 不变量 <sec-milnor-quadratic-forms>

讨论二次型时, 设 $op("char") (F)!=2$. #link(<sec-topological-characteristic-classes>)[拓扑向量丛的特征类]中出现过 Whitney 直和公式. 对域上的二次型, Milnor 群中也有一个同样形式的公式.

#definition(title: [Witt 环与基本理想])[
  记 $⟨a_1,dots,a_r⟩$ 为非退化对角对称双线性型. 在同构类上用正交直和作加法, 张量积作乘法, 先群完备化得到 $G W(F)$, 再令双曲平面 $H=⟨1,-1⟩$ 为零, 得到 *Witt 环*
  $ W(F):=G W(F) slash ⟨H⟩ $
  维数模 $2$ 给出增广 $W(F)->ZZ slash 2$. 其核
  $ I:=ker (W(F)->ZZ slash 2) $
  称为*基本理想*. 它由 $⟨a⟩-1$, $a in F^times$, 生成, 并给出滤过 $W(F) ⊇ I ⊇ I^2 ⊇ dots$.
] <def-witt-fundamental-ideal>

#theorem(title: [Milnor 符号到 Witt 滤过])[
  存在自然满射
  $ s_n:K_n^M (F) slash 2->I^n slash I^(n+1), \
    {a_1,dots,a_n} mapsto product_(i=1)^n (⟨a_i⟩-1) $
] <thm-milnor-witt-surjection>

#proof[
  令 $delta(a)=⟨a⟩-1$. 因为
  $ delta(a b)=delta(a)+delta(b)+delta(a)delta(b) $
  模 $I^2$ 后它是群同态, 乘上其余因子就得到模 $I^(n+1)$ 的多线性.

  对 $a+b=1$, 二维型有等距
  $ ⟨a,b⟩ tilde.eq ⟨1,a b⟩ $
  事实上向量 $(1,1)$ 与 $(b,-a)$ 正交, 范数分别为 $1,a b$, 且构成一组基. 所以 $delta(a)delta(b)=0$, 这就是 Steinberg 关系.

  又因为 $⟨a^2⟩=1$, 有 $2delta(a)=-delta(a)^2 in I^2$. 所以映射消去 $2K_n^M (F)$. 最后, $I$ 由全部 $delta(a)$ 生成, 因而这些乘积生成 $I^n slash I^(n+1)$, 得到满射.
]

要识别这个满射在低次数中的逆映射, 可以给二次型定义取值于 Milnor 群的 Stiefel–Whitney 不变量.

#definition(title: [二次型的总 Stiefel–Whitney 不变量])[
  对 $q=⟨a_1,dots,a_r⟩$, 定义
  $ w(q):=product_(i=1)^r (1+{a_i}) in product_(n>=0) K_n^M (F) slash 2 $
  右边按次数完备化, 写成 $w(q)=1+w_1(q)+w_2(q)+dots$. 特别地,
  $ w_1(q)={a_1 dots a_r}, quad w_2(q)=sum_(i<j) {a_i,a_j} $
  $w_1$ 是行列式的平方类, $w_2$ 称为 Hasse 不变量.
] <def-algebraic-stiefel-whitney>

#proposition(title: [良定义与 Whitney 公式])[
  $w(q)$ 与对角化选择无关, 并且
  $ w(q plus.o q')=w(q)w(q') $
  因为常数项为 $1$, 它在完备分次环中可逆, 所以也延伸到 $G W(F)$ 的虚拟类.
] <prop-algebraic-whitney>

#proof[
  对称型的对角基变换可以由置换, 乘平方与二维对角型的等距变换生成. 前两种显然不改变公式. 对二维变换
  $ ⟨a,b⟩ tilde.eq ⟨alpha,beta⟩ $
  行列式说明 $a b=alpha beta$ 模平方. 若 $alpha=a x^2+b y^2$, 且 $x,y$ 都非零, 则
  $ 0={a x^2 slash alpha,b y^2 slash alpha}
    ={a,b}+{alpha,alpha}-{a,alpha}-{b,alpha} quad mod 2 $
  利用反对称性和 $a b=alpha beta$ 模平方, 得到 ${a,b}={alpha,beta}$ 模 $2$. 若 $x$ 或 $y$ 为零, 只需乘平方与置换. 这证明二维型的 $w_1,w_2$ 不变, 也就证明其总 $w$ 不变. 将该变换乘上其余一维因子, 得到一般情形.

  直和对应合并对角项, 所以总不变量相乘. 常数项为 $1$ 的形式级数具有逐次求得的逆, 因而可以对虚拟差定义 $w(q-q')=w(q)w(q')^(-1)$. 见 @Wei13[III, 引理 7.10.1].
]

这里 $w_1$ 采用不带维数符号修正的行列式平方类. 此外, $w$ 定义在 $G W(F)$ 上, 一般不会直接通过 $W(F)$: 双曲平面满足 $w(H)=1+{-1}$, 并非总为 $1$.

#corollary(title: [Witt 滤过的前两层])[
  上面的 $s_1,s_2$ 是同构. 特别地,
  $ F^times slash (F^times)^2 tilde.eq I slash I^2, quad
    K_2 (F) slash 2 tilde.eq I^2 slash I^3 $
] <cor-milnor-witt-low-degrees>

#proof[
  记 $hat(I)=ker (op("rank"):G W(F)->ZZ)$. 映射 $hat(I)->I$ 是环同构: $H$ 的秩为 $2$, 所以核为零; 而偶数秩的虚拟型可以减去若干 $H$ 调成秩零, 所以满射. 因而可在 $hat(I)$ 中计算 $w$.

  $w_1$ 是加性的, 且在 $(⟨a⟩-1) (⟨b⟩-1)$ 上为零. 所以它在 $I slash I^2$ 上诱导 $s_1$ 的逆.

  在 $hat(I)^2$ 上 $w_1=0$, 因而 Whitney 公式说明 $w_2$ 在这里可加. 令 $A={a}$, $B={b}$. 对一个乘积生成元, 有
  $ w((⟨a⟩-1) (⟨b⟩-1))=(1+A+B) slash ((1+A) (1+B)) $
  右边的次数 $1$ 项为零, 次数 $2$ 项为 $A B={a,b}$.

  再令 $C={c}$. 三个差的乘积的总不变量为
  $ ((1+A+B+C) (1+A) (1+B) (1+C)) slash
    ((1+A+B) (1+A+C) (1+B+C)) $
  分子与分母的次数 $1,2$ 项相同, 所以该式的 $w_1,w_2$ 都为零. 这些三重乘积生成 $hat(I)^3$, 因而 $w_2$ 消去 $I^3$. 它诱导 $I^2 slash I^3->K_2 (F) slash 2$, 并将 $s_2{a,b}$ 送回 ${a,b}$. 由于 $s_2$ 满射, 这便是其逆.
]

#theorem(title: [Milnor 二次型定理])[
  对 $op("char") (F)!=2$ 与所有 $n>=0$, 上面的满射都是同构:
  $ K_n^M (F) slash 2 tilde.eq I^n slash I^(n+1) $
] <thm-milnor-quadratic-isomorphism>

全部次数的同构是 Orlov–Vishik–Voevodsky 定理, 见 @Wei13[III, 注 7.9.2], 这里不证明. 对 $F=RR$, 签名给出 $W(RR)=ZZ$ 与 $I=2ZZ$, 所以它成为
$ K_n^M (RR) slash 2 tilde.eq 2^n ZZ slash 2^(n+1)ZZ tilde.eq ZZ slash 2 $
生成元 ${-1,dots,-1}$ 对应 $2^n$ 的类, 与#link(<ex-milnor-finite-real>)[实数 Milnor 群的计算]一致.

在特征 $2$ 下, 要区分对称双线性型的 Witt 环与非退化二次型的 Witt 群 $W Q(F)$. 对 $n>=1$, Kato 给出的对应版本为
$ K_n^M (F) slash 2 tilde.eq nu(n)_F tilde.eq I^n slash I^(n+1) $
这里 $I$ 属于双线性 Witt 环. 二次型部分则由正合列描述:
$ 0->I^n slash I^(n+1)->Omega_F^n->^℘ Omega_F^n slash dif Omega_F^(n-1)
  ->I^n W Q(F) slash I^(n+1) W Q(F)->0 $
见 @Wei13[III, 定理 7.10.4]. 这说明在特征 $2$ 时, 前面出现的对数微分也控制二次型滤过.

至此, 从初等矩阵的关系得到的 $K_2$, 已经通过单位符号接到了留数, 范数和几类比较定理. 这些工具适合域上的具体计算.

Milnor 理论通过增加符号的参数来推广 $K_2$. #chapter-ref(<chap-higher-k-theory>)则回到投射模与完美复形的整个范畴, 将对象, 自同构及更高相容关系一起组织成谱, 从而定义一般的高阶 $K$ 群.
