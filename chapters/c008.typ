#import "../template.typ":*

#show: doc => conf(
  easy: true,
  doc,
)

= 完美复形 / Perfect Complexes <chap-perfect-complex>

本章先固定定义. 从普通环上的有限投射复形出发, 再看概形上的局部版本. 环谱上, 核心定义是 *模范畴中的紧对象*; 对一般预层, 则在每个仿射测试点上检验这个条件. 随后定义向量丛与完美对象的 $K_0$.

以下的 $QCoh$ 沿用#chapter-ref(<chap-quasi-coherent>)的拟凝聚模无穷范畴, $f^*$ 与 $times.o$ 均按导出意义理解. 大小问题也沿用#chapter-ref(<chap-quasi-coherent>)的宇宙约定. 定义主要参考 @Lur17[第 7.2.4 节], @Lur11DAG8[第 2.7 节] 与 @Stacks26[第 36 章].

== 完美复形的定义

=== 普通环上的定义

取普通交换环 $R$. 记 $Dcat(R)$ 为 $R$-模的导出无穷范畴: 对象用复形表示, 拟同构成为等价. 采用上同调次数, 即微分 $d^i:P^i->P^(i+1)$ 满足 $d^(i+1) d^i=0$.

#definition(title: [环上的完美复形])[
  称 $P in Dcat(R)$ 为*完美复形* (perfect complex), 若存在整数 $a<=b$, 使 $P$ 在 $Dcat(R)$ 中等价于一个复形
  $ 0->P^a stretch(->)^(d^a) P^(a+1)->dots->P^b->0 $
  其中每个 $P^i$ 都是有限生成投射 $R$-模, 也就是某个有限秩自由模的直和因子. 区间 $[a,b]$ 以外的项为零.

  这些对象组成的满子范畴记为
  $ cat("Perf")(R) subset.eq Dcat(R) $
] <def-ring-perfect-complex>

定义要求的是*存在一个有界有限投射表示*. 它不要求手头写出的复形本身有界, 也不只是要求上同调模有限生成. 对普通模 $M$, 说它完美, 是指集中在零次的复形 $M[0]$ 满足这个定义. 参见 @Stacks26[Tag 0656].

=== 概形上的定义

#definition(title: [概形上的完美复形])[
  设 $X$ 是普通概形, $P in QCoh(X)$. 称 $P$ 为*完美复形*, 若对每个点 $x in X$, 都有开邻域 $U$, 使 $P|_U$ 拟同构于一个有界复形
  $ 0->E^a->E^(a+1)->dots->E^b->0 $
  其中各 $E^i$ 是有限局部自由的 $cal(O)_U$-模层. 这里有限局部自由是说, 在足够小的开集 $V subset.eq U$ 上有
  $ E^i|_V tilde.eq cal(O)_V^(plus.o r_i), quad r_i in NN $

  记这些对象组成的满子范畴为
  $ cat("Perf")(X) subset.eq QCoh(X) $
] <def-scheme-perfect-complex>

这是一个局部定义. 开集 $U$, 次数界 $a,b$ 以及各项的秩都可以随邻域变化; 定义没有选定整个 $X$ 上的同一个有界向量丛复形. 此处也不要求 $X$ 拟紧或拟分离.

在仿射概形上, $QCoh(Spec R) tilde.eq Dcat(R)$ 将这一局部定义与前面的环上定义对应起来, 因而沿用记号
$ cat("Perf")(Spec R) tilde.eq cat("Perf")(R) $
这里的相容性参见 @Stacks26[第 36.10 节].

=== 用紧对象定义环谱上的完美复形

现在取交换环谱 $A$, 不要求连通. 用模谱范畴 $Mod_A$ 代替普通复形范畴.

#definition(title: [环谱上的完美对象])[
  称 $P in Mod_A$ 为*完美 $A$-模*或*完美对象*, 若 $P$ 是 $Mod_A$ 中的紧对象. 具体地, 对任意小滤过无穷范畴 $J$ 和图表 $M:J->Mod_A$, 由各阶段的结构映射诱导的典范映射
  $ varinjlim(j in J) Map_(Mod_A) (P,M_j) -> Map_(Mod_A) (P,varinjlim(j in J) M_j) $
  必须是生象的等价.

  左边在 $Ani$ 中取余极限, 右边先在 $Mod_A$ 中取余极限. 紧对象组成的满子范畴记为
  $ cat("Perf")(A):=Mod_A^omega $
] <def-perfect-spectral-module>

直观地, 从 $P$ 映入滤过余极限所需的有限数据, 都能在某个阶段出现. $Map$ 同时记录映射及其全部高阶同伦, 所以紧性要求这些同伦数据也与滤过余极限相容.

对普通环 $R$, $H R$ 表示其 Eilenberg--Mac Lane 环谱. 等价 $Mod_(H R) tilde.eq Dcat(R)$ 将紧对象对应于有界有限生成投射复形, 所以
$ cat("Perf")(H R) tilde.eq cat("Perf")(R) $
这说明环谱上的定义确实延续了普通环上的用法. 参见 @Stacks26[Tag 07LT]. 对一般环谱, 完美性按紧性检验, 不附加同伦群只在有限多个次数非零的要求.

记 $cat("Thick")(A)$ 为从单位模 $A$ 经过有限次移位, 有限余极限和取收缩得到的对象组成的子范畴, 称为 $A$ 生成的*厚子范畴*.

#theorem(title: [完美性, 紧性与可对偶性])[
  设 $A$ 是交换环谱. 在 $(Mod_A,times.o_A,A)$ 中, 有
  $ cat("Perf")(A)=Mod_A^omega=Mod_A^"dual"=cat("Thick")(A) $
  其中 $Mod_A^"dual"$ 表示可对偶模组成的子范畴: 对象 $M$ 有对偶 $D$, 配有满足三角恒等式的余评价 $A->M times.o_A D$ 与评价 $D times.o_A M->A$.

  因而 $M$ 完美当且仅当 $M$ 可对偶. 此时其对偶为
  $ M^or:=underline(Hom)_A (M,A) in cat("Perf")(A) $
  并且对任意 $N in Mod_A$, 有自然的 $A$-模等价
  $ underline(Hom)_A (M,N) tilde.eq M^or times.o_A N $
] <thm-perfect-compact-dualizable>

#proof[
  单位模 $A$ 是紧对象, 它的各次移位检测模的全部同伦群, 因而紧生成 $Mod_A$. 紧生成范畴的紧对象恰好由紧生成元取有限构造与收缩得到, 所以 $Mod_A^omega=cat("Thick")(A)$; 参见 @Lur17[命题 7.2.4.2].

  *完美模可对偶.* $A$ 的对偶是自身. 可对偶对象对移位, 有限余极限和收缩封闭: 取对偶时将移位反向, 将余纤维改为纤维, 并取相应的收缩. 所以 $cat("Thick")(A)$ 中的对象都可对偶, 且这样构造出的对偶仍在 $cat("Thick")(A)$ 中.

  *可对偶模是紧的.* 若 $M$ 有对偶 $D$, 则
  $ Map_(Mod_A) (M,N) tilde.eq Map_(Mod_A) (A,D times.o_A N) $
  张量积保持余极限, 而 $A$ 紧, 所以右边保持滤过余极限. 这正是 $M$ 的紧性.

  最后, 对偶的三角恒等式给出伴随 $M times.o_A - tack.l D times.o_A -$. 与内部 Hom 的伴随定义比较, 得到 $underline(Hom)_A (M,N) tilde.eq D times.o_A N$. 取 $N=A$, 便有 $D tilde.eq underline(Hom)_A (M,A)=M^or$, 从而得到所述公式.
]

=== 一般拟凝聚模的定义

设 $X:CAlg_Lambda->Ani$ 是可达预层, 其中 $Lambda$ 是固定的交换环谱. 取 $Lambda=SS$, 就得到 $X:CAlg(Sp)->Ani$ 的情形. 不要求 $X$ 是概形或叠.

回顾 @def-qcoh-prestack. 一个仿射测试点是 $(A,x)$, 其中 $x in X(A)$, 也可写为 $x:Spec A->X$. 态射 $(A,x)->(B,y)$ 由环谱态射 $f:A->B$ 和路径 $X(f)(x) tilde.eq y$ 给出. 这些数据组成 $J_X$, 并且
$ QCoh(X)=varprojlim((A,x) in J_X) Mod_A $
所以 $P in QCoh(X)$ 给出各点上的模 $P_(A,x)=x^* P$, 以及相容等价
$ B times.o_A P_(A,x) tilde.eq P_(B,y) $
这些等价还带有对复合及更高同伦的相容数据.

#definition(title: [拟凝聚模的完美性])[
  称 $P in QCoh(X)$ 为*完美对象*, 若对每个仿射测试点 $x:Spec A->X$, 拉回 $x^* P$ 都是完美 $A$-模, 即 $Mod_A$ 中的紧对象.

  记
  $ cat("Perf")(X):={P in QCoh(X) | forall (A,x) in J_X, quad x^* P in Mod_A^omega} $
] <def-prestack-perfect-complex>

这里取 $QCoh(X)$ 的满子范畴. 因而一个完美对象, 就是一族带有上述基变换相容数据的完美模.

这个定义检验的是*各个 $Mod_A$ 中的紧性*. 对一般预层, 不能直接把它换成 $P$ 在整个 $QCoh(X)$ 中紧. 定义本身不需要选图册或覆盖.

当 $X=Spec A$ 时, 它恢复 $cat("Perf")(A)$; 当 $X$ 是普通概形时, 它恢复前面的局部有限复形定义. 结构模 $cal(O)_X$ 则是各测试点上取值为 $A$ 的那族相容模.

=== 完美对象的范畴结构

#theorem(title: [完美对象的范畴结构])[
  设 $X:CAlg_Lambda->Ani$ 是可达预层. 则
  $ (cat("Perf")(X), times.o_(cal(O)_X), cal(O)_X) $
  是本质小的, 刚性的, 幂等完备的稳定对称幺半 $oo$-范畴, 且张量积对每个变量都正合.

  这里本质小是指可以选取等价的小范畴. 刚性 (rigid) 是说每个对象 $P$ 都有对偶, 具体为
  $ P^or := underline(Hom)_X (P,cal(O)_X) in cat("Perf")(X) $
  配有满足三角恒等式的余评价与评价
  $ cal(O)_X -> P times.o P^or, quad P^or times.o P -> cal(O)_X $
  幂等完备 (idempotent complete) 则是说, 每个带全部相容同伦的幂等图表都能在此范畴内分裂.
] <thm-perfect-category-structure>

#proof[
  *先看仿射情形.* 单位模 $A$ 紧生成 $Mod_A$, 因而紧对象恰好是从 $A$ 经过有限次移位, 有限余极限和取收缩得到的对象, 见 @Lur17[命题 7.2.4.2]. 所以 $cat("Perf")(A)$ 本质小, 并对有限极限, 有限余极限和收缩封闭.

  $A$ 的对偶是自身. 上述操作也保持可对偶性: 移位后将对偶反向移位, 取余纤维后将对偶改取纤维, 收缩则取对偶的相应收缩. 因此每个完美模都有完美的对偶. 两个这样的模的张量积仍完美, 因为张量积保持有限余极限与收缩. 同理, 扩张标量 $B times.o_A -$ 保持完美对象; 它是正合对称幺半函子, 也保持对偶.

  *稳定性与对称幺半结构.* 在 $QCoh(X)$ 中取零对象, 有限极限或有限余极限, 拉到每个仿射点后仍得到完美模, 因而结果留在 $cat("Perf")(X)$ 中. 稳定性于是从 $QCoh(X)$ 继承. 同样, $cal(O)_X$ 完美, 且
  $ x^* (P times.o Q) tilde.eq x^* P times.o_A x^* Q $
  说明张量积也留在其中. 结合, 交换与单位的相容数据直接从 $QCoh(X)$ 继承. 张量积逐点保持有限余极限, 所以对每个变量都正合.

  *刚性.* 对完美对象 $P$, 在每个仿射点上取 $(x^* P)^or$. 对环谱态射 $A->B$, 换基保持对偶给出
  $ B times.o_A (x^* P)^or tilde.eq (B times.o_A x^* P)^or $
  所以这些局部对偶组成一个完美对象 $P^or$. 评价与余评价也与换基相容, 因而一起粘合; 三角恒等式逐点成立, 故整体成立. 由对偶的张量--Hom 伴随, 这个对象正是 $underline(Hom)_X (P,cal(O)_X)$. 这一论证也见 @Lur11DAG8[命题 2.7.28].

  *幂等完备性.* $QCoh(X)$ 有小余极限, 所以每个相容幂等图表都能分裂: 可取反复作用该幂等态射的序列的余极限. 若图表中的对象是 $P in cat("Perf")(X)$, 分裂所得对象 $Q$ 是 $P$ 的收缩. 拉回后 $x^* Q$ 仍是紧模 $x^* P$ 的收缩, 因而紧. 所以 $Q$ 仍在 $cat("Perf")(X)$ 中.

  *本质小性.* 由可达性, 可将 $X$ 写成仿射可表预层组成的小图表 $i mapsto Spec A_i$ 的余极限, 记指标范畴为 $I$. 如#chapter-ref(<chap-quasi-coherent>)所述, $QCoh$ 将这个余极限变成极限. 由于换基保持完美性, 该等价限制为
  $ cat("Perf")(X) tilde.eq varprojlim(i in I^opp) cat("Perf")(A_i) $
  具体地, 任意测试点 $Spec B->X$ 都在同伦意义下经过其中某个 $Spec A_i$, 因而其拉回是相应完美 $A_i$-模的换基. 所以在这些呈示点上检验完美性就够了. 每个 $cat("Perf")(A_i)$ 本质小, 而本质小范畴的小极限仍本质小, 这就证明了最后一点.
]

#corollary(title: [拉回保持完美性])[
  设 $f:X->Y$ 是可达预层之间的任意态射. 则拉回保持完美对象, 因而限制为正合对称幺半函子
  $ f^*:cat("Perf")(Y)->cat("Perf")(X) $
] <cor-pullback-preserves-perfect>

#proof[
  取 $P in cat("Perf")(Y)$. 对任意仿射测试点 $x:Spec A->X$, 由 @def-qcoh-pullback 有
  $ x^* f^* P tilde.eq (f compose x)^* P in cat("Perf")(A) $
  最后一步就是 $P$ 的完美性. 所以 $f^* P$ 在每个测试点上都完美, 即 $f^* P in cat("Perf")(X)$. 正合性与对称幺半结构则从拟凝聚模上的拉回继承.
]

=== 完美复形的例子

#example(title: [移位与有限直和])[
  对普通环 $R$, 有限生成投射模 $P$ 的任意移位 $P[m]$ 都完美. 对一般预层 $X$, $cal(O)_X [m]$ 及这些对象的有限直和也完美: 拉到仿射点后, 得到紧对象 $A[m]$ 及其有限直和.
] <ex-perfect-shifts>

#example(title: [两项复形])[
  取整数 $n>=2$, 将两项放在 $-1,0$ 次, 则
  $ [ZZ stretch(->)^n ZZ] tilde.eq (ZZ slash n ZZ)[0] $
  左边是有界有限自由复形, 所以完美. 乘 $n$ 的核为零, 余核为 $ZZ slash n ZZ$, 这就给出所写的拟同构. 因而 $ZZ slash n ZZ$ 虽然不是投射模, 仍是完美复形.

  同样, 任意两项有限生成投射模复形 $[P->Q]$ 都完美.
] <ex-perfect-two-term-complex>

#example(title: [余纤维与 Moore 谱])[
  对一般 $X$, 完美对象之间态射的余纤维仍完美: 拉回保持余纤维, 而模范畴中的紧对象对有限余极限封闭. 特别地, 对交换环谱 $A$ 与整数 $n>=2$,
  $ cofib(A stretch(->)^n A) in cat("Perf")(A) $
  取 $A=SS$, 就是 @def-mod-n-moore-spectrum 的 Moore 谱; 取 $A=H ZZ$, 就是上一例的模谱版本.
] <ex-perfect-cofibers-moore>

=== 拟紧拟分离概形上的紧性

#theorem(title: [完美对象与紧对象])[
  设 $X$ 是拟紧拟分离的普通概形, 即 qcqs 概形. 则
  $ cat("Perf")(X)=QCoh(X)^omega $
  换句话说, 此时逐仿射检验的完美性, 恰好等价于整个 $QCoh(X)$ 中的紧性.
] <thm-scheme-perfect-compact>

#proof[
  先说明一个事实: *qcqs 概形上的整体截面保持滤过余极限*. 仿射时, 整体截面只是限制标量. 拟紧分离时, 取有限仿射开覆盖, 各个有限交仍仿射, 用有限的交错 Čech 复形计算导出整体截面即可.

  一般 qcqs 情形, 取有限仿射开覆盖, 逐个加入其中的开集. 新加入的仿射开集与先前开集之并的交, 是仿射概形的拟紧开子概形, 因而拟紧分离. 用#chapter-ref(<chap-quasi-coherent>)的 Mayer--Vietoris 纤维序列归纳, 就得到所需结论: 这些计算只用有限极限, 而滤过余极限与有限极限交换. 也可参见 @Stacks26[Tag 08DZ].

  *完美对象是紧的.* 设 $P$ 完美. 将局部有界有限自由复形取对偶, 得到的对偶与限制相容, 因而粘合成 $P^or$. 局部的张量--Hom 等价也随之粘合, 给出
  $ Map_(QCoh(X)) (P,M) tilde.eq Omega^oo U_Lambda Gamma(X,P^or times.o M) $
  其中 $U_Lambda$ 取底层谱. 张量积, 整体截面, $U_Lambda$ 与 $Omega^oo$ 都保持滤过余极限, 所以左边也保持滤过余极限. 这就说明 $P$ 紧.

  *紧对象是完美的.* 设 $P$ 紧, 取任意仿射开嵌入 $j:U arrow.r.hook X$. 因为 $X$ 拟分离, 对每个仿射开集 $V subset.eq X$, $U ∩ V$ 都拟紧. 在 $V$ 上, $j_* M$ 由 $Gamma(U ∩ V,M|_(U ∩ V))$ 计算. 用刚才的事实, 可知 $j_*$ 保持滤过余极限.

  由伴随 $j^* tack.l j_*$,
  $ Map_(QCoh(U)) (j^* P,M) tilde.eq Map_(QCoh(X)) (P,j_* M) $
  右边的两个函子都保持滤过余极限, 因而 $j^* P$ 是 $QCoh(U)$ 中的紧对象. 仿射上的紧对象就是完美复形, 所以 $P$ 在每个仿射开集上都完美. 按局部定义, $P$ 完美.
]

这一结论也见 @Stacks26[Tag 09M1].

#corollary(title: [由完美对象恢复拟凝聚模])[
  设 $X$ 是 qcqs 普通概形. 则有自然等价
  $ QCoh(X) tilde.eq op("Ind")(cat("Perf")(X)) $
  这里 $op("Ind")$ 表示添加小滤过余极限的完备化. 特别地, 每个拟凝聚模都能写成完美对象的小滤过余极限.
] <cor-qcqs-qcoh-ind-perfect>

#proof[
  还要用到 qcqs 概形的紧生成定理: $QCoh(X)$ 由完美对象在小余极限下生成, 见 @Stacks26[Tag 09IS]. 结合 @thm-scheme-perfect-compact, 它由自身的紧对象生成.

  将包含函子按滤过余极限延拓, 得到 $F:op("Ind")(cat("Perf")(X))->QCoh(X)$. 紧性与 $op("Ind")$ 中的映射公式保证 $F$ 全忠实. 它还保持有限余极限, 因而保持所有小余极限. 于是其本质像对小余极限封闭, 又包含所有完美对象, 由生成性便是整个 $QCoh(X)$.
]

== 向量丛 <sec-perfect-vector-bundles>

仍设 $X:CAlg_Lambda->Ani$ 为可达预层. 先在 $QCoh(X)$ 中直接定义向量丛: 它在局部有有限个基向量.

=== 局部自由模与向量丛

#definition(title: [环谱上的局部自由模])[
  设 $A$ 是交换环谱, $r$ 是非负整数. 称 $E in Mod_A$ *局部自由, 秩为 $r$*, 若存在有限多个 $f_1,dots,f_m in pi_0 A$ 生成单位理想, 使每个 $j$ 都有 $A[f_j^(-1)]$-模的等价
  $ A[f_j^(-1)] times.o_A E tilde.eq A[f_j^(-1)]^(plus.o r) $
  这里的局部化按 @def-spectral-localization 理解, $A^(plus.o r)$ 是 $r$ 份单位模的直和, $r=0$ 时为零模.

  允许不同主开集上使用不同的有限秩 $r_j$, 就称 $E$ 为*有限局部自由模*.
] <def-locally-free-spectral-module>

生成单位理想保证这些主开集覆盖整个 $Spec(pi_0 A)$. 局部平凡化只要求存在, 不作为 $E$ 的额外结构. 对一般环谱, 秩数的是单位模的份数: 平凡模满足 $pi_i (A^(plus.o r)) tilde.eq (pi_i A)^(plus.o r)$, 可以保留各次同伦.

#definition(title: [局部自由模的秩])[
  设 $E$ 是有限局部自由 $A$-模. 对 $frak(p) in Spec(pi_0 A)$, 记 $kappa(frak(p))$ 为普通环 $pi_0 A$ 在 $frak(p)$ 处的剩余域. 定义*秩函数* $op("rk")_A (E):Spec(pi_0 A)->NN$, 令
  $ op("rk")_A (E)(frak(p)):=dim_(kappa(frak(p))) ((pi_0 E) times.o_(pi_0 A) kappa(frak(p))) $
  这里先取普通 $pi_0 A$-模 $pi_0 E$, 公式中的张量积在普通模范畴计算.
] <def-spectral-locally-free-rank>

在局部平凡化 $E[f_j^(-1)] tilde.eq A[f_j^(-1)]^(plus.o r_j)$ 上, 这个维数就是 $r_j$. 因而秩与平凡化的选择无关, 且是局部常值函数. 说 $E$ 的秩为 $r$, 就是说这个函数恒等于 $r$. 这延续了普通有限局部自由模的秩, 参见 @Stacks26[Tag 00NX].

#definition(title: [一般预层上的向量丛与线丛])[
  称 $E in QCoh(X)$ 为*向量丛*, 若对每个仿射测试点 $x:Spec A->X$, $x^* E$ 都是有限局部自由 $A$-模.

  定义 $E$ 沿 $x$ 拉回的*秩函数*为
  $ op("rk")_x (E):=op("rk")_A (x^* E):Spec(pi_0 A)->NN $
  若对每个 $x$, 这个函数都恒等于同一个非负整数 $r$, 就称 $E$ 为*秩 $r$ 的向量丛*. 秩 $1$ 的向量丛称为*线丛*. 不指定 $r$ 时, 允许秩局部变化.

  所有向量丛及其在 $QCoh(X)$ 中的态射组成满子范畴 $cat("Vect")(X)$. 固定秩 $r$, 只保留对象及其等价, 所得生象记为 $cat("Vect")_r (X)$. 这个生象仍保留自同构与高阶同伦.
] <def-qcoh-vector-line-bundles>

这些秩函数与基变换相容. 对环谱态射 $f:A->B$ 及相容路径 $X(f)(x) tilde.eq y$, 有 $y^* E tilde.eq B times.o_A x^* E$. 若 $frak(q) in Spec(pi_0 B)$, 则
$ op("rk")_y (E)(frak(q))=op("rk")_x (E)((pi_0 f)^(-1) (frak(q))) $
因为局部的 $A^(plus.o r)$ 换基后成为 $B^(plus.o r)$, 秩仍为 $r$.

更一般地, 若 $g:Y->X$, $z:Spec A->Y$, 由 @def-qcoh-pullback 有 $z^* g^* E tilde.eq (g compose z)^* E$, 因而
$ op("rk")_z (g^* E)=op("rk")_(g compose z) (E) $

#definition(title: [普通概形上的向量丛])[
  对普通概形 $X$, 一个向量丛就是有限局部自由的普通拟凝聚层 $E$: 每个点附近存在开集 $U$ 和非负整数 $r$, 使
  $ E|_U tilde.eq cal(O)_U^(plus.o r) $
  此时 $r$ 等于该点的纤维 $E times.o k(x)$ 的维数. 将 $E$ 放在零次, 就把它视为 $QCoh(X)$ 的对象, 与上面的一般定义一致.
] <def-scheme-vector-bundle>

向量丛是完美复形的特例. 普通情形下, 向量丛的局部模型只用零次的有限自由模; 完美复形则允许把有限局部自由模放在不同次数, 再用微分连接. 所以完美复形容纳了更多对象, 如非空普通概形上的 $cal(O)_X [1]$.

=== 概形与代数叠上的例子

以下 $K$ 为域, $G slash K$ 为光滑仿射群概形. 普通向量丛都放在零次.

#example(title: [概形上的向量丛])[
  $cal(O)_X^(plus.o r)$ 是秩 $r$ 的平凡丛. 仿射概形 $Spec R$ 上的向量丛对应有限生成投射 $R$-模. 射影直线上的 $cal(O)(1)$ 则是秩 $1$ 的非平凡线丛.
] <ex-vector-bundles-schemes>

#example(title: [分类叠上的表示])[
  $B G$ 上的向量丛就是有限维代数表示:
  $ cat("Vect")(B G) tilde.eq cat("Rep")_K^"fd" (G) $
  表示 $V$ 给出的丛秩为 $dim_K V$. 例如 $B GL_r$ 上, 标准表示 $K^r$ 给出秩 $r$ 的丛, 行列式特征标给出线丛.
] <ex-vector-bundles-classifying-stack>

#example(title: [$B bb(G)_m$ 上的线丛])[
  权 $d in ZZ$ 的表示 $t dot v=t^d v$ 给出线丛 $cal(L)_d$. 它们拉到 $Spec K$ 后都平凡, 但不同权重给出不同的线丛. 其中 $cal(L)_1$ 是万有线丛: 若 $x:T->B bb(G)_m$ 分类 $L$, 则 $x^* cal(L)_1 tilde.eq L$. 见 @prop-quotient-stack-calculation.
] <ex-weight-line-bundles>

#example(title: [商叠上的等变丛])[
  若 $G$ 作用在 $U$ 上, 则
  $ cat("Vect")([U slash G]) tilde.eq cat("Vect")^G (U) $
  即商叠上的向量丛对应 $G$-等变向量丛, 线丛对应其中秩一的对象. 见 @Stacks26[Tags 043S, 06WS].

  例如 $K$ 代数闭, $n>=2$ 且在 $K$ 中可逆时, $[AA_K^1 slash mu_n]$ 上由作用 $zeta dot (z,v)=(zeta z,zeta v)$ 得到的线丛 $cal(L)$ 满足 $cal(L)^(times.o n) tilde.eq cal(O)$. 它却不平凡, 因为原点稳定子在纤维上的作用非平凡.
] <ex-equivariant-bundles-quotient-stack>

== 完美对象的 $K_0$

=== 生成元与纤维序列关系

这里沿用#chapter-ref(<chap-k0>)中三角范畴的 $K_0$, 用稳定无穷范畴中的纤维序列来写关系. 对象的等价类与自由 Abel 群都在足够大的固定宇宙中取.

#definition(title: [完美对象的 $K_0$])[
  对上述预层 $X$, 定义
  $ K_0 (X):=K_0 (cat("Perf")(X)) $
  具体构造如下:

  + 对每个完美对象的等价类引入一个符号 $[P]$, 取这些符号上的自由 Abel 群.
  + 对 $cat("Perf")(X)$ 中每个纤维序列 $P'->P->P''$, 加入关系
    $ [P]=[P']+[P''] $
    即商掉所有 $[P]-[P']-[P'']$ 生成的子群.

  因而 $K_0 (X)$ 的元素是这些符号的有限整数线性组合, 按上述关系识别. 对交换环谱 $A$, 同样定义
  $ K_0 (A):=K_0 (cat("Perf")(A)) $
] <def-scheme-perfect-k0>

这里的纤维序列包含 @def-pointed-fiber-sequence 中的零同伦数据. 在稳定范畴中, 也可以用余纤维序列, 或同伦范畴中的区分三角
$ P'->P->P''->P'[1] $
来规定同一组关系. 因而关系使用所有这样的序列, 包括不分裂的序列.

本章的 $K_0 (X)$ 始终指这个完美版本. 仿射时写作 $K_0 (Spec A)=K_0 (A)$. 对普通环 $R$, 通过 $H R$ 理解其完美复形版本; 它与此前用有限生成投射模定义的 $K_0 (R)$ 相容.

张量积给出这个 $K_0$ 的环运算, 记号约定为
$ [P] dot [Q]:=[P times.o_(cal(O)_X) Q], quad 1:=[cal(O)_X] $
在环谱 $A$ 上, 相应地用 $times.o_A$ 和单位模 $A$.

=== 普通概形上的另外两个记号

#definition(title: [向量丛的 Grothendieck 群])[
  对普通概形 $X$, 记 $K_0^"vb" (X)$ 为由有限秩向量丛的同构类生成的 Abel 群, 对每个三项均为向量丛的短正合列
  $ 0->E'->E->E''->0 $
  加入关系 $[E]=[E']+[E'']$. 正合性在普通 $cal(O)_X$-模层范畴中理解.
] <def-scheme-vector-bundle-k0>

#definition(title: [凝聚层的 $G_0$])[
  对普通 Noetherian 概形 $X$, 定义
  $ G_0 (X):=K_0 (cat("Coh")(X)) $
  这里 $cat("Coh")(X)$ 是普通凝聚层组成的 Abel 范畴. 因而生成元是凝聚层的同构类, 关系来自所有凝聚层的短正合列.
] <def-scheme-g0>

这三个记号分别从完美对象, 向量丛与凝聚层出发. 它们的比较需要另行讨论; 当前先固定各自选取的对象和正合关系.

=== 基本性质

#proposition(title: [直和, 移位与余纤维])[
  对 $P,Q in cat("Perf")(X)$, 整数 $n$ 和态射 $u:P->Q$, 有
  $ [0]=0, quad [P plus.o Q]=[P]+[Q], quad [P[n]]=(-1)^n [P] $
  $ [cofib(u)]=[Q]-[P] $
  特别地, $K_0 (X)$ 的每个元素都能写成某一个完美对象的类.
] <prop-perfect-k0-basic-identities>

#proof[
  分别对纤维序列 $0->0->0$, $P->P plus.o Q->Q$, $P->0->P[1]$ 与 $P stretch(->)^u Q->cofib(u)$ 使用定义关系即可. 反复移位得到任意整数 $n$ 的公式. 最后, 正系数用有限直和实现, 负号用移位实现; 例如 $[P]-[Q]=[P plus.o Q[1]]$.
]

#proposition(title: [函子性与环结构])[
  本质小稳定无穷范畴之间的正合函子 $F:cal(C)->cal(D)$ 诱导群同态
  $ K_0 (F):K_0 (cal(C))->K_0 (cal(D)), quad [P] mapsto [F(P)] $
  因而正合等价诱导 $K_0$ 的同构.

  对本章的预层, $K_0 (X)$ 在上述张量乘法下是交换环. 任意态射 $f:X->Y$ 诱导含幺环同态
  $ f^*:K_0 (Y)->K_0 (X), quad [P] mapsto [f^* P] $
  这些同态保持恒等态射与反向的复合, 所以 $K_0$ 是预层上的反变函子.
] <prop-perfect-k0-functorial-ring>

#proof[
  正合函子保持纤维序列, 所以把定义关系送到定义关系. 张量积对每个变量正合, 保证乘法对关系相容并满足分配律; 结合, 交换与单位律来自 @thm-perfect-category-structure. 再用 @cor-pullback-preserves-perfect, 拉回正合且对称幺半, 因而诱导环同态. 复合的相容性在生成元上检验即可.
]

刚性还给出一个自然的环对合 $[P] mapsto [P^or]$. 因为对偶将纤维序列反向为纤维序列, 且 $(P times.o Q)^or tilde.eq P^or times.o Q^or$, $(P^or)^or tilde.eq P$.

=== 有界复形的交错和

#proposition(title: [与普通环的 $K_0$ 相容])[
  设 $R$ 是普通交换环, $P$ 由有界有限生成投射模复形 $P^bullet$ 表示. 则
  $ [P]=sum_i (-1)^i [P^i [0]] in K_0 (cat("Perf")(R)) $
  暂用 $K_0^"proj" (R)$ 表示#chapter-ref(<chap-k0>)中由有限生成投射模定义的群. 将投射模放在零次, 给出自然环同构
  $ K_0^"proj" (R) tilde.eq K_0 (cat("Perf")(R)) $
  逆映射就是取各项的交错和. 因而两者可以继续共用 $K_0 (R)$ 这个记号.
] <prop-perfect-k0-projective-comparison>

#proof[
  从最高次开始逐项截取 $P^bullet$, 得到有限滤过, 各层是 $P^i [-i]$. 对相应的纤维序列反复使用加法关系, 再用移位变号, 就得到第一个公式.

  反过来, 各项的交错和确实给出 $K_0^"proj" (R)$ 中的不变量: 上同调全为零的有界投射复形可以从最高次向下逐步分裂, 所以其交错和为零. 两个有界投射复形若在导出范畴中等价, 这个等价可由链映射表示; 其映射锥的上同调为零, 因而两端的交错和相同. 任意纤维序列也可用映射锥表示, 锥的逐项公式保证交错和可加.

  于是得到了两个方向的群同态. 它们在投射模上互逆, 而第一个公式说明投射模的类生成整个群, 所以确为同构. 张量积与放在零次的操作相容, 因而也是环同构. 参见 @Stacks26[Tag 0FJG].
]

同样, 若概形上的完美对象 $P$ 有一个*全局有界向量丛复形* $E^bullet$ 作为表示, 就有
$ [P]=sum_i (-1)^i [E^i] in K_0 (X) $
这让有限分解直接成为 $K_0$ 中的计算公式.

=== 几个计算与小应用

#example(title: [域上的 $K_0$ 就是 Euler 数])[
  对域 $K$, 有环同构
  $ chi:K_0 (K) tilde.eq ZZ, quad [P] mapsto sum_i (-1)^i dim_K H^i (P) $
  因为有限维向量空间都是自由模, 上一命题说明所有类都由 $[K]$ 生成. 各项维数的交错和等于上同调维数的交错和, 且 $chi([K])=1$, 所以没有额外关系. 张量积对应整数乘法.
] <ex-perfect-k0-field>

#example(title: [非零对象的类可以为零])[
  对 $n>=2$, 前面的两项复形给出纤维序列
  $ ZZ stretch(->)^n ZZ -> (ZZ slash n ZZ)[0] $
  所以在 $K_0 (ZZ)$ 中,
  $ [(ZZ slash n ZZ)[0]]=[ZZ]-[ZZ]=0 $
  这个完美对象并不为零. 因而 $K_0$ 中的类相等, 比对象等价弱得多. 同样, Moore 谱满足 $[M_n]=[SS]-[SS]=0$ 于 $K_0 (SS)$.
] <ex-perfect-k0-zero-class>

#example(title: [整体 Euler 特征])[
  设 $X$ 是域 $K$ 上的紧合概形. 对 $P in cat("Perf")(X)$, 导出整体截面 $Gamma(X,P)$ 只有有限多个非零上同调, 且各次都是有限维 $K$-向量空间, 因而属于 $cat("Perf")(K)$. 这里用到紧合态射的上同调有限性, 见 @Stacks26[Tag 02O3].

  整体截面保持纤维序列, 所以诱导群同态
  $ chi_X:K_0 (X)->ZZ, quad [P] mapsto sum_i (-1)^i dim_K H^i (X,P) $
  于是对每个纤维序列 $P'->P->P''$, 都有 $chi_X(P)=chi_X(P')+chi_X(P'')$; 若 $P$ 由全局有界向量丛复形 $E^bullet$ 表示, 则
  $ chi_X(P)=sum_i (-1)^i chi_X(E^i) $
  这就是把一个复形的 Euler 特征, 化成有限多个向量丛的 Euler 特征.
] <ex-perfect-k0-global-euler>

== Tor振幅 <sec-perfect-tor-amplitude>

=== Tor振幅的定义

Tor 振幅衡量的是: *张量函子把零次对象送到哪些次数*. 它需要一个 $t$-结构来规定次数. 回顾 @def-t-structure 与 @def-heart, 本节沿用复形的*上同调编号*, 记
$ cal(C)^([a,b]):=cal(C)_(>=-b) ∩ cal(C)_(<=-a), quad cal(C)^suit.heart=cal(C)^([0,0]) $
所以这里的上同调区间 $[a,b]$, 对应#chapter-ref(<chap-spectra>)的同伦次数区间 $[-b,-a]$.

#definition(title: [Tor 振幅])[
  设 $cal(C),cal(D)$ 是带 $t$-结构的稳定无穷范畴, $T:cal(C)->cal(D)$ 是正合函子. 对整数 $a<=b$, 用条件
  $ T(cal(C)^suit.heart) subset.eq cal(D)^([a,b]) $
  表示 $T$ 在心上的振幅包含于 $[a,b]$.

  特别地, 若 $cal(C)$ 是稳定对称幺半无穷范畴, 张量积对每个变量正合, 对 $M in cal(C)$ 令 $T_M (N):=M times.o N$. 称 $M$ 的 *Tor 振幅包含于 $[a,b]$*, 若
  $ M times.o N in cal(C)^([a,b]) quad "对每个" N in cal(C)^suit.heart $
  若存在这样的一对整数 $a,b$, 就称 $M$ 有*有限 Tor 振幅*.
] <def-tor-amplitude-categorical>

这里 $N$ 遍历心中的所有对象, 两个端点必须对所有 $N$ 同时有效. 区间给出一个界, 不要求最小. 更一般, 若张量作用 $cal(C) times cal(D)->cal(D)$ 对第一变量正合, 则对固定 $M in cal(D)$, 检验相应函子 $cal(C)->cal(D)$ 在心上的振幅即可.

#definition(title: [连通环谱上的 Tor 振幅])[
  设 $A$ 是连通交换环谱, $M in Mod_A$. 由 @prop-module-spectra-heart,
  $ Mod_A^suit.heart tilde.eq Mod_(pi_0 A)^"ord" $
  因而 $M$ 的 Tor 振幅包含于 $[a,b]$, 就是说对每个普通 $pi_0 A$-模 $N$, 都有
  $ pi_j (M times.o_A H N)=0 quad (j < -b " 或 " j > -a) $
  其中 $H N$ 沿 $A->H(pi_0 A)$ 视为离散 $A$-模. 张量积始终是导出张量积.
] <def-tor-amplitude-spectral>

这种离散模测试见 @Lur17[定义 7.2.4.21]; 该处用同伦编号描述单侧界. 对普通交换环 $R$, 上述定义就是
$ H^i (M times.o_R N[0])=0 quad (i ∉ [a,b], " 对每个普通 " R "-模 " N) $
若 $M$ 也是普通模, 则 $H^(-j) (M times.o_R N)=Tor_j^R (M,N)$ ($j>=0$). 对 $d>=0$, $M[0]$ 的 Tor 振幅包含于 $[-d,0]$, 恰好表示所有 $Tor_j^R (M,N)$ 在 $j>d$ 时消失. 这就是平坦维数不超过 $d$ 的表述. 参见 @Stacks26[Tag 08FZ].

#example(title: [单位模与两项复形])[
  单位模 $A$ 的 Tor 振幅包含于 $[0,0]$, 因为 $A times.o_A H N tilde.eq H N$. 这允许 $A$ 本身有许多非零的高次同伦群.

  对 $n>=2$, 两项自由复形 $[ZZ stretch(->)^n ZZ]$ 表示 $(ZZ slash n ZZ)[0]$, 其 Tor 振幅包含于 $[-1,0]$. 与任意普通模张量后, 两项仍只在 $-1,0$ 次; 取 $N=ZZ slash n ZZ$, 微分变成零, 两个次数都非零. 因而这个区间不能缩小.
] <ex-tor-amplitude-degrees>

#definition(title: [预层上的 Tor 振幅])[
  固定连通交换环谱 $Lambda$, 记 $CAlg_Lambda^"cn"$ 为连通交换 $Lambda$-代数的范畴. 设 $X:CAlg_Lambda^"cn"->Ani$ 是可达预层, $M in QCoh(X)$; 这里 $QCoh$ 仍由各仿射点上的相容模定义.

  称 $M$ 的 *Tor 振幅包含于 $[a,b]$*, 若对每个仿射测试点 $x:Spec A->X$, $x^* M$ 作为 $A$-模的 Tor 振幅都包含于 $[a,b]$. 展开就是说
  $ pi_j (x^* M times.o_A H N)=0 quad (j ∉ [-b,-a]) $
  对所有这样的 $x$ 与普通 $pi_0 A$-模 $N$ 同时成立. 若可以选取一对统一的有限整数界, 就称 $M$ 有有限 Tor 振幅.
] <def-tor-amplitude-prestack>

这仍是逐仿射的定义, 参见 @Lur11DAG8[定义 2.7.21]. 对普通概形, 可以在仿射开集上检验; 各处使用同一个区间时, 得到整体的振幅界.

本章先前允许非连通环谱, 但其模范畴一般没有上述由底层同伦群给出的标准 $t$-结构. 对定义在所有环谱上的预层, 刚才的逐仿射定义用于它的*连通限制*及拟凝聚模的相应限制. 若要讨论非连通测试点, 则须另行指定合适的 $t$-结构, 再按 @def-tor-amplitude-categorical 理解振幅.

=== Tor 维数

对普通模, Tor 维数记录高次 Tor 最迟在哪一层消失.

#definition(title: [Tor 维数])[
  设 $R$ 是普通交换环, $M$ 是 $R$-模, $d$ 是非负整数. 称 $M$ 的 *Tor 维数不超过 $d$*, 若对每个 $R$-模 $N$ 都有
  $ Tor_j^R (M,N)=0 quad (j>d) $
  满足这个条件的最小非负整数称为 $M$ 的 *Tor 维数* (Tor dimension), 记为 $op("Tor-dim")_R (M)$. 若不存在这样的整数, 就记为 $+oo$; 按此约定, 零模的 Tor 维数为 $0$.

  用前面的振幅记号, 就是
  $ op("Tor-dim")_R (M)<=d quad <==> quad M[0] " 的 Tor 振幅包含于 " [-d,0] $
] <def-tor-dimension-module>

这也叫*平坦维数*, 等于平坦解消
$ 0->F_d->dots->F_0->M->0 $
的最短长度 $d$, 其中每个 $F_i$ 都平坦. 因而 Tor 维数为 $0$ 恰好就是平坦. 参见 @Stacks26[Tag 066F]. 例如, 前面的#link(<ex-tor-amplitude-degrees>)[两项复形]给出
$ op("Tor-dim")_ZZ (ZZ slash n ZZ)=1 quad (n>=2) $

#definition(title: [有限 Tor 维数])[
  在前面已经固定 $t$-结构的语境中, 称对象 $M$ 有*有限 Tor 维数*, 若它有有限 Tor 振幅, 即存在整数 $a<=b$, 使其 Tor 振幅包含于 $[a,b]$.

  对普通环上的复形 $M in Dcat(R)$, 这就是说
  $ H^i (M times.o_R N[0])=0 quad (i ∉ [a,b]) $
  对所有普通 $R$-模 $N$ 同时成立. 对连通环谱上的模或预层上的拟凝聚模, 则分别使用 @def-tor-amplitude-spectral 与 @def-tor-amplitude-prestack 的振幅定义.
] <def-finite-tor-dimension>

普通复形的这一术语见 @Stacks26[Tag 0652]. 对模只需记录区间 $[-d,0]$ 的左端点; 对一般复形, 则保留两个端点 $[a,b]$.

=== 用 Tor 振幅刻画完美性

完美性可以拆成两个条件. 伪凝聚性保证解消的每一步只用有限个生成元, 有限 Tor 振幅则保证可以在有限步后停下来.

#definition(title: [伪凝聚复形])[
  设 $R$ 是普通交换环. 称 $E in Dcat(R)$ *伪凝聚* (pseudo-coherent), 若它可以由一个上有界的有限自由复形表示
  $ dots->F^(b-2)->F^(b-1)->F^b->0 $
  其中每个 $F^i$ 都是有限秩自由 $R$-模. 允许这个复形向负次数无限延伸. 将有限自由换成有限生成投射, 得到同一个条件.
] <def-pseudo-coherent-complex>

这里的"伪凝聚"比"拟凝聚"多了一项有限性要求, 两者不是同一个概念. 上述等价表述见 @Stacks26[Tag 064U].

#theorem(title: [完美复形的 Tor 刻画])[
  对任意普通交换环 $R$ 与 $E in Dcat(R)$, 有
  $ E " 完美 " quad <==> quad E " 伪凝聚且有有限 Tor 维数" $
  更精确地, 若 $E$ 伪凝聚且 Tor 振幅包含于 $[a,b]$, 则存在表示 $E$ 的有限生成投射复形
  $ 0->P^a->P^(a+1)->dots->P^b->0 $
  次数恰好限制在同一个区间 $[a,b]$ 内. 不要求 $R$ Noetherian. 参见 @Stacks26[Tag 0658].
] <thm-perfect-pseudo-coherent-tor>

#proof[
  有界有限投射复形当然伪凝聚, 与普通模张量后也不会超出原来的次数范围, 所以完美性给出右边两个条件.

  反过来, 设振幅包含于 $[a,b]$. 取 $N=R$ 可知 $H^i (E)=0$ 对 $i ∉ [a,b]$ 成立. 由伪凝聚性, 可以选取有限自由表示 $F^bullet->E$, 并使 $F^i=0$ 对 $i>b$ 成立, 见 @Stacks26[Tag 064U]. 令
  $ C:=coker(F^(a-1)->F^a) $
  它有限表示. 由于 $F^bullet$ 在 $a$ 以下正合, 尾部 $dots->F^(a-1)->F^a->C->0$ 是 $C$ 的自由解消. 因而对每个普通模 $N$,
  $ Tor_1^R (C,N) tilde.eq H^(a-1) (F^bullet times.o_R N)=0 $
  这里最后的消失正是 Tor 振幅的下界. 所以 $C$ 平坦; 有限表示且平坦的模是有限投射模, 见 @Stacks26[Tag 00NX].

  现在把 $F^bullet$ 在 $a$ 次截断, 换成
  $ 0->C->F^(a+1)->dots->F^b->0 $
  它仍表示 $E$, 每一项都有限投射, 且只占用 $[a,b]$ 中的次数.
]

=== 连通环谱上的刻画

#definition(title: [几乎完美模])[
  设 $A$ 是连通交换环谱. 称 $M in Mod_A$ *几乎完美* (almost perfect), 若存在整数 $k$, 使 $M in (Mod_A)_(>=k)$, 并且对每个整数 $n>=k$, 截断 $tau_(<=n) M$ 都是范畴
  $ (Mod_A)_(>=k) ∩ (Mod_A)_(<=n) $
  中的紧对象. 这里 $k,n$ 用同伦编号.
] <def-almost-perfect-module>

也就是说, $M$ 同伦下有界, 每个有限次数窗口中的信息都是紧的. 对 $A=H R$, 这正好对应普通环上的伪凝聚复形. 定义及有限自由逼近见 @Lur17[定义 7.2.4.10, 命题 7.2.4.11].

#theorem(title: [几乎完美性与有限 Tor 振幅])[
  设 $A$ 是连通交换环谱, $M in Mod_A$. 则
  $ M " 完美 " quad <==> quad M " 几乎完美且有有限 Tor 振幅" $
  这里 Tor 振幅仍用 @def-tor-amplitude-spectral 的离散模测试定义. 参见 @Lur17[命题 7.2.4.23(4)].
] <thm-perfect-almost-perfect-tor>

#proof[
  完美模几乎完美. 单位模的振幅为 $[0,0]$, 而移位, 有限余纤维和收缩都保持振幅有限, 所以完美模也有有限 Tor 振幅.

  反过来, 先移位使 $M$ 连通, 再取 $d>=0$, 使振幅包含于 $[-d,0]$. 对 $d$ 归纳. 当 $d=0$ 时, 离散模测试的平坦性判据说明 $M$ 平坦. 几乎完美的连通平坦模是有限自由模的收缩, 因而完美; 这是"有限表示且平坦则有限投射"的环谱版本, 见 @Lur17[定理 7.2.2.15, 命题 7.2.4.20].

  若 $d>0$, 几乎完美性保证 $pi_0 M$ 有限生成. 选取 $A^(plus.o r)->M$ 在 $pi_0$ 上满射, 并取纤维序列
  $ K->A^(plus.o r)->M $
  则 $K$ 仍连通且几乎完美. 与任意离散模 $H N$ 张量, 长正合列给出
  $ pi_j (K times.o_A H N) tilde.eq pi_(j+1) (M times.o_A H N) quad (j>=1) $
  所以 $K$ 的振幅包含于 $[-(d-1),0]$. 由归纳 $K$ 完美, 再由纤维序列得到 $M$ 完美.
]

=== 振幅为 $[0,0]$ 的完美对象

#corollary(title: [从完美对象认出向量丛])[
  设 $A$ 是连通交换环谱, $M in cat("Perf")(A)$. 以下条件等价:

  + $M$ 的 Tor 振幅包含于 $[0,0]$.
  + $M$ 是某个 $A^(plus.o r)$ 的收缩, 其中 $r$ 有限.
  + $M$ 有限局部自由.

  特别地, 对普通环 $R$, 振幅包含于 $[0,0]$ 的完美复形恰好是 $P[0]$, 其中 $P$ 为有限生成投射 $R$-模.
] <cor-perfect-tor-zero-vector-bundle>

#proof[
  普通环的结论就是 @thm-perfect-pseudo-coherent-tor 中 $a=b=0$ 的情形.

  对连通环谱, 完美模同伦下有界. 若它有负次数的同伦群, 最低非零的那一群在张量 $H(pi_0 A)$ 后仍非零, 与振幅 $[0,0]$ 矛盾. 所以 $M$ 连通, 上一定理证明中 $d=0$ 的情形便给出有限自由模的收缩.

  有限自由模的收缩仍平坦. 取 $pi_0$ 后得到有限投射 $pi_0 A$-模, 由 @prop-finite-projective-local 可在主开覆盖上选基. 将基提升到 $M$ 中, 得到局部映射 $A^(plus.o r)->M$; 平坦性保证它在所有同伦群上都是同构, 因而是等价. 反过来, 有限局部自由模与离散模张量后仍离散, 所以振幅包含于 $[0,0]$.
]

对定义在连通环谱上的预层 $X$, 逐仿射应用这个推论, 就得到
$ cat("Vect")(X)={M in cat("Perf")(X) | M " 的 Tor 振幅包含于 " [0,0]} $
这里的完美性提供了有限性. 若只要求振幅 $[0,0]$, 非零普通环上的无限秩自由模也满足, 却不是向量丛.

在普通概形上, 伪凝聚性按仿射开邻域定义, 上述定理逐仿射给出"完美当且仅当伪凝聚且局部有有限 Tor 维数". 一般连通谱预层上, 则在每个仿射测试点检验"几乎完美且有有限 Tor 振幅"; 区间可以随测试点变化. 这样判断完美性时, 就不必先写出整个空间上的一份有限投射解消.

=== 相对完美性与完美态射

对于 $f:X->Y$, 还可以只控制沿底空间 $Y$ 张量时产生的次数, 这就得到*相对完美性*. 以下先在普通概形上说明.

#definition(title: [完美态射])[
  设 $f:X->Y$ 局部有限型. 在仿射局部 $Spec B->Spec A$ 上, 选一个有限变量的多项式表示
  $ A->P:=A[t_1,dots,t_m] ->> B $
  称 $f$ *伪凝聚*, 若局部的 $B$ 作为 $P$-模伪凝聚. 若此外 $B$ 作为 $A$-模有有限 Tor 维数, 就称 $f$ 为*完美态射* (perfect morphism).

  等价地, 上述 $B$ 作为 $P$-模完美. 这些条件与多项式表示的选择无关. 参见 @Stacks26[Tag 067G, Tag 0687].
] <def-perfect-morphism>

这里要求的是 $B$ 在多项式环 $P$ 上的有限性. 若直接要求 $B in cat("Perf")(A)$, 就强得多. 例如非零环上的 $A->A[t]$ 给出完美态射, 因为可取 $P=B$ 且 $B$ 在 $A$ 上平坦; 但 $A[t]$ 不是有限生成 $A$-模. 另一方面, $ZZ->ZZ slash n ZZ$ ($n>=2$) 也给出完美态射, 这由前面的两项自由解消直接看出.

#definition(title: [相对完美复形])[
  设 $f:X->Y$ 是伪凝聚态射. 称 $E in QCoh(X)$ *相对于 $Y$ 完美*, 若 $E$ 在 $X$ 上伪凝聚, 且相对于底空间局部有有限 Tor 振幅. 具体地, 在足够小的仿射开集 $U=Spec B->V=Spec A$ 上, 记 $E_U$ 为对应的 $B$-模复形, 要求存在整数 $a<=b$, 使
  $ H^i (E_U times.o_A N[0])=0 quad (i ∉ [a,b]) $
  对每个普通 $A$-模 $N$ 成立. 区间可以随仿射开集变化. 这些对象组成的范畴记为
  $ cat("Perf")(X slash Y) subset.eq QCoh(X) $
] <def-relative-perfect-complex>

这里采用相对伪凝聚性与有限 Tor 振幅的约定; 当 $f$ 伪凝聚时, 相对伪凝聚性等价于 $E$ 在 $X$ 上伪凝聚. 参见 @Stacks26[Tag 0DI9, 引理 15.84.7]. 因而对这样的 $f$, 直接取 $E=cal(O)_X$ 就有
$ f " 完美 " quad <==> quad cal(O)_X in cat("Perf")(X slash Y) $
有限性在 $X$ 上检验, Tor 振幅则相对于 $Y$ 检验, 这正是两个条件各自的作用.

一个常用结论是, 若 $f$ 适当, 平坦且有限表示, 则
$ E in cat("Perf")(X slash Y) quad ==> quad f_* E in cat("Perf")(Y) $
且这里的导出推前与任意基变换相容, 见 @Stacks26[Tag 0DJT]. 这使相对完美性适合研究随底空间变化的上同调, 也是对偶理论与复形模空间中的基本有限性条件.

== 前推与投影公式 <sec-perfect-pushforward>

本节先在一般预层上推导投影公式, 再讨论前推何时保持完美性. 沿用#chapter-ref(<chap-quasi-coherent>)的约定, $f^*,f_*$ 和张量积都已经是导出的; 用普通复形的记号写, 它们就是 $L f^*,R f_*$ 和导出张量积.

=== 前推与完美性

设 $f:X->Y$ 是可达预层 $CAlg_Lambda->Ani$ 之间的态射. 由 @def-qcoh-pushforward, 拉回保持小余极限, 因而有右伴随
$ f^*:QCoh(Y) ⇄ QCoh(X):f_*, quad f^* tack.l f_* $
也就是
$ Map_(QCoh(Y)) (T,f_* F) tilde.eq Map_(QCoh(X)) (f^* T,F) $
以下简写这两个映射生象为 $Map_Y$ 和 $Map_X$. 前推保持极限, 因而在稳定范畴中正合. 但它未必保持小余极限, 也未必保持完美对象.

#proposition(title: [仿射前推的完美性判据])[
  对交换环谱态射 $A->B$ 及 $f:Spec B->Spec A$, 有
  $ f_* (cat("Perf")(B)) subset.eq cat("Perf")(A) quad <==> quad B in cat("Perf")(A) $
  右边把 $B$ 看成 $A$-模.
] <prop-affine-pushforward-perfect>

#proof[
  仿射前推就是限制标量. 若它保持完美性, 对单位模 $B in cat("Perf")(B)$ 使用即可.

  反过来, 由 @thm-perfect-compact-dualizable, 每个完美 $B$-模都由 $B$ 经过有限次移位, 有限余极限和收缩得到. 限制标量正合且保持收缩, 所以其像由完美 $A$-模 $B$ 经过同样的操作得到, 仍然完美.
]

例如对域 $k$, $f:Spec k[t]->Spec k$ 是光滑的完美态射, 但 $f_* cal(O)=k[t]$ 是无限维 $k$-向量空间, 因而不完美. 这也再次说明, 完美态射与其前推保持完美性是两个条件.

=== 投影映射的构造

给定 $E in QCoh(Y)$ 和 $F in QCoh(X)$, 想比较的是先在 $Y$ 上张量, 还是先把系数拉到 $X$ 上张量. 无论它们是否完美, 总有一个自然映射
$ alpha_(E,F):E times.o f_* F -> f_* (f^* E times.o F) $
它的构造只用伴随的余单位 $epsilon_F:f^* f_* F->F$. 先在 $X$ 上作
$ f^* (E times.o f_* F) tilde.eq f^* E times.o f^* f_* F
  stretch(->)^(id times.o epsilon_F) f^* E times.o F $
再沿 $f^* tack.l f_*$ 转置, 就得到 $alpha_(E,F)$. 第一处等价用了拉回的对称幺半性. 这称为*投影映射*, 投影公式则断言它在合适条件下是等价.

仿射时, $F$ 是 $B$-模, 这个映射就是张量积的结合等价
$ E times.o_A op("Res")_A^B F
  tilde.eq op("Res")_A^B ((B times.o_A E) times.o_B F) $
所以仿射情况下不要求 $E$ 完美. 一般情况下, 可对偶性提供了一个统一的证明.

=== 完美系数的投影公式

#theorem(title: [一般预层上的投影公式])[
  设 $f:X->Y$ 是可达预层之间的任意态射. 对 $E in cat("Perf")(Y)$ 和任意 $F in QCoh(X)$, 投影映射给出自然等价
  $ E times.o f_* F tilde.eq f_* (f^* E times.o F) $
  也就是
  $ f_* (F times.o f^* E) tilde.eq f_* F times.o E $
] <thm-prestack-projection-formula>

#proof[
  由 @thm-perfect-category-structure, $E$ 可对偶. 拉回保持对偶, 所以
  $ f^* (E^or) tilde.eq (f^* E)^or $
  对任意 $T in QCoh(Y)$, 依次使用对偶与伴随, 得到
  $ Map_Y (T,E times.o f_* F)
    &tilde.eq Map_Y (E^or times.o T,f_* F) \
    &tilde.eq Map_X (f^* (E^or times.o T),F) \
    &tilde.eq Map_X ((f^* E)^or times.o f^* T,F) \
    &tilde.eq Map_X (f^* T,f^* E times.o F) \
    &tilde.eq Map_Y (T,f_* (f^* E times.o F)) $
  这些等价对 $T,E,F$ 都自然. 因而 Yoneda 引理给出所需对象之间的等价. 展开对偶的评价与余评价, 再用三角恒等式, 其伴随转置正是上一段的 $id times.o epsilon_F$, 所以得到的就是投影映射 $alpha_(E,F)$.
]

这个证明适用于任意强对称幺半左伴随及其右伴随. 对本书的预层, 可达性已经保证 $QCoh$ 可呈示及前推存在; 此公式不再要求 $X,Y$ 是叠, 也不要求 $f$ 适当, 平坦或有有限 Tor 维数. 经典带环空间上的版本见 @Stacks26[Tag 0B54].

对偶还把内部 Hom 化成张量积:
$ underline(Hom)_Y (E,M) tilde.eq E^or times.o M $
于是对上述 $E,F$, 将投影公式用于 $E^or$ 就有
$ f_* underline(Hom)_X (f^* E,F)
  tilde.eq f_* ((f^* E)^or times.o F)
  tilde.eq underline(Hom)_Y (E,f_* F) $
这解释了完美系数的作用: 张量一个完美对象可以转化为张量其对偶的伴随运算, 因而能与前推交换.

特别地, 对结构态射 $p:X->Spec Lambda$ 和 $V in cat("Perf")(Lambda)$,
$ Gamma(X,F times.o p^* V) tilde.eq Gamma(X,F) times.o_Lambda V $
这里也没有要求 $Gamma(X,F)$ 完美.

=== 任意系数的投影公式

#proposition(title: [由完美系数推广到任意系数])[
  设 $f:X->Y$ 是可达预层之间的态射. 假设自然函子给出
  $ QCoh(Y) tilde.eq op("Ind")(cat("Perf")(Y)) $
  且 $f_*$ 保持小滤过余极限. 则 @thm-prestack-projection-formula 对任意 $E in QCoh(Y)$ 和 $F in QCoh(X)$ 都成立.
] <prop-projection-formula-arbitrary-coefficients>

#proof[
  将 $E$ 写成 $varinjlim(j in J) E_j$, 其中 $J$ 小且滤过, 每个 $E_j$ 完美. 投影映射两边关于 $E$ 都保持这个余极限: 拉回与张量积保持所有小余极限, 前推则由假设保持滤过余极限. 因而
  $ E times.o f_* F
    &tilde.eq varinjlim(j in J) (E_j times.o f_* F) \
    &tilde.eq varinjlim(j in J) f_* (f^* E_j times.o F) \
    &tilde.eq f_* (f^* E times.o F) $
  中间一步使用完美系数的投影公式. 自然性保证这仍是 $alpha_(E,F)$.
]

#corollary(title: [概形上的投影公式])[
  若 $f:X->Y$ 是普通概形之间的 qcqs 态射, 则对任意 $E in QCoh(Y)$ 和 $F in QCoh(X)$, 有
  $ f_* F times.o E tilde.eq f_* (F times.o f^* E) $
] <cor-scheme-projection-formula>

#proof[
  在 $Y$ 的仿射开集上检验即可, 因而可设 $Y=Spec A$, 此时 $X$ 是 qcqs 概形. 由 @cor-qcqs-qcoh-ind-perfect, $QCoh(Y)$ 是完美对象的 $op("Ind")$ 完备化.

  此时 $f_*$ 是导出整体截面, 它保持滤过余极限, 这一点已在 @thm-scheme-perfect-compact 的证明中用有限仿射覆盖与 Mayer--Vietoris 证明. 因而上一命题适用. 前推与开集限制相容, 所以这些局部等价给出整体等价. 参见 @Stacks26[Tag 08DZ, Tag 08EU].
]

这里的推广确实用到了额外假设. 例如取 $X=coprod_(i in NN) Spec k$, $Y=Spec k$, 并令 $F=cal(O)_X$. 此时
$ f_* F=product_(i in NN) k $
若 $E=plus.o.big_(j in NN) k$, 投影映射变为
$ (plus.o.big_(j in NN) k) times.o_k (product_(i in NN) k)
  -> product_(i in NN) (plus.o.big_(j in NN) k) $
左边的族在 $j$ 方向上有统一的有限支撑. 右边可以取第 $i$ 个分量为第 $i$ 个基向量, 因而不在像中. 所以任意系数的版本对一般预层并不自动成立.

=== 适当前推保持完美性

现在用投影公式控制前推的 Tor 振幅. 以下给出一个常用且假设明确的概形版本.

#theorem(title: [适当完美态射的前推])[
  设 $Y$ 是普通 Noetherian 概形, $f:X->Y$ 是适当的完美态射. 则前推限制为正合函子
  $ f_*:cat("Perf")(X)->cat("Perf")(Y) $
  即 $F$ 完美时, $f_* F$ 仍完美.
] <thm-proper-perfect-pushforward>

#proof[
  完美性在 $Y$ 上局部检验, 可设 $Y=Spec A$. 这时 $X$ 是 Noetherian 拟紧分离概形. 取有限仿射开覆盖 $U_1,dots,U_r$, 使 $F$ 在各块上由有界有限生成投射复形表示. 记 $G=f_* F$.

  *先看伪凝聚性.* $F$ 的上同调层凝聚, 且只有有限多个非零. 适当态射的凝聚上同调有限性定理保证它们的高阶前推仍凝聚. 有限仿射覆盖又给出上同调维数的界 $c=r-1$. 由上同调谱序列, $G$ 有界且各次上同调都是有限生成 $A$-模. 因为 $A$ Noetherian, 这说明 $G$ 伪凝聚. 这里用到的有限性定理见 @Stacks26[Tag 02O3, 引理 36.11.3].

  *再看相对 Tor 振幅.* $f$ 有有限 Tor 维数, 而 $F$ 局部由有限投射模作有限构造得到. 因而 $F$ 相对于 $Y$ 局部有有限 Tor 振幅. 覆盖只有有限块, 可以选取统一的整数 $a<=b$, 使每个普通 $A$-模 $N$ 都满足
  $ cal(H)^i (F times.o f^* N[0])=0 quad (i ∉ [a,b]) $

  *将这个界传给前推.* @cor-scheme-projection-formula 允许使用任意普通模 $N$, 给出
  $ G times.o_A N[0] tilde.eq f_* (F times.o f^* N[0]) $
  右边可用上述覆盖的有限 Čech 复形计算. 它的 Čech 次数在 $[0,c]$, 各块的上同调次数在 $[a,b]$, 所以
  $ H^i (G times.o_A N[0])=0 quad (i ∉ [a,b+c]) $
  这个界与 $N$ 无关, 故 $G$ 有有限 Tor 振幅.

  现在 $G$ 伪凝聚且有有限 Tor 振幅, 由 @thm-perfect-pseudo-coherent-tor 即知 $G$ 完美. 前推正合已由伴随关系说明. 这一结论也见 @Stacks26[Tag 08EV, Tag 0B6G].
]

证明中, 适当性提供上同调的有限生成性, 有限 Tor 维数提供张量后的统一次数界. Noetherian 假设则让有界凝聚复形直接成为伪凝聚复形. 这些是上述证明各步使用的条件.

Noetherian 不是所有版本都必须的. 例如前面#link(<def-relative-perfect-complex>)[相对完美性部分]引用的适当, 平坦且有限表示的情形, 在任意普通基概形上都有
$ f_* (cat("Perf")(X slash Y)) subset.eq cat("Perf")(Y) $
由平坦性, $cat("Perf")(X) subset.eq cat("Perf")(X slash Y)$, 所以它也给出绝对完美对象的前推. 这是相对完美复形的前推定理 @Stacks26[Tag 0DJT].

只有适当性则不够. 取 $A=k[epsilon] slash (epsilon^2)$ 和有限闭嵌入 $i:Spec k->Spec A$. 模 $k$ 在自身上完美, 但在 $A$ 上有自由解消
$ dots stretch(->)^epsilon A stretch(->)^epsilon A stretch(->)^epsilon A -> k -> 0 $
张量 $k$ 后所有微分为零, 所以 $Tor_i^A (k,k) tilde.eq k$ 对所有 $i>=0$ 成立. 因而 $i_* k$ 不完美. 有限态射虽然适当, 这里却没有有限 Tor 维数.

=== 一般预层上的前推有限性

回到可达预层. 投影公式已经在最初的伴随框架下成立, 而前推保持完美性还需要有限性. 一个直接的办法是把前推拉到仿射测试点上计算, 但这一步需要基变换定理.

对 $y:Spec A->Y$, 记
$ X_A:=X times_Y Spec A, quad u_A:X_A->X, quad f_A:X_A->Spec A $
由拉回的相容性与伴随, 总有基变换映射
$ beta_(y,F):y^* f_* F -> (f_A)_* u_A^* F $
它是 $f_A^* y^* f_* F tilde.eq u_A^* f^* f_* F -> u_A^* F$ 的伴随转置. 一般不能直接把这个映射当成等价.

#proposition(title: [逐仿射检验前推的完美性])[
  设 $f:X->Y$ 是可达预层之间的态射. 假设对每个仿射测试点 $y:Spec A->Y$:

  + $beta_(y,F)$ 对每个 $F in cat("Perf")(X)$ 都是等价.
  + $(f_A)_*$ 把 $cat("Perf")(X_A)$ 送入 $cat("Perf")(A)$.

  则 $f_*$ 保持完美对象.
] <prop-prestack-pushforward-affine-test>

#proof[
  拉回保持完美性, 所以 $u_A^* F$ 完美. 由两个假设,
  $ y^* f_* F tilde.eq (f_A)_* u_A^* F in cat("Perf")(A) $
  这对所有测试点成立, 正是 $f_* F$ 完美的定义.
]

这里把两个需要另外验证的事实写了出来: 前推能否换基, 以及换基后的前推是否有限. 对概形或代数叠, 应使用相应的基变换与有限性定理; 不能仅由逐点定义 $QCoh$ 就推出前推逐点计算.

#corollary(title: [可表仿射态射的充分必要条件])[
  设 $f:X->Y$ 可表仿射, 即每个 $y:Spec A->Y$ 的拉回 $X_A$ 都是某个 $Spec B_A$. 则
  $ f_* (cat("Perf")(X)) subset.eq cat("Perf")(Y)
    quad <==> quad forall (A,y), quad B_A in cat("Perf")(A) $
  特别地, 若每个 $B_A$ 都是有限局部自由的 $A$-模, 即 $f$ 可表有限局部自由, 则前推保持完美性. 这里 $Y$ 只需是可达预层.
] <cor-affine-prestack-pushforward-perfect>

#proof[
  可表仿射时, 前推在每个测试点上就是限制标量. 说明这个计算与换基相容即可: 对 $A->A'$, 有 $B_(A') tilde.eq A' times.o_A B_A$, 并且对每个 $B_A$-模 $M$,
  $ A' times.o_A op("Res")_A^(B_A) M
    tilde.eq op("Res")_(A')^(B_(A')) (B_(A') times.o_(B_A) M) $
  因而这些限制标量组成相容模族. 逐仿射的扩张与限制标量伴随一起给出全局的 $f^* tack.l f_*$, 所以这确实计算前推, 同时证明了上述基变换等价.

  若各 $B_A$ 在 $A$ 上完美, 用 @prop-affine-pushforward-perfect 与上一命题即可. 反过来, 若 $f_*$ 保持完美性, 则 $f_* cal(O)_X$ 完美; 在 $y$ 上的值正是 $B_A$, 所以每个 $B_A$ 都完美. 有限局部自由时, 这些模是向量丛, 自然满足条件.
]

另一个办法是使用紧性, 它不依赖仿射描述.

#proposition(title: [通过右伴随检验前推的完美性])[
  假设 $QCoh(X)$ 和 $QCoh(Y)$ 都由紧对象生成, 且两边的紧对象恰好是完美对象. 再设 $f_*$ 保持小余极限, 从而有右伴随 $f^!$, 即
  $ f^* tack.l f_* tack.l f^! $
  则 $f_*$ 保持完美对象, 当且仅当 $f^!$ 保持小滤过余极限.
] <prop-pushforward-right-adjoint-criterion>

#proof[
  先设 $f^!$ 保持滤过余极限. 对完美对象 $P$ 和小滤过图表 $N_j$, 有
  $ Map_Y (f_* P,varinjlim(j in J) N_j)
    &tilde.eq Map_X (P,f^! (varinjlim(j in J) N_j)) \
    &tilde.eq Map_X (P,varinjlim(j in J) f^! N_j) \
    &tilde.eq varinjlim(j in J) Map_Y (f_* P,N_j) $
  最后一步用了 $P$ 的紧性及伴随. 所以 $f_* P$ 紧, 也就完美.

  反过来, 假设 $f_*$ 保持完美对象. 对每个紧对象 $P in QCoh(X)$, 用 $P$ 检验自然映射
  $ varinjlim(j in J) f^! N_j -> f^! (varinjlim(j in J) N_j) $
  再用伴随, 就得到紧对象 $f_* P$ 的紧性等价. 因而这个映射被所有紧生成元检验为等价, 它本身也是等价.
]

$f^!$ 是前推的右伴随, 与拉回 $f^*$ 的方向相同, 但定义不同; 它是对偶理论中的另一种逆像. 上述命题说明, 在紧生成的语境中, 前推的有限性可以转化为这个右伴随与滤过余极限的相容性. 对一般预层, 这里的紧生成性, 完美对象等于紧对象, 以及 $f_*$ 保持余极限都要另外验证.

叠上的自同构群也会影响有限性. 例如令 $k$ 的特征为 $p>0$, $G=C_p$, 并取 $q:B G->Spec k$. 单位对象 $cal(O)_(B G)$ 是线丛, 但由#chapter-ref(<chap-quasi-coherent>)的群上同调计算,
$ H^i (q_* cal(O)_(B G)) tilde.eq Ext_(k[G])^i (k,k) tilde.eq k quad (i>=0) $
最后一个等价可以直接验证: 写 $k[G] tilde.eq k[t] slash t^p$, 平凡模 $k$ 有微分交替为乘 $t$ 与乘 $t^(p-1)$ 的周期自由解消; 施加 $Hom_(k[G]) (-,k)$ 后所有微分为零. 所以前推有无限多个非零上同调, 并不完美. 推广到叠时, 必须检验这类上同调有限性.

=== 在 $K_0$ 上的前推

#corollary(title: [前推与 $K_0$ 的投影公式])[
  设 $f:X->Y$ 的前推保持完美对象. 则它诱导群同态
  $ f_*:K_0 (X)->K_0 (Y), quad [F] mapsto [f_* F] $
  对 $x in K_0 (X)$ 和 $y in K_0 (Y)$, 有
  $ f_* (x dot f^* y)=f_* (x) dot y $
  即 $f_*$ 是 $K_0 (Y)$-模同态, 其中 $K_0 (X)$ 通过 $f^*$ 成为 $K_0 (Y)$-模.
] <cor-perfect-k0-pushforward>

#proof[
  前推正合, 因而保持定义 $K_0$ 所用的纤维序列关系, 得到群同态. 对 $x=[F]$, $y=[E]$ 使用 @thm-prestack-projection-formula 并取类, 就得到公式; 再由可加性推广到所有元素.
]

前推一般不保持环的单位或乘法. 例如有限域扩张 $L slash k$ 的次数为 $d>1$ 时, $Spec L->Spec k$ 在 $K_0 tilde.eq ZZ$ 上的前推是乘 $d$. 对域上的适当概形, 结构态射的前推则正是前面#link(<ex-perfect-k0-global-euler>)[整体 Euler 特征]的构造.
