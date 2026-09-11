#import "../template.typ":*
#import "@preview/fletcher:0.5.8": *

#show: doc => conf(easy: true, doc,)

= Hopf 代数 <chap-hopf-algebras>

== 代数与余代数

=== 代数的定义

环谱可以看成谱中的代数对象. 现在把底层范畴换成一般的对称幺半 $oo$-范畴 $(cal(C),times.o,bold(1))$. $EE_1$-代数推广结合代数, $EE_oo$-代数推广交换代数; 将运算的方向反过来, 就得到余代数.

#definition(title: [$cal(O)^times.o$-代数])[
  设 $cal(O)^times.o$ 是一个无穷算筹. 对称幺半结构给出无穷算筹 $cal(C)^times.o->N(Fin_*)$. 一个取值于 $cal(C)$ 的 *$cal(O)^times.o$-代数*是无穷算筹态射
  $ A:cal(O)^times.o->cal(C)^times.o $
  即位于 $N(Fin_*)$ 之上且保持惰性态射的函子. 惰性态射负责选取输入分量, 保持它们就保证这个函子尊重运算的输入组织方式.

  这些代数及其自然变换组成无穷范畴
  $ Alg_(cal(O)^times.o) (cal(C))
    :=Fun^times.o_(\/ N(Fin_*)) (cal(O)^times.o,cal(C)^times.o) $
  这里 $Fun^times.o$ 表示上述保持惰性态射的函子. 参见 @Lur17[定义 2.1.3.1].
] <def-operadic-algebra>

对单色算筹, 可以把它理解为一个对象 $A$, 连同算筹指定的所有多元运算及其相容同伦. 以后简记
$ Alg(cal(C)):=Alg_(EE_1)(cal(C)), quad CAlg(cal(C)):=Alg_(EE_oo)(cal(C)) $
例如结合代数首先有乘法 $mu:A times.o A->A$ 和单位 $eta:bold(1)->A$, 再由算筹记录结合律及其全部相容性.

#example(title: [普通代数与环谱])[
  取普通交换环 $k$. 在普通模范畴 $(Mod_k^"ord",times.o_k,k)$ 的神经中, 结合代数和交换代数就是通常的含幺 $k$-代数与交换 $k$-代数. 例如矩阵环 $M_n(k)$ 是结合代数, 多项式环 $k[t]$ 是交换代数. 这里使用普通张量积, 普通范畴中没有额外的高阶同伦数据.

  在 $(Sp,smash,SS)$ 中, 两者分别是结合环谱和交换环谱. 普通环 $k$ 给出 $H k$; 若 $k$ 交换, 则 $H k$ 是交换环谱.
]

#proposition(title: [交换 $R$-代数的刻画])[
  设 $R$ 是交换环谱. 在 $(Mod_R,times.o_R,R)$ 中给出一个交换代数, 等价于给出一个交换环谱态射 $R->A$. 更准确地, 有自然等价
  $ CAlg(Mod_R) tilde.eq CAlg(Sp)_(R\/) $
  右边的态射是与 $R$ 的结构映射相容的交换环谱态射. 参见 @Lur17[推论 3.4.1.7].
] <prop-commutative-relative-algebra>

#proof[
  若 $A$ 是 $R$-模中的交换代数, 则单位是 $R->A$, 而复合
  $ A smash A->A times.o_R A stretch(->)^mu A $
  给出底层谱的乘法, 单位为 $SS->R->A$. 各个多元运算同样可以忘掉 $R$-线性, 从而得到交换环谱及其结构态射.

  反过来, 给定交换环谱态射 $f:R->A$, 用乘法赋予 $A$ 一个 $R$-作用. 由于 $f$ 保持交换代数结构, $A$ 的乘法及全部多元运算都相容地下降到相对张量积, 得到 $A times.o_R A->A$ 等运算, 单位就是 $f$. 两种构造互逆, 对态射及其同伦也相容, 因而给出所述范畴等价.
]

例如取 $R=SS$, 就恢复 $CAlg(Mod_(SS)) tilde.eq CAlg(Sp)$. 对普通交换环同态 $k->B$, 相应的例子是 $H k->H B$.

=== 余代数的定义

余代数将代数的运算方向反过来. 这里先取范畴的反范畴, 不要求对象本身有线性对偶.

#definition(title: [$cal(O)^times.o$-余代数])[
  设 $(cal(C),times.o,bold(1))$ 是对称幺半 $oo$-范畴. 给 $cal(C)^opp$ 配上诱导的对称幺半结构, 定义 *$cal(O)^times.o$-余代数范畴*
  $ cat("CoAlg")_(cal(O)^times.o) (cal(C)) := Alg_(cal(O)^times.o)(cal(C)^opp)^opp $
  特别记
  $ cat("CoAlg")(cal(C)):=cat("CoAlg")_(EE_1)(cal(C)), quad
    cat("CoCAlg")(cal(C)):=cat("CoAlg")_(EE_oo)(cal(C)) $
  它们分别称为余结合余代数与余交换余代数的范畴.
] <def-operadic-coalgebra>

一个余结合余代数 $D$ 首先有*余乘法*和*余单位*
$ Delta:D->D times.o D, quad epsilon:D->bold(1) $
满足余结合律与余单位律
$ (Delta times.o id) compose Delta=(id times.o Delta) compose Delta, $
$ (epsilon times.o id) compose Delta=id_D=(id times.o epsilon) compose Delta $
这里省略了结合与单位约束. 在无穷范畴中, 这些等式需要指定相容同伦, 并延伸到所有阶; 余交换结构还包含交换两个输出及其相容性.

定义末尾的 $opp$ 使余代数态射保持通常的方向. 例如 $f:D->D'$ 要与余乘法和余单位相容:
$ Delta' compose f=(f times.o f) compose Delta, quad epsilon' compose f=epsilon $

#example(title: [对角映射给出的余代数])[
  若 $cal(C)$ 的张量积是 Cartesian 积, 则每个对象 $X$ 都有典范的余交换结构
  $ Delta_X:X->X times X, quad epsilon_X:X->* $
  两种三重余乘法都是对角映射 $X->X times X times X$. 更高次相容性也由积的泛性质给出, 而且每个态射自动保持这些结构.

  特别地, 每个生象 $X$ 都是余交换余代数. 对称幺半函子 $Sigma_+^oo:(Ani,times,*)->(Sp,smash,SS)$ 将它送到谱中的余交换余代数:
  $ Sigma_+^oo X->Sigma_+^oo(X times X)
    tilde.eq Sigma_+^oo X smash Sigma_+^oo X $
  余单位由 $X->*$ 诱导.
]

#proposition(title: [可对偶对象上的代数与余代数])[
  记 $cal(C)^"dual"$ 为可对偶对象组成的对称幺半子范畴. 取对偶给出等价
  $ Alg(cal(C)^"dual")^opp tilde.eq cat("CoAlg")(cal(C)^"dual") $
  交换代数与余交换余代数之间也有同样的等价.
] <prop-algebra-coalgebra-duality>

#proof[
  可对偶对象满足自然等价
  $ (M times.o N)^or tilde.eq M^or times.o N^or, quad
    bold(1)^or tilde.eq bold(1), quad (M^or)^or tilde.eq M $
  因而取对偶是 $(cal(C)^"dual")^opp->cal(C)^"dual"$ 的对称幺半等价. 它把代数的乘法与单位变成
  $ Delta=mu^or:A^or->(A times.o A)^or tilde.eq A^or times.o A^or, $
  $ epsilon=eta^or:A^or->bold(1) $
  结合律对偶为余结合律, 单位律对偶为余单位律, 全部相容同伦也随函子一起传递. 再取一次对偶恢复原结构, 因而得到所述等价.
]

#example(title: [有限对偶与完美模])[
  取域 $k$ 和有限维 $k$-代数 $A$, 上述余乘法的具体公式是
  $ Delta(f)(a times.o b)=f(a b), quad epsilon(f)=f(1), quad f in A^or $
  例如对有限集合 $S$ 的函数代数 $k^S$, 记点值函数为 $delta_s$, 对偶基为 $e_s$, 则
  $ Delta(e_s)=e_s times.o e_s, quad epsilon(e_s)=1 $

  在交换环谱 $R$ 上, 可对偶模正是完美模, 所以上述命题也适用于底层 $R$-模完美的代数与余代数; 参见 @Lur17[第 4.6.1 节, 第 7.2.4 节]. 对任意无限维代数, 则不能直接将 $(A times.o A)^or$ 认作 $A^or times.o A^or$.
]

=== 双代数的定义

双代数同时带有代数与余代数结构, 并要求两种结构相容. 余代数的张量积由底层张量积给出, 余乘法先分别作用于两个因子, 再交换中间两个输出. 这使 $cat("CoAlg")(cal(C))$ 也成为对称幺半无穷范畴.

#definition(title: [双代数])[
  对称幺半 $oo$-范畴 $cal(C)$ 中的*双代数*是余代数范畴中的结合代数, 记
  $ cat("BiAlg")(cal(C)):=Alg(cat("CoAlg")(cal(C))) $
  换言之, 一个双代数 $B$ 有乘法, 单位, 余乘法与余单位, 且乘法和单位是余代数态射. 这些条件都包含全部相容同伦.

  若要求余交换, 则使用 $Alg(cat("CoCAlg")(cal(C)))$; 若再要求乘法交换, 则使用 $CAlg(cat("CoCAlg")(cal(C)))$.
] <def-bialgebra>

下面的计算先在普通 $k$-模范畴中进行, $k$ 是交换环, 张量积均在 $k$ 上取. 此时相容性等价于 $Delta$ 和 $epsilon$ 是含幺代数同态, 即
$ Delta(a b)=Delta(a) Delta(b), quad Delta(1)=1 times.o 1, $
$ epsilon(a b)=epsilon(a) epsilon(b), quad epsilon(1)=1 $
这里 $(a times.o b)(c times.o d)=a c times.o b d$. 例如第一条展开就是
$ Delta compose mu=(mu times.o mu) compose (id times.o tau times.o id) compose (Delta times.o Delta) $
其中 $tau$ 交换中间两个因子. 这也正是 $mu$ 保持余乘法的条件, 其余三条分别对应余单位与单位的相容性. 经典定义与例子可参见 @GR20[第 1.1--1.3 节].

#example(title: [幺半群代数与群代数])[
  对幺半群 $M$, 其代数 $k[M]$ 以 $[m]$ 为基, 乘法为 $[m][n]=[m n]$. 在基上定义
  $ Delta([m])=[m] times.o [m], quad epsilon([m])=1 $
  再作 $k$-线性延拓, 就得到余交换双代数. 余结合律的两边都把 $[m]$ 送到 $[m] times.o [m] times.o [m]$, 而
  $ Delta([m][n])=[m n] times.o [m n]=Delta([m]) Delta([n]) $
  其余单位条件也直接成立.

  群代数 $k[G]$ 是其中的典型例子. 在两个表示的张量积上, 这条余乘法正好给出熟悉的对角作用 $g(v times.o w)=g v times.o g w$.
]

#example(title: [多项式的加法余乘法])[
  在 $k[t]$ 上指定
  $ Delta(t)=t times.o 1+1 times.o t, quad epsilon(t)=0 $
  并要求 $Delta,epsilon$ 是含幺代数同态. 由多项式环的泛性质, 这唯一确定它们, 且
  $ Delta(t^n)=sum_(i=0)^n binom(n,i) t^i times.o t^(n-i) $
  例如 $Delta(t^2)=t^2 times.o 1+2 t times.o t+1 times.o t^2$. 余结合律只需在生成元 $t$ 上检查, 两边都得到
  $ t times.o 1 times.o 1+1 times.o t times.o 1+1 times.o 1 times.o t $
  余单位律也只需在 $t$ 上检查. 因而这是交换且余交换的双代数.

  将 $k[t] times.o k[t]$ 写成 $k[x,y]$, 余乘法就是 $f(t) mapsto f(x+y)$. 同一个多项式代数还可取 $Delta(t)=t times.o t$, $epsilon(t)=1$, 此时对应 $f(t) mapsto f(x y)$, 也就是幺半群代数 $k[NN]$ 的结构. 因此底层代数并不唯一决定余乘法.
]

#proposition(title: [双代数的表示可以取张量积])[
  若 $B$ 是普通 $k$-双代数, 则左 $B$-模范畴有自然的幺半结构, 底层张量积为 $V times.o_k W$, 单位为通过 $epsilon$ 获得作用的 $k$. 若 $B$ 余交换, 则这是对称幺半结构.
]

#proof[
  将余乘法简记为 $Delta(b)=sum b_((1)) times.o b_((2))$, 定义
  $ b dot (v times.o w):=sum (b_((1)) v) times.o (b_((2)) w) $
  $Delta$ 保持乘法和单位, 所以 $(b c) dot z=b dot (c dot z)$ 且 $1 dot z=z$, 确实给出模结构. 在三个模的张量积上, 两种加括号方式的作用分别由 $(Delta times.o id) Delta$ 和 $(id times.o Delta) Delta$ 给出; 余结合律保证通常的结合同构保持 $B$-作用. 余单位律同样保证左右单位同构保持 $B$-作用.

  若 $Delta$ 余交换, 交换因子 $v times.o w mapsto w times.o v$ 也保持 $B$-作用. 结合, 单位与对称约束的相容性由底层模范畴继承.
]

== 自同态的卷积 <sec-end-convolution>

设 $H$ 是对称幺半 $oo$-范畴 $(cal(C),times.o,bold(1))$ 中的双代数, 结构映射记为
$ mu:H times.o H->H, quad eta:bold(1)->H, quad
  Delta:H->H times.o H, quad epsilon:H->bold(1) $
下面在 $H$ 的自同态上构造一种乘法. 这一步只用到代数与余代数结构, 因而也适用于 Hopf 代数, 无需先使用对极.

#definition(title: [自同态的卷积])[
  记 $H$ 的底层自同态生象为
  $ op("End")_(cal(C))(H):=Map_(cal(C))(H,H) $
  这里的自同态是 $cal(C)$ 中的态射, 不要求保持代数或余代数结构. 对 $f,g:H->H$, 定义它们的*卷积*
  $ f star g:=mu compose (f times.o g) compose Delta $
  即复合
  $ H stretch(->)^Delta H times.o H
    stretch(->)^(f times.o g) H times.o H stretch(->)^mu H $
  同时记
  $ e:=eta compose epsilon:H->bold(1)->H $
  由于张量积与复合都作用于整个映射生象, 这给出自然的运算
  $ star:op("End")_(cal(C))(H) times op("End")_(cal(C))(H)
    ->op("End")_(cal(C))(H) $
] <def-end-convolution>

直观地, 先用 $Delta$ 将输入分成两路, 分别施加 $f$ 与 $g$, 再用 $mu$ 合并输出. 整个构造由给定的结构映射决定, 不需要选择基或对偶.

#proposition(title: [卷积的结合律与单位])[
  卷积使 $op("End")_(cal(C))(H)$ 典范成为 $Ani$ 中的 $EE_1$-代数, 即带相容同伦的幺半生象. 其单位为 $e=eta compose epsilon$, 因而
  $ (f star g) star h tilde.eq f star (g star h), quad
    e star f tilde.eq f tilde.eq f star e $
  对普通 $k$-双代数 $H$, 这使 $op("End")_k(H)=Hom_k(H,H)$ 成为含幺结合 $k$-代数. 经典版本参见 @GR20[定义 1.4.1].
] <prop-convolution-monoid>

#proof[
  先看结合律. 乘法的结合性与余乘法的余结合性给出相容的三重运算
  $ mu_3:=mu compose (mu times.o id) tilde.eq mu compose (id times.o mu), $
  $ Delta_3:=(Delta times.o id) compose Delta
    tilde.eq (id times.o Delta) compose Delta $
  展开卷积, 两种加括号方式都等价于同一个复合:
  $ (f star g) star h
    tilde.eq mu_3 compose (f times.o g times.o h) compose Delta_3
    tilde.eq f star (g star h) $
  再由单位律与余单位律,
  $ e star f=mu compose (eta times.o id) compose (epsilon times.o f) compose Delta tilde.eq f, $
  $ f star e=mu compose (id times.o eta) compose (f times.o epsilon) compose Delta tilde.eq f $
  这里省略了单位约束; 例如 $(epsilon times.o f) compose Delta$ 在余单位约束下就是 $f$.

  为了同时得到全部高阶相容性, 考虑典范的 lax 对称幺半函子
  $ Map_(cal(C)):cal(C)^opp times cal(C)->Ani $
  其幺半结构由张量映射给出:
  $ Map_(cal(C))(X,Y) times Map_(cal(C))(X',Y')
    ->Map_(cal(C))(X times.o X',Y times.o Y') $
  它将 $(f,g)$ 送到 $f times.o g$, 单位由 $id_(bold(1))$ 给出. $H$ 的余代数结构是 $cal(C)^opp$ 中的代数结构, 与第二个因子中的代数 $H$ 一起, 给出乘积范畴中的 $EE_1$-代数. 沿这个 lax 对称幺半函子取像, 就得到上述卷积及其全部相容同伦.

  普通模情形下, 上述同伦等式就是普通等式. 卷积还对两个输入分别 $k$-线性, 因而得到所述结合代数.
]

#example(title: [群代数上的卷积])[
  对普通双代数, 用 Sweedler 记号 $Delta(x)=sum x_((1)) times.o x_((2))$, 卷积就是
  $ (f star g)(x)=sum f(x_((1))) g(x_((2))), quad e(x)=epsilon(x) 1_H $
  例如 $H=k[G]$ 时, 在基元素 $[a]$ 上有
  $ (f star g)([a])=f([a]) g([a]), quad e([a])=1_H $
  所以 $(id_H star id_H)([a])=[a^2]$. 与之相比, $(id_H compose id_H)([a])=[a]$. 复合以 $id_H$ 为单位, 卷积以 $e$ 为单位.
]

#remark(title: [内部自同态对象上的卷积])[
  若 $cal(C)$ 闭对称幺半, 还可以把上述构造放到内部自同态对象
  $ E:=underline(Hom)_(cal(C))(H,H) $
  上. 记评价为 $op("ev"):E times.o H->H$. 卷积乘法 $m_star:E times.o E->E$ 是下列复合在张量与内部 Hom 伴随下对应的态射:
  $ E times.o E times.o H
    stretch(->)^(id times.o id times.o Delta)
    E times.o E times.o H times.o H $
  $ tilde.eq (E times.o H) times.o (E times.o H)
    stretch(->)^(op("ev") times.o op("ev"))
    H times.o H stretch(->)^mu H $
  中间的等价交换第二个 $E$ 与第一个 $H$. 单位 $bold(1)->E$ 对应 $e:H->H$. 同样的结合律与余结合律使 $E$ 成为 $cal(C)$ 中的 $EE_1$-代数, 取 $Map_(cal(C))(bold(1),-)$ 后恢复前面的卷积.

  例如对交换环谱 $R$, 在 $Mod_R$ 中的 $E$ 是内部 $R$-模 Hom, 因而卷积给出一个结合 $R$-代数. 这不要求 $H$ 完美或可对偶.
]

这个卷积结构使我们可以用逆元来表述 Hopf 条件.

== Hopf 代数的定义与性质

=== 定义与态射

Hopf 代数同时具有代数与余代数结构. 两种结构要满足双代数的相容性, 还要满足一个额外的可逆性条件.

#definition(title: [Hopf 代数与对极])[
  设 $cal(C)$ 是对称幺半 $oo$-范畴. 一个 *Hopf 代数*首先是双代数 $H in cat("BiAlg")(cal(C))$: $(H,mu,eta)$ 是结合代数, $(H,Delta,epsilon)$ 是余结合余代数, 且 $mu,eta$ 是余代数态射.

  此外, 要求 $id_H$ 在卷积幺半生象 $op("End")_(cal(C))(H)$ 中可逆, 即它在幺半群 $pi_0 op("End")_(cal(C))(H)$ 中的类可逆. 其卷积逆
  $ S:H->H $
  称为*对极* (antipode). 它满足
  $ mu compose (S times.o id_H) compose Delta
    tilde.eq eta compose epsilon
    tilde.eq mu compose (id_H times.o S) compose Delta $
  也就是 $S star id_H tilde.eq e tilde.eq id_H star S$. 逆元及其相容性按 $EE_1$-幺半生象中的逆元理解.
] <def-hopf-algebra>

因此, 只在一个对象上分别给出乘法与余乘法还不够. 双代数相容性把两者联系起来, Hopf 条件则要求 $id_H$ 的卷积逆存在. 定义并不要求乘法交换或余乘法余交换. 普通情形下, 它正是 @GR20[定义 1.4.6]:
$ sum S(x_((1))) x_((2))=epsilon(x) 1_H
  =sum x_((1)) S(x_((2))) $

#proposition(title: [对极的唯一性])[
  给定一个 Hopf 代数的双代数结构, 对极连同完整相容逆数据的选择生象可缩. 特别地, 普通 Hopf 代数的对极唯一.
] <prop-antipode-unique>

#proof[
  若 $S,T$ 都是 $id_H$ 的卷积逆, 则
  $ S tilde.eq S star (id_H star T)
    tilde.eq (S star id_H) star T tilde.eq T $
  更准确地, 与可逆元素 $id_H$ 作卷积是整个自同态生象上的等价. 它在单位 $e$ 上的同伦纤维可缩, 因而指定逆元及相容逆数据没有额外的选择. 普通情形下, 上面的同伦等式就是等式.
]

#definition(title: [Hopf 代数的无穷范畴])[
  记 Hopf 代数组成的无穷范畴为
  $ cat("Hopf")(cal(C)) subset.eq cat("BiAlg")(cal(C)) $
  它由满足 @def-hopf-algebra 的双代数构成, 映射生象直接取
  $ Map_(cat("Hopf")(cal(C)))(H,K)
    :=Map_(cat("BiAlg")(cal(C)))(H,K) $

  因而一个 *Hopf 代数态射*是双代数态射 $f:H->K$. 它同时保持乘法, 单位, 余乘法与余单位:
  $ f compose mu_H tilde.eq mu_K compose (f times.o f), quad
    f compose eta_H tilde.eq eta_K, $
  $ Delta_K compose f tilde.eq (f times.o f) compose Delta_H, quad
    epsilon_K compose f tilde.eq epsilon_H $
  这些相容性包含双代数态射的全部高阶数据. 态射之间的同伦及更高次同伦也从双代数范畴继承.
] <def-hopf-infinity-category>

态射的定义中没有另加一条对极条件, 因为它会自动成立.

#proposition(title: [Hopf 态射的基本性质])[
  对任意 Hopf 代数态射 $f:H->K$, 有自然的相容同伦
  $ f compose S_H tilde.eq S_K compose f $
  而且 $f$ 是 $cat("Hopf")(cal(C))$ 中的等价, 当且仅当底层态射在 $cal(C)$ 中是等价. 普通情形下的对极相容性见 @GR20[推论 1.4.27].
] <prop-hopf-morphism-antipode>

#proof[
  卷积同样可以定义在从余代数 $D$ 到代数 $A$ 的映射生象上:
  $ a star b:=mu_A compose (a times.o b) compose Delta_D, quad
    e_(D,A):=eta_A compose epsilon_D $
  前一节的结合律与单位律证明原样适用. 沿代数态射作后复合, 或沿余代数态射作预复合, 都保持这个卷积与单位.

  现在取 $D=H$, $A=K$. 因为 $f$ 保持代数结构, $f compose S_H$ 是 $f$ 的卷积逆; 因为 $f$ 保持余代数结构, $S_K compose f$ 也是 $f$ 的卷积逆. 逆元的唯一性给出所述相容同伦, 并保证它们对态射及其复合相容.

  最后, 代数与余代数的忘却函子都检测等价, 所以双代数态射是等价当且仅当底层态射是等价. 两端都是 Hopf 代数时, 这也正是 Hopf 范畴中的等价.
]

=== 对极与基本构造

#theorem(title: [对极反转乘法与余乘法])[
  设 $H$ 是 Hopf 代数, $tau:H times.o H->H times.o H$ 是交换两个因子的对称约束. 则
  $ S compose eta tilde.eq eta, quad epsilon compose S tilde.eq epsilon, $
  $ S compose mu tilde.eq mu compose tau compose (S times.o S), $
  $ Delta compose S tilde.eq tau compose (S times.o S) compose Delta $
  普通情形下, 对极是代数反同态与余代数反同态. 特别有
  $ S(1)=1, quad S(a b)=S(b) S(a) $
  参见 @GR20[命题 1.4.10, 习题 1.4.28].
] <thm-antipode-antimultiplicative>

#proof[
  单位对象 $bold(1)$ 的典范双代数结构以 $id_(bold(1))$ 为对极. 由于 $eta$ 和 $epsilon$ 都是双代数态射, @prop-hopf-morphism-antipode 给出前两个等价.

  在 $Map_(cal(C))(H times.o H,H)$ 上取卷积, 并记
  $ u:=id_H times.o epsilon, quad v:=epsilon times.o id_H $
  这里用单位约束将它们的目标识别为 $H$. 两者都是余代数态射, 且余单位律给出 $u star v tilde.eq mu$. 因而 $S compose u$ 与 $S compose v$ 分别是 $u,v$ 的卷积逆.

  双代数相容性又说明 $mu$ 是余代数态射, 所以 $S compose mu$ 是 $mu$ 的卷积逆. 乘积的逆要反转顺序, 因而
  $ S compose mu
    tilde.eq (S compose v) star (S compose u)
    tilde.eq mu compose tau compose (S times.o S) $
  最后一个等价只需展开卷积并使用两次余单位律; 在普通模中, 它把 $a times.o b$ 送到 $S(b) S(a)$.

  将上述论证的所有箭头反向, 就得到余乘法的公式. 这里使用反范畴, 不要求 $H$ 有线性对偶.
]

#corollary(title: [交换或余交换时的对极])[
  若 $H$ 的乘法交换, 或余乘法余交换, 则对极满足
  $ S compose S tilde.eq id_H $
  因而此时 $S$ 也是底层对象的自等价.
]

#proof[
  若乘法交换, 上述定理使 $S$ 保持乘法和单位, 所以后复合 $S$ 保持卷积. 对两个对极恒等式作后复合, 得到
  $ (S compose S) star S tilde.eq e tilde.eq S star (S compose S) $
  所以 $S compose S$ 与 $id_H$ 都是 $S$ 的卷积逆, 由唯一性得到结论. 余交换情形对偶地使用预复合 $S$, 以及 $epsilon compose S tilde.eq epsilon$.
]

#proposition(title: [张量积与换系数])[
  $cat("Hopf")(cal(C))$ 继承对称幺半结构. 单位为 $bold(1)$, 两个 Hopf 代数的张量积仍为 Hopf 代数, 且
  $ S_(H times.o K) tilde.eq S_H times.o S_K $
  任意强对称幺半函子 $F:cal(C)->cal(D)$ 都诱导
  $ cat("Hopf")(cal(C))->cat("Hopf")(cal(D)), quad H mapsto F(H) $
  并将对极送到 $F(S_H)$.
]

#proof[
  对张量积双代数展开卷积, 对称约束给出
  $ (a times.o b) star (c times.o d)
    tilde.eq (a star c) times.o (b star d) $
  因而 $S_H times.o S_K$ 是 $id_H times.o id_K$ 的双侧卷积逆. 张量积的结合, 单位与对称约束均继承自双代数范畴.

  强对称幺半函子保持乘法, 余乘法及其相容性, 也把对极恒等式送到对应的恒等式, 所以保持 Hopf 条件.
]

例如对交换环谱态射 $R->R'$, 扩张标量 $R' times.o_R -$ 是强对称幺半函子, 因而
$ H mapsto R' times.o_R H $
把 $R$ 上的 Hopf 代数送到 $R'$ 上的 Hopf 代数. 此外, 若 $H$ 的底层对象可对偶, @prop-algebra-coalgebra-duality 将它的代数与余代数结构互换, 对极恒等式随之对偶, 所以 $H^or$ 仍是 Hopf 代数, 对极为 $S_H^or$.

=== 例子与连通分次情形

#example(title: [群代数与多项式])[
  取非零普通交换环 $k$. 群代数 $k[G]$ 的对极由
  $ S([g])=[g^(-1)] $
  作 $k$-线性延拓得到. 两个对极恒等式在基上分别是 $[g^(-1)][g]=1$ 和 $[g][g^(-1)]=1$. 群同态 $G->G'$ 的线性延拓给出 Hopf 代数态射 $k[G]->k[G']$.

  对带加法余乘法的 $k[t]$, 取 $S(t)=-t$, 并作代数延拓, 即 $S(q(t))=q(-t)$. 由于 $Delta(q(t))=q(x+y)$, 有
  $ (S star id)(q(t))=q(-t+t)=q(0)=(eta compose epsilon)(q(t)) $
  另一侧同样成立, 所以这是 Hopf 代数.

  对同一个代数取乘法余乘法 $Delta(t)=t times.o t$, $epsilon(t)=1$ 时, 对极条件却要求 $S(t)t=1$, 而 $t$ 在 $k[t]$ 中不可逆. 因而这个双代数不是 Hopf 代数. 将 $t$ 取逆后得到 $k[t,t^(-1)]$, 对极为 $S(t)=t^(-1)$.
]

#example(title: [有限群上的函数])[
  设 $k$ 是域, $G$ 是有限群. 有限对偶将 $k[G]$ 变成函数 Hopf 代数 $k^G$, 其乘法逐点计算, 并有
  $ (Delta f)(g,h)=f(g h), quad epsilon(f)=f(1_G), quad (S f)(g)=f(g^(-1)) $
  它的乘法总是交换的; 余乘法余交换当且仅当 $G$ 交换. 这与群代数的情形相对: $k[G]$ 总是余交换, 但乘法未必交换.
]

最后给出一个常用的存在性定理. 这里回到普通模范畴, 使用普通双代数上的非负分次.

#theorem(title: [连通分次双代数自动是 Hopf 代数])[
  设 $k$ 是交换环, $H=plus.o.big_(n>=0) H_n$ 是分次 $k$-双代数. 乘法与余乘法满足
  $ H_i H_j subset.eq H_(i+j), quad
    Delta(H_n) subset.eq plus.o.big_(i+j=n) H_i times.o_k H_j $
  单位与余单位也保持分次, 且 $eta:k->H_0$ 是同构. 这个条件称为*分次连通*.

  则 $H$ 有唯一对极. 记 $e=eta compose epsilon$, $p=id_H-e$, 它由卷积级数给出:
  $ S=sum_(r>=0) (-1)^r p^(star r), quad p^(star 0):=e $
  每个元素上只有有限项非零. 参见 @GR20[命题 1.4.16, 1.4.24].
] <thm-connected-graded-hopf>

#proof[
  $p$ 在 $H_0$ 上为零, 在正次部分为恒等. 记 $mu_r,Delta_r$ 为 $r$ 重乘法与余乘法, 则对 $r>=1$ 有
  $ p^(star r)=mu_r compose p^(times.o r) compose Delta_r $
  对 $x in H_n$, $Delta_r(x)$ 的各个分量位于总次数为 $n$ 的 $r$ 重张量积中. 若 $r>n$, 至少一个因子的次数为零, 施加 $p^(times.o r)$ 后就消失. 因而 $p^(star r)(x)=0$, 上面的级数确实逐元素有限.

  由于 $id_H=e+p$, 有限几何级数的消去给出
  $ (e+p) star sum_(r>=0) (-1)^r p^(star r)=e
    =sum_(r>=0) (-1)^r p^(star r) star (e+p) $
  所以这个 $S$ 是 $id_H$ 的双侧卷积逆. 唯一性由 @prop-antipode-unique 得到. 各项都保持分次, 故对极也保持分次.
]

例如把加法余乘法的 $k[t]$ 按 $deg(t)=1$ 分次, 就满足这个定理. 乘法余乘法 $Delta(t)=t times.o t$ 的总次数为 $2$, 不满足定理中的分次条件.
