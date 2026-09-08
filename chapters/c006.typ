#import "../template.typ":*
#import "@preview/cetz:0.4.1"
#import "@preview/fletcher:0.5.8" :*

#show: doc => conf(
  easy: true,
  doc,
)

= 拟凝聚层 / Quasi-coherent Sheaves

== 拟凝聚层的定义

拟凝聚层是刻画几何对象上线性代数数据的工具.

=== Grothendieck 构造与拉直

一个函子 $F:C->Cat_oo$ 给每个 $c$ 指定一个范畴 $F(c)$. *Grothendieck 构造*把它们合成一个总范畴及投影:
$ E:=integral_C F, quad p:E->C $
对象是 $(c,x)$, 其中 $x in F(c)$; 态射是 $f:c->d$ 连同 $F(f)(x)->y$, 并保留全部相容同伦. 投影的纤维就是 $F(c)$. 总范畴也称为*元素的无穷范畴* (∞-category of elements).

从 $F$ 构造这样的投影叫*反拉直* (unstraightening); 反过来, 从投影读出纤维及沿箭头的运输, 叫*拉直* (straightening). 这里的投影是 coCartesian 纤维化, 两个过程互为等价. 若 $F$ 取值于 $Ani$, 对应的是左纤维化. 反变函子则对应 Cartesian 纤维化, 生象值时对应右纤维化. 参见 @Lur09[第 3.2 节], @Ker26[第 5.6 节].

后面只需记住两个事实: *换基* $u:D->C$ 对应预合成 $F compose u$; *取极限*对应相容地选择各层对象 $x_c in F(c)$, 连同等价 $F(f)(x_c) tilde.eq x_d$ 及其全部相容同伦. 参见 @Lur09[第 3.2.1 节, 第 3.3.3 节].

=== 一般定义

回顾 @def-ani-sheaf. 现在固定一个交换环谱 $Lambda$, 定义*交换 $Lambda$-代数的 $oo$-范畴*
$ CAlg_Lambda tilde.eq CAlg(Sp)_(Lambda \/) $
也就是说, 一个 $Lambda$-代数是一个交换环谱 $A$ 连同一个环谱同态 $Lambda->A$. 我们把 $CAlg_Lambda^opp$ 看作仿射测试对象的范畴. 下面说的一个*预层*, 是指一个*可达* (@def-accessible-functor, 由于 $CAlg_Lambda, Ani$ 都可呈示, 这个定义是合理的) 的函子
$ cal(F): CAlg_Lambda->Ani $
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
$ f^*:Mod_A->Mod_B, quad m mapsto B⊗_A m $
就得到图表 $J_(cal(F))->Cat_oo$.

#definition(title: "拟凝聚层")[
  预层 $cal(F):CAlg_Lambda->Ani$ 上的*拟凝聚层范畴*定义为
  $ QCoh(cal(F)):=varprojlim((A,x) in J_(cal(F))) Mod_A $
  这里在足够大宇宙的 $Cat_oo$ 中取极限. 它的对象称为 $cal(F)$ 上的*拟凝聚层* (quasi-coherent sheaf). 参见 @Lur11DAG8[定义 2.7.8, 注 2.7.9].
] <def-qcoh-prestack>

#remark(title: "这个极限怎样取")[
  一个对象就是一族模 $m_(A,x) in Mod_A$, 连同对每个 $(f,gamma):(A,x)->(B,y)$ 指定的等价
  $ theta_(f,gamma):B⊗_A m_(A,x) stretch(->)^tilde m_(B,y) $
  它们对恒等、复合及全部高阶同伦相容. 例如沿 $A->B->C$ 连做两次换系数, 应与直接沿 $A->C$ 换系数相容, 使用自然等价
  $ C⊗_B (B⊗_A m_(A,x)) tilde.eq C⊗_A m_(A,x) $
  态射则是一族相容的模映射, 同样带有相容同伦. 所以取这个极限, 就是在所有测试点上选择模, 并使它们随基变换一致. 参见 @Lur11DAG8[注 2.7.12].
]

#example(title: "仿射情形怎样计算")[
  若 $cal(F)=Spec R$, 则 $cal(F)(A)=Map_(CAlg_Lambda) (R,A)$. 此时 $J_(cal(F))$ 就是 $R$-代数范畴, 有始对象 $(R,id_R)$. 因而整个相容族由这里的一个 $R$-模 $m$ 决定:
  $ m_(A,x) tilde.eq A⊗_R m, quad x:R->A $
  在始对象处取值与上述扩张标量构造互逆, 从而
  $ QCoh(Spec R) tilde.eq Mod_R $
  例如 $m=R$ 时, 每个测试点上的值就是 $A$; 沿 $A->B$ 的相容等价为 $B⊗_A A tilde.eq B$.
]
