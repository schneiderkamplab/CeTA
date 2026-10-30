theory LP_Return_Shapes_Test
  imports LP_Return_Shapes
begin

definition lprs_spine :: "nat lp_return_grammar" where
  "lprs_spine = [[(0,[]),(1,[LPReturnAny,LPReturnShape 0])]]"

definition lprs_keyed :: "nat lp_return_grammar" where
  "lprs_keyed = [[(0,[]),(1,[LPReturnShape 1,LPReturnShape 0])],
    [(2,[LPReturnGround,LPReturnAny])]]"

lemma lprs_empty:
  "lp_return_shape_holds lprs_spine (LPReturnShape 0) (LPIFun 0 [])"
  by (rule lp_return_shape_holds.node[where shapes="[]"])
    (simp_all add: lprs_spine_def)

lemma lprs_arbitrary_head:
  "lp_return_shape_holds lprs_spine (LPReturnShape 0) (LPIFun 1 [h,LPIFun 0 []])"
proof (rule lp_return_shape_holds.node[where shapes="[LPReturnAny,LPReturnShape 0]"])
  show "0<length lprs_spine" by (simp add: lprs_spine_def)
  show "(1,[LPReturnAny,LPReturnShape 0])\<in>set (lprs_spine!0)" by (simp add: lprs_spine_def)
  show "length [LPReturnAny,LPReturnShape 0]=length [h,LPIFun 0 []]" by simp
  fix j assume "j<length [h,LPIFun 0 []]"
  then have "j=0 \<or> j=1" by auto
  then show "lp_return_shape_holds lprs_spine ([LPReturnAny,LPReturnShape 0]!j) ([h,LPIFun 0 []]!j)"
    using lprs_empty by (auto intro: lp_return_shape_holds.any)
qed

lemma lprs_keyed_constructor:
  "lp_return_shape_check 4 lprs_keyed [(LPReturnGround,0::nat),(LPReturnShape 0,1)]
    (LPReturnShape 0) (Fun 1 [Fun 2 [Var 0,Var 2],Var 1])"
  by (simp add: lprs_keyed_def eval_nat_numeral)

lemma lprs_missing_key_groundness:
  "\<not>lp_return_shape_check 4 lprs_keyed [(LPReturnShape 0,1::nat)]
    (LPReturnShape 0) (Fun 1 [Fun 2 [Var 0,Var 2],Var 1])"
  by (simp add: lprs_keyed_def eval_nat_numeral)

lemma lprs_cyclic_spine_rejected:
  assumes held: "lp_return_shape_holds lprs_spine shape t"
  shows "shape=LPReturnShape 0 \<Longrightarrow> t=LPIFun 1 [h,t] \<Longrightarrow> False"
  using held
proof (induct rule: lp_return_shape_holds.induct)
  case (any t) then show ?case by simp
next
  case (ground t) then show ?case by simp
next
  case (node i f shapes ts)
  have i: "i=0" using node.prems(1) by simp
  have f: "f=1" and eq: "ts=[h,LPIFun f ts]"
    using node.prems(2) by auto
  have length: "length ts=2" using arg_cong[OF eq, of length] by simp
  have tail: "ts!1=LPIFun f ts" using arg_cong[OF eq, of "\<lambda>xs. xs!1"] by simp
  have shapes: "shapes=[LPReturnAny,LPReturnShape 0]"
    using node.hyps(2) i f by (simp add: lprs_spine_def)
  have impossible: "ts!1 \<noteq> LPIFun 1 [h,ts!1]"
    using node.hyps(5)[of 1] length shapes by auto
  show ?case using impossible node.prems(2) tail by metis
qed

end
