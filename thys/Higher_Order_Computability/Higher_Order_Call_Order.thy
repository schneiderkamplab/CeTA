theory Higher_Order_Call_Order
  imports Higher_Order_Call_Reduction
begin

context ho_source_neutral_reducibility
begin

definition terminating_descent where
  "terminating_descent={(u,t). Wellfounded.accp application_descent t \<and> application_descent u t}"

lemma wf_terminating_descent: "wf terminating_descent"
proof -
  let ?r = "\<lambda>u t. Wellfounded.accp application_descent t \<and> application_descent u t"
  have acc: "Wellfounded.accp ?r t" for t
  proof (cases "Wellfounded.accp application_descent t")
    case True
    then show ?thesis by (induction t rule: accp.induct) (auto intro: accp.accI)
  next
    case False
    show ?thesis by (rule accp.accI) (use False in auto)
  qed
  have "wfp ?r" by (rule accp_wfpI) (simp add: acc)
  then show ?thesis by (simp add: wfp_def terminating_descent_def)
qed

definition call_order :: "(nat \<Rightarrow> nat) \<Rightarrow> ((nat \<times> ho_term list) \<times> (nat \<times> ho_term list)) set" where
  "call_order rank=inv_image (less_than <*lex*> lex (terminating_descent\<^sup>+))
    (\<lambda>(c,xs). (rank c,xs))"

lemma wf_call_order: "wf (call_order rank)"
  unfolding call_order_def by (intro wf_inv_image wf_lex_prod wf_less_than wf_lex wf_trancl wf_terminating_descent)

lemma computable_arguments_step:
  assumes args: "list_all2 source.computable Ts xs" and step: "ho_arguments_step S V R B xs ys"
  shows "list_all2 source.computable Ts ys"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain As A Bs where ts: "Ts=As@A#Bs" and pre: "list_all2 source.computable As us"
    and cv: "source.computable A v" and post: "list_all2 source.computable Bs vs"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have cw: "source.computable A w" by (rule source.computable_reduction[OF cv vw])
  show ?thesis unfolding ts ys using pre cw post by (auto intro: list_all2_appendI)
qed

lemma argument_step_call_order:
  assumes args: "list_all2 source.computable Ts xs" and step: "ho_arguments_step S V R B xs ys"
  shows "((c,ys),(c,xs))\<in>call_order rank"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain A where cv: "source.computable A v"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have small: "(w,v)\<in>terminating_descent"
    using computable_application_descent[OF cv] vw
    by (simp add: terminating_descent_def application_descent_def)
  have lex: "(ys,xs)\<in>lex (terminating_descent\<^sup>+)"
    using r_into_trancl[OF small] unfolding xs ys lex_conv by auto
  show ?thesis using lex by (simp add: call_order_def inv_image_def lex_prod_def)
qed

end

lemma ho_apply_terms_type:
  assumes ty: "ho_typeof S V B f=Some A"
    and args: "list_all2 (\<lambda>T x. ho_typeof S V B x=Some T) (ho_argument_types A) xs"
  shows "ho_typeof S V B (ho_apply_terms f xs)=Some (HBase (ho_result_sort A))"
  using ty args
proof (induction A arbitrary: f xs)
  case (HBase b)
  then show ?case by simp
next
  case (HArrow A C)
  obtain x ys where xs: "xs=x#ys" and xt: "ho_typeof S V B x=Some A"
    and ys: "list_all2 (\<lambda>T x. ho_typeof S V B x=Some T) (ho_argument_types C) ys"
    using HArrow.prems(2) by (auto simp: list_all2_Cons1)
  have ft: "ho_typeof S V B (HApp f x)=Some C" using HArrow.prems(1) xt by simp
  show ?case using HArrow.IH(2)[OF ft ys] by (simp add: xs)
qed

end
