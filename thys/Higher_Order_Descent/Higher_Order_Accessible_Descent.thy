theory Higher_Order_Accessible_Descent
  imports "Higher_Order_Accessible.Higher_Order_Accessible_Schema"
begin

context ho_source_accessible_reducibility
begin

definition candidate_descent where
  "candidate_descent n u t = (ho_step S V R B t u \<or>
    access.accessible_step n (access.candidate_slice n (access.candidate_lower n)
      (access.candidate_level n (access.candidate_lower n))) t u)"

lemma candidate_descent_SN:
  assumes comp: "source_candidate T t"
  shows "Wellfounded.accp (candidate_descent n) t"
proof (cases "\<exists>b. T=HBase b \<and> rank b=n")
  case True
  then obtain b where eq: "T=HBase b" and level: "rank b=n" by blast
  have cb: "source_candidate (HBase b) t" using comp eq by simp
  show ?thesis using source_candidate_extended_SN[OF cb, of n] level
    by (simp add: candidate_descent_def[abs_def])
next
  case False
  have ty: "ho_typeof S V B t=Some T" by (rule source.candidate_typed[OF comp])
  have sn: "source.strongly_normalizing t" by (rule source.candidate_SN[OF comp])
  show ?thesis using sn ty
  proof (induction t rule: accp.induct)
    case (accI t)
    show ?case
    proof (rule accp.accI)
      fix u assume st: "candidate_descent n u t"
      have step: "ho_step S V R B t u"
        using st accI.prems False unfolding candidate_descent_def access.accessible_step_def by auto
      have ut: "ho_typeof S V B u=Some T" by (rule ho_zero_arity_step_type[OF step zero accI.prems])
      show "Wellfounded.accp (candidate_descent n) u" by (rule accI.IH[OF step ut])
    qed
  qed
qed

definition candidate_terminating_descent where
  "candidate_terminating_descent n = {(u,t). Wellfounded.accp (candidate_descent n) t \<and> candidate_descent n u t}"

lemma wf_candidate_terminating_descent: "wf (candidate_terminating_descent n)"
proof -
  let ?r = "\<lambda>u t. Wellfounded.accp (candidate_descent n) t \<and> candidate_descent n u t"
  have acc: "Wellfounded.accp ?r t" for t
  proof (cases "Wellfounded.accp (candidate_descent n) t")
    case True
    then show ?thesis by (induction t rule: accp.induct) (auto intro: accp.accI)
  next
    case False
    show ?thesis by (rule accp.accI) (use False in auto)
  qed
  have "wfp ?r" by (rule accp_wfpI) (simp add: acc)
  then show ?thesis by (simp add: wfp_def candidate_terminating_descent_def)
qed

definition accessible_call_order where
  "accessible_call_order n prec priority =
    inv_image (less_than <*lex*> lex ((candidate_terminating_descent n)\<^sup>+))
      (\<lambda>(c,xs). (prec c,ho_priority_arguments priority xs))"

lemma wf_accessible_call_order: "wf (accessible_call_order n prec priority)"
  unfolding accessible_call_order_def
  by (intro wf_inv_image wf_lex_prod wf_less_than wf_lex wf_trancl wf_candidate_terminating_descent)

lemma accessible_argument_step_order:
  assumes args: "list_all2 source_candidate Ts xs" and step: "ho_arguments_step S V R B xs ys"
  shows "((c,ys),(c,xs))\<in>accessible_call_order n prec priority"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain A where cv: "source_candidate A v"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have small: "(w,v)\<in>candidate_terminating_descent n"
    using candidate_descent_SN[OF cv, of n] vw
    by (simp add: candidate_terminating_descent_def candidate_descent_def)
  have index: "length us<length xs" and at: "xs!length us=v" and update: "ys=xs[length us:=w]"
    by (simp_all add: xs ys list_update_append)
  have lex: "(ho_priority_arguments priority ys,ho_priority_arguments priority xs)\<in>lex ((candidate_terminating_descent n)\<^sup>+)"
    unfolding update by (rule ho_priority_arguments_update[OF index]) (use r_into_trancl[OF small] at in simp)
  show ?thesis using lex by (simp add: accessible_call_order_def inv_image_def lex_prod_def)
qed

end

end
