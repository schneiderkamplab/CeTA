theory LP_Prolog_Equation_Congruence
 imports LP_Prolog_Evaluation_Context
begin

definition lpp_check_context_equation_rewrite where
  "lpp_check_context_equation_rewrite context a b =
    (a=b \<or> (\<exists>observation\<in>set (snd (snd context)). case observation of
       LPPOEquation s t \<Rightarrow> lp_equation_replace s t a=b \<or> lp_equation_replace t s a=b
     | _ \<Rightarrow> False))"

lemma lpp_context_equation_rewrite_sound:
  assumes checked: "lpp_check_context_equation_rewrite source_context a b"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
  shows "lp_ieval a eta=lp_ieval b eta"
proof -
  have equal: "lp_ieval s eta=lp_ieval t eta"
    if "LPPOEquation s t\<in>set (snd (snd source_context))" for s t
    using observed that by (cases source_context)
      (auto simp: lpp_evaluation_context_holds_def list_all_iff)
  show ?thesis
  proof (cases "a=b")
    case True then show ?thesis by simp
  next
    case False
    obtain observation where member: "observation\<in>set (snd (snd source_context))"
      and usable: "(case observation of LPPOEquation s t \<Rightarrow>
        lp_equation_replace s t a=b \<or> lp_equation_replace t s a=b | _ \<Rightarrow> False)"
      using checked False by (auto simp: lpp_check_context_equation_rewrite_def)
    obtain s t where shape: "observation=LPPOEquation s t"
      and replacement: "lp_equation_replace s t a=b \<or> lp_equation_replace t s a=b"
      using usable by (cases observation) auto
    have eq: "lp_ieval s eta=lp_ieval t eta" using equal member shape by blast
    have forward: "lp_ieval (lp_equation_replace s t a) eta=lp_ieval a eta"
      by (rule lp_equation_replace_eval[OF eq])
    have backward: "lp_ieval (lp_equation_replace t s a) eta=lp_ieval a eta"
      by (rule lp_equation_replace_eval[OF eq[symmetric]])
    show ?thesis using replacement forward backward by auto
  qed
qed

lemma lpp_context_equation_rewrite_requires_initialization:
  "a\<noteq>b \<Longrightarrow> \<not>lpp_check_context_equation_rewrite (facts,guards,[]) a b"
  by (simp add: lpp_check_context_equation_rewrite_def)

end
