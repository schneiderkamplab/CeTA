theory LP_Answer_Post_Actual
 imports LP_Scoped_Answer_Composition
begin

text \<open>Changing a module's output contract requires a bridge for actual
successful returns, independently of its termination argument.\<close>

lemma lp_answer_contract_post_actual:
 assumes contract: "lp_answer_contract T ss R t ret"
 and post: "\<And>eta. lp_actual_answer T ss eta \<Longrightarrow> (ret eta,final eta)\<in>R\<^sup>*"
 shows "lp_answer_contract T ss R t final"
 using contract post
 unfolding lp_answer_contract_def lp_answers_covered_def lp_actual_answer_def
 by (meson rtrancl_trans)

lemma lp_answer_contract_reject_uncovered_return:
 assumes actual: "lp_actual_answer T ss eta"
 and missing: "(t,final eta)\<notin>R\<^sup>*"
 shows "\<not>lp_answer_contract T ss R t final"
proof
 assume contract: "lp_answer_contract T ss R t final"
 have "(t,final eta)\<in>R\<^sup>*"
  by (rule lp_actual_answer_covered[OF contract actual])
 then show False using missing by simp
qed

end
