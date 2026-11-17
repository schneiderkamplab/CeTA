theory LP_Answer_Invariant_Refinement
 imports LP_Answer_Contracts
begin

text \<open>Refinement on a checked reachable invariant. The invariant is
initialized and preserved by every actual source transition, including failure
and later answers. No closure under arbitrary replacement of goal frames is
assumed. Both termination and all successful returns are transported.\<close>

lemma lp_answer_contract_invariant_refinement:
 assumes initial: "I ss"
   and preserved: "\<And>xs event ys. I xs \<Longrightarrow> T xs event ys \<Longrightarrow> I ys"
   and refines: "\<And>xs event ys. I xs \<Longrightarrow> T xs event ys \<Longrightarrow> U xs event ys"
   and contract: "lp_answer_contract U ss R t ret"
 shows "lp_answer_contract T ss R t ret"
proof -
 have reflect: "I xs \<longrightarrow> SN_on (lp_answer_steps T) {xs}"
   if sn: "SN_on (lp_answer_steps U) {xs}" for xs
 proof (rule SN_on_induct[OF sn singletonI], intro impI)
  fix xs
  assume ih: "\<And>ys. (xs,ys)\<in>lp_answer_steps U \<Longrightarrow>
    I ys \<longrightarrow> SN_on (lp_answer_steps T) {ys}"
    and inv: "I xs"
  show "SN_on (lp_answer_steps T) {xs}"
  proof (rule step_reflects_SN_on)
   fix ys assume edge: "(xs,ys)\<in>lp_answer_steps T"
   obtain event where step: "T xs event ys" using edge by (auto simp: lp_answer_steps_def)
   have target: "(xs,ys)\<in>lp_answer_steps U"
     using refines[OF inv step] by (auto simp: lp_answer_steps_def)
   show "SN_on (lp_answer_steps T) {ys}" using ih[OF target] preserved[OF inv step] by blast
  qed
 qed
 have sn: "SN_on (lp_answer_steps T) {ss}"
   using reflect initial contract by (auto simp: lp_answer_contract_def)
 have path: "I ys \<and> (ss,ys)\<in>(lp_answer_steps U)\<^sup>*"
   if "(ss,ys)\<in>(lp_answer_steps T)\<^sup>*" for ys
   using that
 proof (induction rule: rtrancl_induct)
  case base then show ?case using initial by simp
 next
  case (step xs ys)
  obtain event where selected: "T xs event ys" using step.hyps(2)
    by (auto simp: lp_answer_steps_def)
  have inv: "I xs" using step.IH by blast
  have successor: "I ys" by (rule preserved[OF inv selected])
  have edge: "(xs,ys)\<in>lp_answer_steps U" using refines[OF inv selected]
    by (auto simp: lp_answer_steps_def)
  show ?case using successor step.IH edge by (auto intro: rtrancl_into_rtrancl)
 qed
 have covered: "lp_answers_covered T ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
   using contract path refines unfolding lp_answer_contract_def lp_answers_covered_def by blast
 show ?thesis using sn covered by (simp add: lp_answer_contract_def)
qed

ML \<open>
val checked = [@{thm lp_answer_contract_invariant_refinement}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted invariant refinement" else ();
\<close>
end
