theory LP_Cut_Return_Contracts_Test
  imports LP_Cut_Return_Contracts
begin

text \<open>Termination by itself is not a return contract: even the empty
successful goal must have a residual path to its actual answer.\<close>

lemma missing_return_path_rejected:
  assumes "t \<noteq> ret \<eta>"
  shows "\<not> lpc_return_contract P [(LPCGoals [],\<eta>)] {} t ret"
proof
  assume contract: "lpc_return_contract P [(LPCGoals [],\<eta>)] {} t ret"
  have success: "lpc_answer_transition P [(LPCGoals [],\<eta>)] (Some \<eta>) []"
    by (rule lpc_answer_transition.success)
  have "(t,ret \<eta>)\<in>({})\<^sup>*"
    using contract success unfolding lpc_return_contract_def by blast
  then show False using assms by simp
qed

text \<open>A failed active frame restores the saved frame's environment.
It must not report the active (failed) environment as the next successful answer.\<close>

lemma saved_answer_must_be_covered:
  assumes contract: "lpc_return_contract P
      [(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)] R t ret"
  shows "(t,ret \<nu>)\<in>R\<^sup>*"
proof -
  have step: "([(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)],[(LPCGoals [],\<nu>)])
    \<in>lpc_answer_steps P"
    unfolding lpc_answer_steps_def by (auto intro: lpc_answer_transition.failure)
  have path: "([(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)],[(LPCGoals [],\<nu>)])
    \<in>(lpc_answer_steps P)\<^sup>*" by (rule r_into_rtrancl[OF step])
  have success: "lpc_answer_transition P [(LPCGoals [],\<nu>)] (Some \<nu>) []"
    by (rule lpc_answer_transition.success)
  show ?thesis using contract path success unfolding lpc_return_contract_def by blast
qed

lemma failure_cannot_emit_return:
  "\<not> lpc_answer_transition P ((LPCGoals [LPCFail],\<eta>)#es) (Some \<nu>) tt"
  by (rule lpc_answer_failure_never_returns)

lemma barrier_cannot_emit_return:
  "\<not> lpc_answer_transition P ((LPCBarrier m,\<eta>)#es) (Some \<nu>) tt"
  by (rule lpc_answer_barrier_never_returns)

text \<open>Zero-cost progress cannot certify an unchanged source loop. This
guards the administrative-stuttering allowance independently of residual SN.\<close>

lemma stationary_cycle_rejected:
  assumes rep: "rep ss t" and loop: "lpc_answer_transition P ss None ss"
  shows "\<not> lpc_return_graph_valid P {} rep ret weight"
proof
  assume valid: "lpc_return_graph_valid P {} rep ret weight"
  have "(\<exists>u. (t,u)\<in>({})\<^sup>+ \<and> rep ss u) \<or>
    (rep ss t \<and> weight ss < weight ss)"
    using valid rep loop unfolding lpc_return_graph_valid_def by blast
  then show False by simp
qed

text \<open>Positive stuttering example: fail, restore a saved success, exhaust.
The failed and saved environments need not be equal. A return rule for the
saved environment is sufficient; one for the failed environment is not.\<close>

lemma saved_success_graph_valid:
  "lpc_return_graph_valid P {}
    (\<lambda>ss (n::nat). n=0 \<and>
      (ss=[(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)] \<or>
       ss=[(LPCGoals [],\<nu>)] \<or> ss=[]))
    (\<lambda>\<rho>. if \<rho>=\<nu> then 0 else 1) length"
  unfolding lpc_return_graph_valid_def
  by (auto elim: lpc_answer_transition.cases)

lemma saved_success_contract:
  "lpc_return_contract P [(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)] {}
    (0::nat) (\<lambda>\<rho>. if \<rho>=\<nu> then 0 else 1)"
  by (rule lpc_return_graph_contract[OF saved_success_graph_valid]) auto

lemma wrong_saved_environment_rejected:
  assumes "\<eta>\<noteq>\<nu>"
  shows "\<not> lpc_return_contract P [(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)] {}
    (0::nat) (\<lambda>\<rho>. if \<rho>=\<eta> then 0 else 1)"
proof
  assume contract: "lpc_return_contract P [(LPCGoals [LPCFail],\<eta>),(LPCGoals [],\<nu>)] {}
    (0::nat) (\<lambda>\<rho>. if \<rho>=\<eta> then 0 else 1)"
  have "(0,if \<nu>=\<eta> then 0 else 1)\<in>({}::(nat*nat)set)\<^sup>*"
    by (rule saved_answer_must_be_covered[OF contract])
  then show False using assms by auto
qed

end
