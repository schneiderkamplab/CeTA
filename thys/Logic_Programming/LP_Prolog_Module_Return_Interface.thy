theory LP_Prolog_Module_Return_Interface
 imports LP_Prolog_Return_Interface LP_Answer_Post_Actual
begin

text \<open>Execution connections may have different caller and callee answer
tuples. Keep the commuting interface map and the actual-return bridge separate;
neither execution matching nor residual termination supplies the bridge.\<close>

lemma lpp_domain_contract_lift_interface_actual:
 assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
 and contract: "lp_answer_contract (lpp_domain_answers P B U D) (lpc_reinterface F ss) R t ret"
 and bridge: "\<And>eta. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
      (ret (F eta),final eta)\<in>R\<^sup>*"
 shows "lp_answer_contract (lpp_domain_answers P B U D) ss R t final"
proof -
 have lifted: "lp_answer_contract (lpp_domain_answers P B U D) ss R t (\<lambda>eta. ret (F eta))"
  by (rule lpp_domain_contract_lift_interface[where F=F, OF commute contract]) simp
 show ?thesis by (rule lp_answer_contract_post_actual[OF lifted bridge])
qed

theorem lpp_domain_module_boundary_contract:
 assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
 and child: "lp_answer_contract (lpp_domain_answers P B U D) (lpc_reinterface F ss) R u ret"
 and call: "(t,u)\<in>R\<^sup>*"
 and bridge: "\<And>eta. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
      (ret (F eta),final eta)\<in>R\<^sup>*"
 shows "lp_answer_contract (lpp_domain_answers P B U D) ss R t final"
proof -
 have lifted: "lp_answer_contract (lpp_domain_answers P B U D) ss R u final"
  by (rule lpp_domain_contract_lift_interface_actual[where F=F, OF commute child bridge])
 show ?thesis by (rule lp_answer_contract_start[OF call lifted])
qed

text \<open>A shared interface avoids assuming that either output tuple determines
the other. Both projections commute with runtime substitutions, including
substitutions that change shared caller-only terms.\<close>

theorem lpp_domain_shared_interface_boundary:
 assumes caller: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
 and callee: "\<And>eta sigma. G (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (G eta y) sigma)"
 and child: "lp_answer_contract (lpp_domain_answers P B U D) (lpc_reinterface G ss) R u ret"
 and call: "(t,u)\<in>R\<^sup>*"
 and bridge: "\<And>eta. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
      (ret (G eta),final (F eta))\<in>R\<^sup>*"
 shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_reinterface F ss) R t final"
proof -
 have shared: "lp_answer_contract (lpp_domain_answers P B U D) ss R t (\<lambda>eta. final (F eta))"
  by (rule lpp_domain_module_boundary_contract[where F=G, OF callee child call bridge])
 show ?thesis
  by (rule lpp_domain_contract_project[where F=F, OF caller shared]) simp
qed

definition lpp_check_shared_return_interface where
 "lpp_check_shared_return_interface left_indices right_indices shared caller callee =
  (lpc_check_return_projection left_indices shared caller \<and>
   lpc_check_return_projection right_indices shared callee)"

theorem lpp_domain_checked_shared_interface_boundary:
 assumes checked: "lpp_check_shared_return_interface left_indices right_indices shared caller callee"
 and child: "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_eval eta callee) R u ret"
 and call: "(t,u)\<in>R\<^sup>*"
 and bridge: "\<And>rho. lp_actual_answer (lpp_domain_answers P B U D) (lpc_return_eval eta shared) rho \<Longrightarrow>
   (ret (lpc_project_interface right_indices rho),final (lpc_project_interface left_indices rho))\<in>R\<^sup>*"
 shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_eval eta caller) R t final"
proof -
 have left_shape: "lpc_return_eval eta caller =
   lpc_reinterface (lpc_project_interface left_indices) (lpc_return_eval eta shared)"
  by (rule lpc_check_return_projection_sound) (use checked in \<open>simp add: lpp_check_shared_return_interface_def\<close>)
 have right_shape: "lpc_return_eval eta callee =
   lpc_reinterface (lpc_project_interface right_indices) (lpc_return_eval eta shared)"
  by (rule lpc_check_return_projection_sound) (use checked in \<open>simp add: lpp_check_shared_return_interface_def\<close>)
 show ?thesis unfolding left_shape
  apply (rule lpp_domain_shared_interface_boundary[where F="lpc_project_interface left_indices"
    and G="lpc_project_interface right_indices" and u=u and ret=ret])
  subgoal by (rule lpc_project_interface_commutes)
  subgoal by (rule lpc_project_interface_commutes)
  subgoal using child right_shape by simp
  subgoal by (rule call)
  subgoal by (rule bridge)
  done
qed

ML \<open>
val checked = @{thms lp_answer_contract_post_actual lp_answer_contract_reject_uncovered_return lpp_domain_contract_lift_interface_actual lpp_domain_module_boundary_contract lpp_domain_shared_interface_boundary lpp_domain_checked_shared_interface_boundary};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted module return interface dependency" else ();
\<close>
end
