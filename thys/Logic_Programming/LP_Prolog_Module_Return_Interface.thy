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

ML \<open>
val checked = @{thms lp_answer_contract_post_actual lp_answer_contract_reject_uncovered_return lpp_domain_contract_lift_interface_actual lpp_domain_module_boundary_contract};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted module return interface dependency" else ();
\<close>
end
