theory LP_Cut_Domain_Return_Domain_Compose
  imports LP_Cut_Domain_Return_Interface_Lift
begin

context cut_runtime_domain
begin

lemma precise_actual_return_domain:
  assumes initial: "precise_environments ss"
    and actual: "precise_actual_return P ss rho"
  shows "D (rho x)"
  using actual precise_returned_domain[OF initial]
  by (auto simp: precise_actual_return_def)

text \<open>Only reachable successful answers start a continuation. Thus a
continuation checker may use membership in the selected term domain: that
membership follows from the input and the verified execution, even when the
residual relation overapproximates answers by arbitrary infinite trees.\<close>
theorem precise_return_contract_compose_domain:
  assumes program: "lp_cut_source_program P"
    and prefix: "precise_return_contract P ss R t ret"
    and initial: "precise_environments ss"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. (\<And>x. D (eta x)) \<Longrightarrow> (t,ret eta)\<in>R\<^sup>* \<Longrightarrow>
      precise_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "precise_return_contract P (lpc_attach_answers rest ss) R t final"
proof (rule precise_return_contract_compose_actual[OF program prefix valid separated])
  fix eta assume actual: "precise_actual_return P ss eta"
  have domain: "\<And>x. D (eta x)" by (rule precise_actual_return_domain[OF initial actual])
  have reach: "(t,ret eta)\<in>R\<^sup>*" by (rule precise_actual_return_residual[OF prefix actual])
  show "precise_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
    by (rule continuation[OF domain reach])
qed

end
end
