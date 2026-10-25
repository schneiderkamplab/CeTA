theory LP_Cut_SEG_Split_Lower
  imports LP_Cut_SEG_Connection
begin

text \<open>Recursive Split uses whole contextual residuals as induction
measures. Groundness and routing of the continuation need only hold for actual
prefix answers, not arbitrary residual terms that happen to be reachable.\<close>

theorem lpc_seg_split_lower_actual:
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
      lpc_return_contract P vs R v out"
    and entry: "(t,p)\<in>R\<^sup>+"
    and prefix_rep: "rep ss p ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation_rep: "\<And>mu. lpc_actual_return P ss mu \<Longrightarrow>
      \<exists>v out. (ret mu,v)\<in>R\<^sup>* \<and>
        rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x mu)) rest),mu)] v out \<and>
        (\<forall>eta. lpc_actual_return P
          [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x mu)) rest),mu)] eta \<longrightarrow>
          (out eta,final eta)\<in>R\<^sup>*)"
  shows "lpc_return_contract P (lpc_attach_answers rest ss) R t final"
proof -
  have prefix: "lpc_return_contract P ss R p ret" by (rule lower[OF entry prefix_rep])
  have composed: "lpc_return_contract P (lpc_attach_answers rest ss) R p final"
  proof (rule lpc_return_contract_compose_actual[OF program prefix valid separated])
    fix mu assume actual: "lpc_actual_return P ss mu"
    let ?us = "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x mu)) rest),mu)]"
    obtain v out where bridge: "(ret mu,v)\<in>R\<^sup>*"
      and represented: "rep ?us v out"
      and finish: "\<And>eta. lpc_actual_return P ?us eta \<Longrightarrow> (out eta,final eta)\<in>R\<^sup>*"
      using continuation_rep[OF actual] by blast
    have returned: "(p,ret mu)\<in>R\<^sup>*" by (rule lpc_actual_return_residual[OF prefix actual])
    have path: "(p,v)\<in>R\<^sup>*" by (rule rtrancl_trans[OF returned bridge])
    have strict: "(t,v)\<in>R\<^sup>+" by (rule trancl_rtrancl_trancl[OF entry path])
    have child: "lpc_return_contract P ?us R v out" by (rule lower[OF strict represented])
    have completed: "lpc_return_contract P ?us R v final"
      by (rule lpc_return_contract_post_actual[OF child finish])
    show "lpc_return_contract P ?us R (ret mu) final"
      by (rule lpc_return_contract_start[OF bridge completed])
  qed
  show ?thesis by (rule lpc_return_contract_start[OF trancl_into_rtrancl[OF entry] composed])
qed

end
