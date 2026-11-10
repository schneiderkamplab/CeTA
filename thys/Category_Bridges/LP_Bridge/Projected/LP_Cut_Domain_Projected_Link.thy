theory LP_Cut_Domain_Projected_Link
 imports LP_Cut_Domain_Projected_Plain
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_projected_checked_link_sound:
  assumes rule: "lpc_check_projected_link_rule filtering R nd nds e"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and link: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "knowledge (set G) guards eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
  by (rule precise_projected_table_link_sound[OF _ initial lpc_return_link_restrict[OF link] equations old known])
    (use rule in \<open>simp add: lpc_check_projected_link_rule_def\<close>)


lemma precise_projected_refreshed_link_sound:
  fixes filtering :: "'f lp_cut_symbol afs"
  assumes refreshed: "lpc_check_refreshed_link fuel filtering R k G A eqs nd nds e left_term right_term"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and link: "lpc_check_return_table_link fuel Q nds states nd ss H guards eqs e"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and equations: "lp_equations eqs (lp_cut_resolution_env k l eta sigma rho)"
    and known: "knowledge (set H) guards (lp_cut_resolution_env k l eta sigma rho)"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps
      (lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ss)) u"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma rho"
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) ?env"
  let ?u = "[(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))]"
  obtain m :: "('f lp_cut_symbol,string) term" where pr: "lp_iproject filtering (LPIFun (lpcn_pred nd) (map eta (lpcn_vars nd))) m"
    using initial by (auto simp: lpc_observed_def lpc_observes_def)
  have basic: "lpc_check_return_link fuel Q nds nd ss H guards eqs (states!?j) e"
    and sb: "?j<length states" and nb: "?j<length nds"
    using link by (auto simp: lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def Let_def)
  obtain n where same: "lpc_return_eval ?env ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval ?nu (states!?j))"
    and knowledge: "knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) ?nu"
    and target_pr: "lp_iproject filtering (LPIFun (lpcn_pred (nds!?j)) (map ?nu (lpcn_vars (nds!?j)))) n"
    and step: "(m,n)\<in>rstep (af_rule filtering ` set R)"
    by (rule precise_projected_return_link[OF basic _ bounds ground equations known pr])
      (use refreshed in \<open>auto simp: lpc_check_refreshed_link_def\<close>)
  have edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],?u)\<in>lpc_projected_rel filtering (set R)"
    using pr target_pr step by (auto simp: lpc_projected_rel_def lpc_observes_def)
  have rep: "precise_return_rep nds states
    (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval ?env ss)) ?u"
    unfolding precise_return_rep_def
    by (rule exI[of _ ?j], rule exI[of _ ?nu])
      (use sb nb knowledge same in \<open>simp add: lpc_return_scope_word_inverse\<close>)
  show ?thesis using edge rep by blast
qed


end
end
