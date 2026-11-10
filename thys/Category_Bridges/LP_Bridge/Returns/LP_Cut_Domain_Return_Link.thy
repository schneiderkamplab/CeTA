theory LP_Cut_Domain_Return_Link
  imports LP_Cut_Domain_Return_Symbolic
begin

context cut_runtime_domain
begin

theorem precise_return_link_sound:
  assumes checked: "lpc_check_return_link fuel Q nds nd ss G guards eqs child e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd) = map eta (lpcn_vars nd)"
    and known: "knowledge (set G) guards eta'"
  defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  shows "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    and "knowledge (set (lpcn_ground (nds!lpcl_target e)))
      (lpcn_guards (nds!lpcl_target e)) nu"
    and "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
proof -
  let ?mu = "lp_cut_instance_subst (lpcl_bindings e)"
  let ?target = "nds!lpcl_target e"
  have link: "lpc_check_link fuel Q nds nd (map fst ss) G guards eqs e"
    and annotated: "lpc_return_map
      (\<lambda>t. t\<cdot>lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))) ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_map (\<lambda>t. t\<cdot>?mu) child)"
    using checked by (auto simp: lpc_check_return_link_def)
  have intf: "lp_cut_check_interface fuel eqs (lpcl_vars e) (lpcl_terms e) (map fst ss) G guards
      (lpcl_state e) (lpcl_ground e) (lpcl_guards e)"
    and inst: "lp_cut_check_instance (lpcl_state e) (lpcl_ground e) (lpcl_guards e)
      (lpcn_state ?target) (lpcn_ground ?target) (lpcn_guards ?target) (lpcl_bindings e) (lpcl_swaps e)"
    and lhs: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcn_vars nd)) =
      Some (Some (map LPCAtom (lpcl_lhs e)))"
    and rhs: "lp_cut_normalize fuel eqs (map LPCAtom (map ?mu (lpcn_vars ?target))) =
      Some (Some (map LPCAtom (lpcl_rhs e)))"
    and clause: "((lpcn_pred nd,lpcl_lhs e),[(lpcn_pred ?target,lpcl_rhs e)])\<in>set Q"
    using link by (auto simp: lpc_check_link_def Let_def)
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcl_vars e)) =
    Some (Some (map LPCAtom (lpcl_terms e)))"
    using intf by (simp add: lp_cut_check_interface_def)
  have unchanged: "\<And>x. lp_ieval (lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e)) x) eta' = eta' x"
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have evaluated: "lpc_return_eval eta'
      (lpc_return_map (\<lambda>t. t\<cdot>lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))) ss) =
      lpc_return_eval eta' (lpc_return_scope_word (lpcl_swaps e) (lpc_return_map (\<lambda>t. t\<cdot>?mu) child))"
    by (rule arg_cong[OF annotated])
  show "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    using evaluated by (simp add: lpc_return_eval_subst lpc_return_eval_scopes unchanged nu_def)
  have specialized: "knowledge (set (lpcl_ground e)) (lpcl_guards e) eta'"
    by (rule interface_knowledge[OF intf equations known])
  show "knowledge (set (lpcn_ground ?target)) (lpcn_guards ?target) nu"
    unfolding nu_def by (rule instance_knowledge[OF inst specialized])
  have normalized_rhs: "map (\<lambda>t. lp_ieval t eta') (lpcl_rhs e)=map nu (lpcn_vars ?target)"
    using lp_cut_normalized_terms[OF equations rhs] by (simp add: nu_def map_map o_def)
  show "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred ?target,map nu (lpcn_vars ?target))])\<in>lp_ild Q"
    using lp_cut_normalized_residual_step[OF clause equations lhs old] normalized_rhs by simp
qed

end
end
