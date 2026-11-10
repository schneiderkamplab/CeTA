theory LP_Cut_Domain_Link
  imports LP_Cut_Domain_Success
begin

context cut_runtime_domain
begin

lemma link_sound:
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_link fuel Q nds nd s G K eqs e"
    and equations: "lp_equations eqs \<eta>'"
    and old: "map \<eta>' (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
    and known: "knowledge (set G) K \<eta>'"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (source P) {lp_cut_state_eval s \<eta>'}"
proof -
  let ?child = "nds ! lpcl_target e"
  let ?mu = "lp_cut_instance_subst (lpcl_bindings e)"
  let ?nu = "\<lambda>x. lp_ieval (?mu x) \<eta>'"
  have bound: "lpcl_target e<length nds"
    and intf: "lp_cut_check_interface fuel eqs (lpcl_vars e) (lpcl_terms e) s G K
      (lpcl_state e) (lpcl_ground e) (lpcl_guards e)"
    and inst: "lp_cut_check_instance (lpcl_state e) (lpcl_ground e) (lpcl_guards e)
      (lpcn_state ?child) (lpcn_ground ?child) (lpcn_guards ?child)
      (lpcl_bindings e) (lpcl_swaps e)"
    and inputs: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcn_vars nd)) =
      Some (Some (map LPCAtom (lpcl_lhs e)))"
    and outputs: "lp_cut_normalize fuel eqs (map LPCAtom (map ?mu (lpcn_vars ?child))) =
      Some (Some (map LPCAtom (lpcl_rhs e)))"
    and clause: "((lpcn_pred nd,lpcl_lhs e),[(lpcn_pred ?child,lpcl_rhs e)]) \<in> set Q"
    using checked by (auto simp: lpc_check_link_def Let_def)
  have specialized: "knowledge (set (lpcl_ground e)) (lpcl_guards e) \<eta>'"
    by (rule interface_knowledge[OF intf equations known])
  have child_known: "knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) ?nu"
    by (rule instance_knowledge[OF inst specialized])
  have rhs: "map (\<lambda>t. lp_ieval t \<eta>') (lpcl_rhs e)=map ?nu (lpcn_vars ?child)"
    using lp_cut_normalized_terms[OF equations outputs] by (simp add: map_map o_def)
  have edge: "([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
      [(lpcn_pred ?child,map ?nu (lpcn_vars ?child))]) \<in> lp_ild Q"
    using lp_cut_normalized_residual_step[OF clause equations inputs old] rhs by simp
  have child_sn: "SN_on (source P) {lp_cut_state_eval (lpcn_state ?child) ?nu}"
    by (rule ih[OF bound child_known edge])
  have specialized_sn: "SN_on (source P) {lp_cut_state_eval (lpcl_state e) \<eta>'}"
    by (rule checked_instance_SN[OF program inst child_sn])
  show ?thesis using specialized_sn lp_cut_checked_interface_state[OF intf equations] by simp
qed
lemma plain_link_sound:
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_link fuel Q nds nd s G K [] e"
    and known: "knowledge (set G) K \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (source P) {lp_cut_state_eval s \<eta>}"
  by (rule link_sound[OF program checked _ refl known ih])
    (simp add: lp_equations_def)


end
end
