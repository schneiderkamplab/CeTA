theory LP_Cut_Domain_Return_Residual_Query
 imports LP_Cut_Domain_Return_Ground_Split_Check
begin

context cut_runtime_domain
begin

theorem precise_check_residual_query_sound:
  fixes fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "lpc_check_residual_query I J Q nd predicates constructors
      R outs fallback names marks filters q n positions seed nfs prf"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
  shows "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
proof -
  let ?p = "lpc_lookup fallback predicates"
  let ?d = "lpc_lookup fallback constructors"
  let ?ts = "map (map_lp_iterm ?d id) (map eta (lpcn_vars nd))"
  have child: "check_lp_constructor I J R outs fallback names marks filters q n positions seed nfs prf"
    and length: "n=length (lpcn_vars nd)"
    and positions: "positions=lpc_node_ground_positions nd"
    and source: "R=lp_roles_program ?p ?d Q" and root: "q=?p (lpcn_pred nd)"
    using checked by (auto simp: lpc_check_residual_query_def Let_def)
  have gr: "lp_seg_ground (?ts!i)" if member: "i\<in>set positions" and bound: "i<n" for i
  proof -
    have input: "lpcn_vars nd!i\<in>set (lpcn_ground nd)"
      using member positions by (simp add: lpc_node_ground_positions_def)
    have "lp_seg_ground (eta (lpcn_vars nd!i))"
      using known input by (simp add: knowledge_def)
    then have "lp_seg_ground (map_lp_iterm ?d id (eta (lpcn_vars nd!i)))"
      by (rule lp_seg_ground_map_symbols)
    then show ?thesis using bound length by simp
  qed
  have mapped: "SN_on (lp_ild R) {[(q,?ts)]}"
    by (rule check_lp_constructor_infinite_sound[OF I J child]) (use length gr in auto)
  show ?thesis by (rule lp_roles_termination_reflect[where p="?p" and d="?d"])
    (use mapped source root in \<open>simp add: lp_roles_iatom_def\<close>)
qed



end
end
