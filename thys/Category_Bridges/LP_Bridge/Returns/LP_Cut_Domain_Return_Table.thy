theory LP_Cut_Domain_Return_Table
  imports LP_Cut_Domain_Return_Link LP_Cut_Domain_Return_Steps
begin

context cut_runtime_domain
begin

definition precise_return_rep where
  "precise_return_rep nds states ss t = (\<exists>i eta.
    i < length nds \<and> i < length states \<and>
    ss = lpc_return_eval eta (states!i) \<and>
    knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    t = [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

lemma precise_return_table_link_sound:
  assumes checked: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "knowledge (set G) guards eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  have link: "lpc_check_return_link fuel Q nds nd ss G guards eqs (states!?j) e"
    and state_bound: "?j<length states"
    using checked by (auto simp: lpc_check_return_table_link_def)
  have node_bound: "?j<length nds"
    using link by (auto simp: lpc_check_return_link_def lpc_check_link_def)
  have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval ?nu (states!?j))"
    and child_known: "knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) ?nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using precise_return_link_sound[OF link equations old known] by blast+
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss) = lpc_return_eval ?nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have represented: "precise_return_rep nds states
    (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
    [(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))]"
    unfolding precise_return_rep_def
    by (rule exI[of _ ?j], rule exI[of _ ?nu])
      (use node_bound state_bound inverse child_known in auto)
  show ?thesis using edge represented by blast
qed

theorem precise_return_admin_node_sound:
  assumes checked: "lpc_check_return_admin_node fuel Q nds states nd ss returned arity event next e"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "precise_answer_transition P (lpc_return_eval eta ss) actual tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      precise_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. actual=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof -
  have admin: "lpc_return_admin ss=Some (event,next)"
    and link: "lpc_check_return_table_link fuel Q nds states nd next (lpcn_ground nd) (lpcn_guards nd) [] e"
    and emit: "case event of None\<Rightarrow>True | Some ts\<Rightarrow>lpc_check_return_emit Q nd returned arity ts"
    using checked by (auto simp: lpc_check_return_admin_node_def)
  have evaluated: "lpc_return_admin (lpc_return_eval eta ss) =
    Some (map_option (\<lambda>ts. lpc_return_env ts eta) event,lpc_return_eval eta next)"
    by (simp add: lpc_return_eval_admin admin)
  have same: "actual=map_option (\<lambda>ts. lpc_return_env ts eta) event \<and> tt=lpc_return_eval eta next"
    by (rule precise_return_admin_unique[OF evaluated step])
  have successor: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps tt) u"
    using precise_return_table_link_sound[OF link _ refl known] same
    by (simp add: lp_equations_def)
  have returns: "\<forall>rho. actual=Some rho \<longrightarrow>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  proof (intro allI impI)
    fix rho assume actual: "actual=Some rho"
    obtain ts where event: "event=Some ts" and rho: "rho=lpc_return_env ts eta"
      using same actual by (cases event) auto
    have check: "lpc_check_return_emit Q nd returned arity ts" using emit event by simp
    show "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
      using lpc_return_emit_sound[OF check, of eta] rho by auto
  qed
  show ?thesis using successor returns by blast
qed

end
end
