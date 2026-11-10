theory LP_Cut_Domain_Projected_Action
 imports LP_Cut_Domain_Projected_Equality
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_refreshed_action_sound:
  assumes checked: "lpc_check_refreshed_action fuel filtering R P Q nds states nd ss action vs left_term right_term"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "precise_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps tt) u)"
  using checked step
proof (cases action)
  case (LPCRResolution call gs c m active saved k l A successor anchors bindings mode outputs yes no)
  show ?thesis
    by (rule precise_projected_resolution_node_sound[OF _ initial known])
      (use checked step LPCRResolution in auto)
next
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  show ?thesis
    by (rule precise_projected_equality_node_sound[OF _ initial known])
      (use checked step LPCREquality in auto)
qed auto

theorem precise_checked_projected_action_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_projected_action fuel filtering R P nds states nd ss returned arity action"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<Longrightarrow>
      precise_return_module_rep nds states vs v \<Longrightarrow>
      precise_return_contract P vs (lpc_projected_rel filtering (set R)) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "precise_return_contract P (lpc_return_eval eta ss) (lpc_projected_rel filtering (set R))
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPCPPlain Q a)
  show ?thesis by (rule precise_projected_module_action_sound[OF _ initial _ known lower])
    (use checked LPCPPlain in auto)
next
  case (LPCPRefreshed Q a vs left_term right_term)
  have check: "lpc_check_refreshed_action fuel filtering R P Q nds states nd ss a vs left_term right_term"
    using checked LPCPRefreshed by simp
  show ?thesis
  proof (rule precise_return_primitive_lower[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v"])
    fix vs v and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v"
    show "precise_return_contract P vs (lpc_projected_rel filtering (set R)) v out"
      using lower[OF strict] represented by auto
  next
    fix event tt assume step: "precise_answer_transition P (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
        ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
          precise_return_module_rep nds states tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lpc_projected_rel filtering (set R))\<^sup>*)"
      using precise_refreshed_action_sound[OF check initial known step]
      by (auto simp: precise_return_module_rep_def)
  qed
qed


end
end
