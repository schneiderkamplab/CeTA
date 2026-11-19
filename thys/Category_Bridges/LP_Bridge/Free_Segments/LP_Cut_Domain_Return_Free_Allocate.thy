theory LP_Cut_Domain_Return_Free_Allocate
 imports LP_Cut_Domain_Return_Free_Resolution
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_return_free_admin_node_sound:
  assumes checked: "lpc_check_return_free_admin_node fuel Q nds states Fs nd F ss returned arity event next e"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and step: "precise_answer_transition P (lpc_return_eval eta ss) actual tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      precise_return_free_rep nds states Fs (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. actual=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof -
  have base: "lpc_check_return_admin_node fuel Q nds states nd ss returned arity event next e"
    and link: "lpc_check_return_free_table_link fuel Q nds states Fs nd next (lpcn_ground nd) (lpcn_guards nd) [] F e"
    using checked by (auto simp: lpc_check_return_free_admin_node_def)
  have admin: "lpc_return_admin ss=Some (event,next)"
    using base by (simp add: lpc_check_return_admin_node_def)
  have evaluated: "lpc_return_admin (lpc_return_eval eta ss) =
    Some (map_option (\<lambda>ts. lpc_return_env ts eta) event,lpc_return_eval eta next)"
    by (simp add: lpc_return_eval_admin admin)
  have same: "tt=lpc_return_eval eta next"
    using precise_return_admin_unique[OF evaluated step] by simp
  have successor: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_free_rep nds states Fs (lpc_return_scope_word swaps tt) u"
    using precise_return_free_table_link_sound[OF link _ refl known free] same
    by (simp add: lp_equations_def)
  show ?thesis using successor precise_return_admin_node_sound[OF base known step] by blast
qed


theorem precise_return_free_case_node_sound:
  assumes checked: "lpc_check_return_free_case_node fuel P Q nds states Fs nd F m f ts gs active saved e"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_free_rep nds states Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpc_check_return_free_table_link fuel Q nds states Fs nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] F e"
    using checked by (auto simp: lpc_check_return_free_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using precise_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_free_rep nds states Fs (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using precise_return_free_table_link_sound[OF link _ refl known free] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed


theorem precise_return_free_meta_node_sound:
  assumes checked: "lpc_check_return_free_meta_node fuel Q nds states Fs nd F m a gs active saved body e"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_free_rep nds states Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpc_check_return_free_table_link fuel Q nds states Fs nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F e"
    using checked by (auto simp: lpc_check_return_free_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using precise_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_free_rep nds states Fs (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using precise_return_free_table_link_sound[OF link _ refl known free] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed


end
end
