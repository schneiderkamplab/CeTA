theory LP_Prolog_Context_Free_Allocate
 imports LP_Prolog_Context_Free_Admin
begin
definition lpp_check_context_free_case_node where
  "lpp_check_context_free_case_node fuel P Q nds states contexts Fs nd F source_context m f ts gs active saved e =
    (lp_cut_check_case P m f ts gs (map fst saved)
       (map fst (lpc_return_case P m f ts gs active saved)) \<and>
     lpp_check_context_free_link fuel Q nds states contexts Fs nd (lpc_return_case P m f ts gs active saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context e)"

theorem lpp_context_free_case_node_sound:
  assumes checked: "lpp_check_context_free_case_node fuel P Q nds states contexts Fs nd F source_context m f ts gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp: lpp_check_context_free_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using lpc_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using lpp_context_free_link_sound[OF link _ refl known free observed] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

definition lpp_check_context_free_meta_node where
  "lpp_check_context_free_meta_node fuel Q nds states contexts Fs nd F source_context m a gs active saved body e =
    (lp_cut_check_meta m a gs (map fst saved) body \<and>
     lpp_check_context_free_link fuel Q nds states contexts Fs nd
       ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context e)"

theorem lpp_context_free_meta_node_sound:
  assumes checked: "lpp_check_context_free_meta_node fuel Q nds states contexts Fs nd F source_context m a gs active saved body e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp: lpp_check_context_free_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using lpc_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using lpp_context_free_link_sound[OF link _ refl known free observed] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

end
