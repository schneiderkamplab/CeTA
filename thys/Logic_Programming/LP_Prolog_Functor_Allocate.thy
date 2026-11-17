theory LP_Prolog_Functor_Allocate
 imports LP_Prolog_Functor_Admin
begin
definition lpp_check_functor_case_node where
  "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts nd F source_context source_functors m f ts gs active saved e =
    (lp_cut_check_case P m f ts gs (map fst saved)
       (map fst (lpc_return_case P m f ts gs active saved)) \<and>
     lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd (lpc_return_case P m f ts gs active saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e)"

theorem lpp_functor_case_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts nd F source_context source_functors m f ts gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    using checked by (auto simp: lpp_check_functor_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using lpc_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using lpp_evaluation_functor_link_sound[OF contract evaluation program link _ refl known free observed functors] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

definition lpp_check_functor_meta_node where
  "lpp_check_functor_meta_node T fs fuel Q nds states contexts Fs functor_contexts nd F source_context source_functors m a gs active saved body e =
    (lp_cut_check_meta m a gs (map fst saved) body \<and>
     lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
       ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e)"

theorem lpp_functor_meta_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_meta_node T fs fuel Q nds states contexts Fs functor_contexts nd F source_context source_functors m a gs active saved body e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    using checked by (auto simp: lpp_check_functor_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using lpc_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using lpp_evaluation_functor_link_sound[OF contract evaluation program link _ refl known free observed functors] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed


lemma lpp_functor_case_missing_table_rejected:
 "\<not> lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs [] nd F
   source_context source_functors m f ts gs active saved e"
 by (simp add: lpp_check_functor_case_node_def lpp_check_evaluation_functor_link_def)

lemma lpp_functor_meta_missing_table_rejected:
 "\<not> lpp_check_functor_meta_node T fs fuel Q nds states contexts Fs [] nd F
   source_context source_functors m a gs active saved body e"
 by (simp add: lpp_check_functor_meta_node_def lpp_check_evaluation_functor_link_def)

ML \<open>
val checked = [@{thm lpp_functor_case_node_sound}, @{thm lpp_functor_meta_node_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor administrative dependency" else ();
\<close>
end
