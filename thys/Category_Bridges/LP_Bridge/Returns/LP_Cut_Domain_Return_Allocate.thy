theory LP_Cut_Domain_Return_Allocate
  imports LP_Cut_Domain_Return_Table
begin

context cut_runtime_domain
begin

lemma precise_return_case_covers:
  assumes checked: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>n. tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved)))"
proof -
  have erased: "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#map fst saved) eta,map fst tt)\<in>source P"
    using precise_source_subset[THEN subsetD, OF precise_answer_transition_erases[OF step]]
    by (simp add: lpc_return_eval_erases)
  obtain n where target: "map fst tt=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
    (lp_cut_state_eval (map fst (lpc_return_case P m f ts gs active saved)) eta)"
    using checked_case_covers[OF checked erased] by blast
  have first: "map fst tt=map fst (lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved)))"
    using target by (simp only: lpc_return_scope_erases lpc_return_eval_erases)
  have st: "precise_answer_transition P
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) (map (\<lambda>t. lp_ieval t eta) ts))#
      map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have event: "event=None" and second: "map snd tt=map snd
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using st by (cases rule: precise_answer_transition.cases;
      auto simp: lpc_return_case_def lpc_return_eval_def map_map o_def)+
  have same: "tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    by (rule lpc_return_pairs_eq[OF first]) (simp add: lpc_return_scope_answers second)
  show ?thesis using event same by blast
qed

theorem precise_return_case_node_sound:
  assumes checked: "lpc_check_return_case_node fuel P Q nds states nd m f ts gs active saved e"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpc_check_return_table_link fuel Q nds states nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (auto simp: lpc_check_return_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using precise_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using precise_return_table_link_sound[OF link _ refl known] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

lemma precise_return_meta_covers:
  assumes checked: "lp_cut_check_meta m a gs (map fst saved) body"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>n. tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved)))"
proof -
  have erased: "(lp_cut_state_eval (LPCGoals (LPCMeta a#gs)#map fst saved) eta,map fst tt)\<in>source P"
    using precise_source_subset[THEN subsetD, OF precise_answer_transition_erases[OF step]]
    by (simp add: lpc_return_eval_erases)
  obtain n where target: "map fst tt=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
    (lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#map fst saved) eta)"
    using checked_meta_covers[OF checked erased] by blast
  have first: "map fst tt=map fst (lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved)))"
    using target by (simp only: lpc_return_scope_erases lpc_return_eval_erases list.map fst_conv)
  have st: "precise_answer_transition P
    ((LPCGoals (LPCMeta (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have lowered: "lp_cut_lower m (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) body)"
    by (rule lp_cut_lower_finite_sound) (use checked in \<open>simp add: lp_cut_check_meta_def\<close>)
  have event: "event=None" and second: "map snd tt=map snd
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using st lowered by (cases rule: precise_answer_transition.cases;
      auto simp: lpc_return_eval_def map_map o_def)+
  have same: "tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    by (rule lpc_return_pairs_eq[OF first]) (simp add: lpc_return_scope_answers second)
  show ?thesis using event same by blast
qed

theorem precise_return_meta_node_sound:
  assumes checked: "lpc_check_return_meta_node fuel Q nds states nd m a gs active saved body e"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpc_check_return_table_link fuel Q nds states nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (auto simp: lpc_check_return_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using precise_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using precise_return_table_link_sound[OF link _ refl known] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

end
end
