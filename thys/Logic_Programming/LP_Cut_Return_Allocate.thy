theory LP_Cut_Return_Allocate
  imports LP_Cut_Return_Table_Resolution
begin

definition lpc_return_case where
  "lpc_return_case P m f ts gs active saved =
    map (\<lambda>c. (LPCClause (LPCAtom (Fun (LPCUser f) ts)#gs) c m,active))
      (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,active)#saved"

lemma lpc_return_case_erases:
  "map fst (lpc_return_case P m f ts gs active saved) =
    map (\<lambda>c. LPCClause (LPCAtom (Fun (LPCUser f) ts)#gs) c m)
      (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m#map fst saved"
  by (simp add: lpc_return_case_def map_map o_def)

lemma lpc_return_pairs_eq:
  "map fst xs = map fst ys \<Longrightarrow> map snd xs = map snd ys \<Longrightarrow> xs=ys"
  by (metis zip_map_fst_snd)

lemma lpc_return_scope_erases:
  "map fst (lpc_return_scope r ss) = map (lp_cut_scope_entry r) (map fst ss)"
  by (simp add: map_map o_def map_prod_def split_def)

lemma lpc_return_scope_answers:
  "map snd (lpc_return_scope r ss) = map snd ss"
  by (simp add: map_map o_def map_prod_def split_def)

lemma lpc_return_case_covers:
  assumes checked: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>n. tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved)))"
proof -
  have erased: "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#map fst saved) eta,map fst tt)\<in>lp_cut_source P"
    using lp_cut_mgu_source_subset[THEN subsetD, OF lpc_answer_transition_erases[OF step]]
    by (simp add: lpc_return_eval_erases)
  obtain n where target: "map fst tt=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
    (lp_cut_state_eval (map fst (lpc_return_case P m f ts gs active saved)) eta)"
    using lp_cut_checked_case_covers[OF checked erased] by blast
  have first: "map fst tt=map fst (lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved)))"
    using target by (simp only: lpc_return_scope_erases lpc_return_eval_erases)
  have st: "lpc_answer_transition P
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) (map (\<lambda>t. lp_ieval t eta) ts))#
      map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have event: "event=None" and second: "map snd tt=map snd
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using st by (cases rule: lpc_answer_transition.cases;
      auto simp: lpc_return_case_def lpc_return_eval_def map_map o_def)+
  have same: "tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    by (rule lpc_return_pairs_eq[OF first]) (simp add: lpc_return_scope_answers second)
  show ?thesis using event same by blast
qed

lemma lpc_return_scoped_successor:
  assumes same: "tt=lpc_return_scope_word swaps ss"
    and child: "\<exists>u more. (t,u)\<in>R\<^sup>+ \<and> rep (lpc_return_scope_word more ss) u"
  shows "\<exists>u more. (t,u)\<in>R\<^sup>+ \<and> rep (lpc_return_scope_word more tt) u"
proof -
  obtain u more where edge: "(t,u)\<in>R\<^sup>+" and represented: "rep (lpc_return_scope_word more ss) u"
    using child by blast
  show ?thesis by (rule exI[of _ u], rule exI[of _ "rev swaps@more"])
    (simp add: edge same lpc_return_scope_word_append lpc_return_scope_word_inverse represented)
qed

definition lpc_check_return_case_node where
  "lpc_check_return_case_node fuel P Q nds states nd m f ts gs active saved e =
    (lp_cut_check_case P m f ts gs (map fst saved)
       (map fst (lpc_return_case P m f ts gs active saved)) \<and>
     lpc_check_return_table_link fuel Q nds states nd (lpc_return_case P m f ts gs active saved)
       (lpcn_ground nd) (lpcn_guards nd) [] e)"

theorem lpc_return_case_node_sound:
  assumes checked: "lpc_check_return_case_node fuel P Q nds states nd m f ts gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpc_check_return_table_link fuel Q nds states nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (auto simp: lpc_check_return_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using lpc_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using lpc_return_table_link_sound[OF link _ refl known] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

lemma lpc_return_meta_covers:
  assumes checked: "lp_cut_check_meta m a gs (map fst saved) body"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>n. tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved)))"
proof -
  have erased: "(lp_cut_state_eval (LPCGoals (LPCMeta a#gs)#map fst saved) eta,map fst tt)\<in>lp_cut_source P"
    using lp_cut_mgu_source_subset[THEN subsetD, OF lpc_answer_transition_erases[OF step]]
    by (simp add: lpc_return_eval_erases)
  obtain n where target: "map fst tt=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
    (lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#map fst saved) eta)"
    using lp_cut_checked_meta_covers[OF checked erased] by blast
  have first: "map fst tt=map fst (lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved)))"
    using target by (simp only: lpc_return_scope_erases lpc_return_eval_erases list.map fst_conv)
  have st: "lpc_answer_transition P
    ((LPCGoals (LPCMeta (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have lowered: "lp_cut_lower m (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) body)"
    by (rule lp_cut_lower_finite_sound) (use checked in \<open>simp add: lp_cut_check_meta_def\<close>)
  have event: "event=None" and second: "map snd tt=map snd
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using st lowered by (cases rule: lpc_answer_transition.cases;
      auto simp: lpc_return_eval_def map_map o_def)+
  have same: "tt=lpc_return_scope (lp_cut_scope_swap m n)
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    by (rule lpc_return_pairs_eq[OF first]) (simp add: lpc_return_scope_answers second)
  show ?thesis using event same by blast
qed

definition lpc_check_return_meta_node where
  "lpc_check_return_meta_node fuel Q nds states nd m a gs active saved body e =
    (lp_cut_check_meta m a gs (map fst saved) body \<and>
     lpc_check_return_table_link fuel Q nds states nd
       ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] e)"

theorem lpc_return_meta_node_sound:
  assumes checked: "lpc_check_return_meta_node fuel Q nds states nd m a gs active saved body e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpc_check_return_table_link fuel Q nds states nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (auto simp: lpc_check_return_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using lpc_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using lpc_return_table_link_sound[OF link _ refl known] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

end
