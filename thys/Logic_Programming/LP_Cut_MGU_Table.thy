theory LP_Cut_MGU_Table
  imports LP_Cut_MGU_Answer_Split LP_Cut_Table_Check
begin

fun lpc_mgu_check_action where
  "lpc_mgu_check_action fuel P Q nds Fs nd F LPCATerminal = (lpcn_state nd=[])"
| "lpc_mgu_check_action fuel P Q nds Fs nd F LPCAInconsistent = lp_cut_check_inconsistent (lpcn_guards nd)"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCARefutedGuard i k bindings) =
    lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAPlain Ss roles) = lpc_check_plain P Q nd Ss roles"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAControl Ss roles) = lpc_check_control P Q nd Ss roles"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAAnswerSplit pregs rest Ss j) =
    (lpc_check_answer_split P Q nds nd pregs rest Ss j \<and> Fs!j=[])"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAStack links) =
    (length links=length (lpcn_state nd) \<and>
     list_all (\<lambda>i. lpc_check_link fuel Q nds nd [lpcn_state nd!i]
       (lpcn_ground nd) (lpcn_guards nd) [] (links!i) \<and>
       lpc_check_link_free fuel [] F (Fs!lpcl_target (links!i)) (lpcl_bindings (links!i))) [0..<length links])"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAAdmin successor e) =
    (lp_cut_check_admin (lpcn_state nd) successor \<and>
     lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e \<and>
     lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e))"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCATrim successor bs e) =
    (lpcn_state nd=successor@bs \<and> lp_cut_barriers bs \<and>
     lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e \<and>
     lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e))"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCACase f ts gs es m successor e) =
    (lpcn_state nd=LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es \<and>
     lp_cut_check_case P m f ts gs es successor \<and>
     lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e \<and>
     lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e))"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAMeta a gs es m body e) =
    (lpcn_state nd=LPCGoals (LPCMeta a#gs)#es \<and>
     lp_cut_check_meta m a gs es body \<and>
     lpc_check_link fuel Q nds nd (LPCGoals (body@gs)#LPCBarrier m#es)
       (lpcn_ground nd) (lpcn_guards nd) [] e \<and>
     lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e))"
| "lpc_mgu_check_action fuel P Q nds Fs nd F
    (LPCAResolution a gs c m es k l A successor anchors bindings mode yes no) =
     lpc_mgu_check_resolution_node fuel P Q nds Fs nd F a gs c m es k l A successor anchors bindings mode yes no"
| "lpc_mgu_check_action fuel P Q nds Fs nd F (LPCAEquality a b gs es k l successor mode yes no) =
     (lpc_check_equality_node fuel P Q nds nd a b gs es k l successor mode yes no \<and>
      (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
        lpc_check_link_free fuel [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd)))]
          [] (Fs!lpcl_target yes) (lpcl_bindings yes)) \<and>
      (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
        lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)))"

lemma lpc_mgu_allocation_reflects_SN:
  assumes program: "lp_cut_source_program P"
    and covers: "\<And>t. (s,t)\<in>lp_cut_mgu_source P \<Longrightarrow>
      \<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) successor"
    and sn: "SN_on (lp_cut_mgu_source P) {successor}"
  shows "SN_on (lp_cut_mgu_source P) {s}"
proof (rule step_reflects_SN_on)
  fix t assume "(s,t)\<in>lp_cut_mgu_source P"
  then obtain n where "t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) successor"
    using covers by blast
  then show "SN_on (lp_cut_mgu_source P) {t}"
    using lpc_mgu_scope_swap_preserves_SN[OF program sn, of m n] by simp
qed

theorem lpc_mgu_action_sound:
  fixes P :: "('a,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_mgu_check_action fuel P Q nds Fs nd F action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
    and paths: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> (lp_ild Q)\<^sup>+ \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (cases action)
  case (LPCAAnswerSplit pregs rest Ss j)
  have split: "lpc_check_answer_split P Q nds nd pregs rest Ss j" and empty: "Fs!j=[]"
    using checked by (simp_all add: LPCAAnswerSplit)
  have bound: "j<length nds" using split by (simp add: lpc_check_answer_split_def)
  show ?thesis by (rule lpc_mgu_check_answer_split_sound[OF split known residual])
    (use paths[OF bound] in \<open>auto simp: empty lpc_free_knowledge_def\<close>)
next
  case LPCATerminal
  show ?thesis by (rule lp_cut_conservative_implies_mgu_SN)
    (use LPCATerminal checked lp_cut_terminal_node_sound[of P] in \<open>simp add: lp_cut_state_map_def\<close>)
next
  case LPCAInconsistent
  then have "lp_cut_check_inconsistent (lpcn_guards nd)" using checked by simp
  then show ?thesis using lp_cut_checked_inconsistent[OF _ known] by blast
next
  case (LPCARefutedGuard i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked by (simp add: LPCARefutedGuard)
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
next
  case (LPCAPlain Ss roles)
  have plain: "lpc_check_plain P Q nd Ss roles" using checked by (simp add: LPCAPlain)
  show ?thesis by (rule lp_cut_conservative_implies_mgu_SN[OF lpc_check_plain_sound[OF plain residual]])
next
  case (LPCAControl Ss roles)
  have control: "lpc_check_control P Q nd Ss roles" using checked by (simp add: LPCAControl)
  show ?thesis by (rule lp_cut_conservative_implies_mgu_SN[OF lpc_check_control_sound[OF control residual]])
next
  case (LPCAStack links)
  have len: "length links=length (lpcn_state nd)"
    and checks: "\<And>i. i<length links \<Longrightarrow>
      lpc_check_link fuel Q nds nd [lpcn_state nd!i]
        (lpcn_ground nd) (lpcn_guards nd) [] (links!i)"
    and frees: "\<And>i. i<length links \<Longrightarrow>
      lpc_check_link_free fuel [] F (Fs!lpcl_target (links!i)) (lpcl_bindings (links!i))"
    using checked by (auto simp: LPCAStack list_all_iff)
  show ?thesis
  proof (rule lpc_mgu_singleton_stack_SN)
    fix e assume "e\<in>set (lp_cut_state_eval (lpcn_state nd) \<eta>)"
    then obtain i where i: "i<length (lpcn_state nd)"
      and e: "[e]=lp_cut_state_eval [lpcn_state nd!i] \<eta>"
      by (auto simp: lp_cut_state_map_def in_set_conv_nth)
    show "SN_on (lp_cut_mgu_source P) {[e]}" unfolding e
      by (rule lpc_mgu_plain_link_sound[OF program checks frees known free ih]) (use i len in simp_all)
  qed
next
  case (LPCAAdmin successor e)
  have admin: "lp_cut_check_admin (lpcn_state nd) successor"
    and link: "lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    and frees: "lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e)"
    using checked by (simp_all add: LPCAAdmin)
  have child: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval successor \<eta>}"
    by (rule lpc_mgu_plain_link_sound[OF program link frees known free ih])
  show ?thesis
    by (rule step_reflects_SN_on)
      (use lp_cut_checked_admin_covers[OF admin] child lp_cut_mgu_source_subset[of P] in blast)
next
  case (LPCATrim successor bs e)
  have shape: "lpcn_state nd=successor@bs" and barriers: "lp_cut_barriers bs"
    and link: "lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    and frees: "lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e)"
    using checked by (simp_all add: LPCATrim)
  have child: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval successor \<eta>}"
    by (rule lpc_mgu_plain_link_sound[OF program link frees known free ih])
  have bs: "lp_cut_barriers (lp_cut_state_eval bs \<eta>)"
    using barriers by (simp only: lp_cut_barriers_state_map)
  show ?thesis using lpc_mgu_append_barriers_SN[OF child bs] shape
    by (simp add: lp_cut_state_map_def)
next
  case (LPCACase f ts gs es m successor e)
  have shape: "lpcn_state nd=LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es"
    and allocation: "lp_cut_check_case P m f ts gs es successor"
    and link: "lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    and frees: "lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e)"
    using checked by (simp_all add: LPCACase)
  have child: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval successor \<eta>}"
    by (rule lpc_mgu_plain_link_sound[OF program link frees known free ih])
  show ?thesis
  proof (rule lpc_mgu_allocation_reflects_SN[where m=m, OF program _ child])
    fix t assume st: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t)\<in>lp_cut_mgu_source P"
    show "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) (lp_cut_state_eval successor \<eta>)"
      by (rule lp_cut_checked_case_covers[OF allocation]) (use st lp_cut_mgu_source_subset[of P] in \<open>auto simp only: shape\<close>)
  qed
next
  case (LPCAMeta a gs es m body e)
  have shape: "lpcn_state nd=LPCGoals (LPCMeta a#gs)#es"
    and allocation: "lp_cut_check_meta m a gs es body"
    and link: "lpc_check_link fuel Q nds nd (LPCGoals (body@gs)#LPCBarrier m#es)
      (lpcn_ground nd) (lpcn_guards nd) [] e"
    and frees: "lpc_check_link_free fuel [] F (Fs!lpcl_target e) (lpcl_bindings e)"
    using checked by (simp_all add: LPCAMeta)
  have child: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta>}"
    by (rule lpc_mgu_plain_link_sound[OF program link frees known free ih])
  show ?thesis
  proof (rule lpc_mgu_allocation_reflects_SN[where m=m, OF program _ child])
    fix t assume st: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t)\<in>lp_cut_mgu_source P"
    show "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
      (lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta>)"
      by (rule lp_cut_checked_meta_covers[OF allocation]) (use st lp_cut_mgu_source_subset[of P] in \<open>auto simp only: shape\<close>)
  qed
next
  case (LPCAResolution a gs c m es k l A successor anchors bindings mode yes no)
  have resolve: "lpc_mgu_check_resolution_node fuel P Q nds Fs nd F a gs c m es k l A successor anchors bindings mode yes no"
    using checked by (simp add: LPCAResolution)
  show ?thesis by (rule lpc_mgu_resolution_node_sound[OF program resolve known free ih])
next
  case (LPCAEquality a b gs es k l successor mode yes no)
  have eq: "lpc_check_equality_node fuel P Q nds nd a b gs es k l successor mode yes no"
    and success: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpc_check_link_free fuel [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd)))]
        [] (Fs!lpcl_target yes) (lpcl_bindings yes)"
    and failure: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)"
    using checked by (auto simp: LPCAEquality)
  show ?thesis by (rule lpc_mgu_equality_node_sound[OF program eq success failure free known ih])
qed


definition lpc_mgu_check_table where
  "lpc_mgu_check_table fuel P Q nds Fs actions =
    (lp_cut_source_program P \<and> length nds=length actions \<and> length Fs=length nds \<and>
     list_all (\<lambda>i. lpc_mgu_check_action fuel P Q nds Fs (nds!i) (Fs!i) (actions!i)) [0..<length nds])"

theorem lpc_mgu_table_sound:
  assumes checked: "lpc_mgu_check_table fuel P Q nds Fs actions"
    and bound: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) \<eta>"
    and free: "lpc_free_knowledge (set (Fs!i)) \<eta>"
    and child: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map \<eta> (lpcn_vars (nds!i)))]}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!i)) \<eta>}"
proof -
  have all: "SN_on (lp_ild Q) {xs} \<and>
    (\<forall>j \<nu>. j<length nds \<longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<longrightarrow>
      xs=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))] \<longrightarrow>
      SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>})"
    if sn: "SN_on (lp_ild Q) {xs}" for xs
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix xs
    assume ih: "\<And>ys. (xs,ys)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      SN_on (lp_ild Q) {ys} \<and>
      (\<forall>j \<nu>. j<length nds \<longrightarrow>
        lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<longrightarrow>
        ys=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))] \<longrightarrow>
        SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>})"
    have current: "SN_on (lp_ild Q) {xs}"
      by (rule step_reflects_SN_on) (use ih in \<open>blast intro: r_into_trancl\<close>)
    show "SN_on (lp_ild Q) {xs} \<and>
      (\<forall>j \<nu>. j<length nds \<longrightarrow>
        lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<longrightarrow>
        xs=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))] \<longrightarrow>
        SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>})"
    proof (intro conjI allI impI)
      show "SN_on (lp_ild Q) {xs}" by (rule current)
    next
      fix j \<nu>
      assume member: "j<length nds"
        and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu>"
        and freeness: "lpc_free_knowledge (set (Fs!j)) \<nu>"
        and xs: "xs=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]"
      have program: "lp_cut_source_program P"
        and action: "lpc_mgu_check_action fuel P Q nds Fs (nds!j) (Fs!j) (actions!j)"
        using checked member by (auto simp: lpc_mgu_check_table_def list_all_iff)
      have residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]}"
        using current xs by simp
      show "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
        by (rule lpc_mgu_action_sound[OF program action knowledge freeness residual])
          (use ih xs in \<open>blast intro: r_into_trancl\<close>)+
    qed
  qed
  show ?thesis using all[OF child] bound known free by blast
qed


end

