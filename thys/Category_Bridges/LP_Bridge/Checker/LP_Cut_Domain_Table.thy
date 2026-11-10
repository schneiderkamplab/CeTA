theory LP_Cut_Domain_Table
  imports LP_Cut_Domain_Answer_Split
begin

context cut_runtime_domain
begin

lemma terminal_SN: "SN_on (source P) {[]}"
  by (rule step_reflects_SN_on) (auto elim: source.cases)

lemma query_env_domain:
  "(\<And>t. t\<in>set ts \<Longrightarrow> D t) \<Longrightarrow> D (lp_cut_query_env vs ts x)"
  by (auto simp: lp_cut_query_env_def split: option.splits
    dest: map_of_SomeD set_zip_rightD intro: variables)

lemma allocation_reflects_SN:
  assumes program: "lp_cut_source_program P"
    and covers: "\<And>t. (s,t)\<in>source P \<Longrightarrow>
      \<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) successor"
    and sn: "SN_on (source P) {successor}"
  shows "SN_on (source P) {s}"
proof (rule step_reflects_SN_on)
  fix t assume "(s,t)\<in>source P"
  then obtain n where "t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) successor"
    using covers by blast
  then show "SN_on (source P) {t}"
    using scope_swap_SN[OF program sn, of m n] by simp
qed

theorem action_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_action fuel P Q nds nd action"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
    and paths: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> (lp_ild Q)\<^sup>+ \<Longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (cases action)
  case LPCATerminal
  then show ?thesis using checked terminal_SN[of P]
    by (simp add: lp_cut_state_map_def)
next
  case LPCAInconsistent
  then have "lp_cut_check_inconsistent (lpcn_guards nd)" using checked by simp
  then show ?thesis using inconsistent[OF _ known] by blast
next
  case (LPCARefutedGuard i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked by (simp add: LPCARefutedGuard)
  then show ?thesis using checked_refuted_guard[OF _ known] by blast
next
  case (LPCAPlain Fs roles)
  have plain: "lpc_check_plain P Q nd Fs roles" using checked by (simp add: LPCAPlain)
  show ?thesis by (rule check_plain_sound[OF plain residual])
next
  case (LPCAControl Fs roles)
  have control: "lpc_check_control P Q nd Fs roles" using checked by (simp add: LPCAControl)
  show ?thesis by (rule check_control_sound[OF control residual])
next
  case (LPCAAnswerSplit pregs rest Fs modes j)
  have split: "lpc_check_answer_split P Q nds nd pregs rest Fs modes j"
    using checked by (simp add: LPCAAnswerSplit)
  show ?thesis by (rule check_answer_split_sound[OF split known residual paths])
next
  case (LPCAStack links)
  have len: "length links=length (lpcn_state nd)"
    and checks: "\<And>i. i<length links \<Longrightarrow>
      lpc_check_link fuel Q nds nd [lpcn_state nd!i]
        (lpcn_ground nd) (lpcn_guards nd) [] (links!i)"
    using checked by (auto simp: LPCAStack list_all_iff)
  show ?thesis
  proof (rule singleton_stack_SN)
    fix e assume "e\<in>set (lp_cut_state_eval (lpcn_state nd) \<eta>)"
    then obtain i where i: "i<length (lpcn_state nd)"
      and e: "[e]=lp_cut_state_eval [lpcn_state nd!i] \<eta>"
      by (auto simp: lp_cut_state_map_def in_set_conv_nth)
    show "SN_on (source P) {[e]}" unfolding e
      by (rule plain_link_sound[OF program checks known ih]) (use i len in simp)
  qed
next
  case (LPCAAdmin successor e)
  have admin: "lp_cut_check_admin (lpcn_state nd) successor"
    and link: "lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (simp_all add: LPCAAdmin)
  have child: "SN_on (source P) {lp_cut_state_eval successor \<eta>}"
    by (rule plain_link_sound[OF program link known ih])
  show ?thesis
    by (rule step_reflects_SN_on)
      (use checked_admin_covers[OF admin] child in blast)
next
  case (LPCATrim successor bs e)
  have shape: "lpcn_state nd=successor@bs" and barriers: "lp_cut_barriers bs"
    and link: "lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (simp_all add: LPCATrim)
  have child: "SN_on (source P) {lp_cut_state_eval successor \<eta>}"
    by (rule plain_link_sound[OF program link known ih])
  have bs: "lp_cut_barriers (lp_cut_state_eval bs \<eta>)"
    using barriers by (simp only: lp_cut_barriers_state_map)
  show ?thesis using append_barriers_SN[OF child bs] shape
    by (simp add: lp_cut_state_map_def)
next
  case (LPCACase f ts gs es m successor e)
  have shape: "lpcn_state nd=LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es"
    and allocation: "lp_cut_check_case P m f ts gs es successor"
    and link: "lpc_check_link fuel Q nds nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (simp_all add: LPCACase)
  have child: "SN_on (source P) {lp_cut_state_eval successor \<eta>}"
    by (rule plain_link_sound[OF program link known ih])
  show ?thesis
  proof (rule allocation_reflects_SN[where m=m, OF program _ child])
    fix t assume st: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t)\<in>source P"
    show "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) (lp_cut_state_eval successor \<eta>)"
      by (rule checked_case_covers[OF allocation]) (use st in \<open>simp only: shape\<close>)
  qed
next
  case (LPCAMeta a gs es m body e)
  have shape: "lpcn_state nd=LPCGoals (LPCMeta a#gs)#es"
    and allocation: "lp_cut_check_meta m a gs es body"
    and link: "lpc_check_link fuel Q nds nd (LPCGoals (body@gs)#LPCBarrier m#es)
      (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked by (simp_all add: LPCAMeta)
  have child: "SN_on (source P) {lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta>}"
    by (rule plain_link_sound[OF program link known ih])
  show ?thesis
  proof (rule allocation_reflects_SN[where m=m, OF program _ child])
    fix t assume st: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t)\<in>source P"
    show "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
      (lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta>)"
      by (rule checked_meta_covers[OF allocation]) (use st in \<open>simp only: shape\<close>)
  qed
next
  case (LPCAResolution a gs c m es k l A successor anchors bindings mode yes no)
  have resolve: "lpc_check_resolution_node fuel P Q nds nd a gs c m es k l A successor anchors bindings mode yes no"
    using checked by (simp add: LPCAResolution)
  show ?thesis by (rule resolution_node_sound[OF program resolve known ih])
next
  case (LPCAEquality a b gs es k l successor mode yes no)
  have eq: "lpc_check_equality_node fuel P Q nds nd a b gs es k l successor mode yes no"
    using checked by (simp add: LPCAEquality)
  show ?thesis by (rule equality_node_sound[OF program eq known ih])
qed

theorem table_sound:
  assumes checked: "lpc_check_table fuel P Q nds actions"
    and bound: "i<length nds"
    and known: "knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) \<eta>"
    and child: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map \<eta> (lpcn_vars (nds!i)))]}"
  shows "SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!i)) \<eta>}"
proof -
  have all: "SN_on (lp_ild Q) {xs} \<and>
    (\<forall>j \<nu>. j<length nds \<longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<longrightarrow>
      xs=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))] \<longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>})"
    if sn: "SN_on (lp_ild Q) {xs}" for xs
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix xs
    assume ih: "\<And>ys. (xs,ys)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      SN_on (lp_ild Q) {ys} \<and>
      (\<forall>j \<nu>. j<length nds \<longrightarrow>
        knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<longrightarrow>
        ys=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))] \<longrightarrow>
        SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>})"
    have current: "SN_on (lp_ild Q) {xs}"
      by (rule step_reflects_SN_on) (use ih in \<open>blast intro: r_into_trancl\<close>)
    show "SN_on (lp_ild Q) {xs} \<and>
      (\<forall>j \<nu>. j<length nds \<longrightarrow>
        knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<longrightarrow>
        xs=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))] \<longrightarrow>
        SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>})"
    proof (intro conjI allI impI)
      show "SN_on (lp_ild Q) {xs}" by (rule current)
    next
      fix j \<nu>
      assume member: "j<length nds"
        and knowledge: "knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu>"
        and xs: "xs=[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]"
      have program: "lp_cut_source_program P"
        and action: "lpc_check_action fuel P Q nds (nds!j) (actions!j)"
        using checked member by (auto simp: lpc_check_table_def list_all_iff)
      have residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]}"
        using current xs by simp
      show "SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
        by (rule action_sound[OF program action knowledge residual])
          (use ih xs in \<open>blast intro: r_into_trancl\<close>)+
    qed
  qed
  show ?thesis using all[OF child] bound known by blast
qed
theorem root_table_sound:
  fixes ts :: "('f lp_cut_symbol,string) term list"
    and p d :: "'f lp_cut_symbol\<Rightarrow>'b"
  assumes checked: "lpc_check_root_table fuel P Q nds acts r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_ild (lp_roles_program p d Q))
        {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
  shows "SN_on (source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?nd = "nds!r"
  let ?vs = "lpcn_vars ?nd"
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?env = "lp_cut_query_env ?vs ?vals"
  have root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and table: "lpc_check_table fuel P Q nds acts" and bound: "r<length nds"
    using checked by (auto simp: lpc_check_root_table_def)
  have lengths: "length ?vs=length ?vals" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env ?vs=?vals" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_index: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> lp_seg_ground (?vals!i)"
    using ground len by (auto simp: lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have finite: "\<forall>(t,b)\<in>set (zip ?vals modes). b \<longrightarrow> lp_seg_ground t"
    using finite_index len by (auto simp: in_set_zip)
  have finite': "\<forall>(t,b)\<in>set (zip (map ?env ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using finite by (simp only: vals)
  have domain: "\<forall>x. D (?env x)"
    by (intro allI; rule query_env_domain)
      (auto intro: valuation_domain variables)
  have known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?env"
    using root finite' domain by (auto simp: lp_cut_check_root_def knowledge_def zip_map1)
  have mapped: "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred ?nd),map (\<lambda>t. lp_ieval t LPIVar) (map (map_term d id) ts))]}"
    by (rule child) (use len ground in \<open>auto simp: lpc_positions_def\<close>)
  have residual: "SN_on (lp_ild Q) {[(lpcn_pred ?nd,map ?env ?vs)]}"
    by (rule lp_roles_termination_reflect[where p=p and d=d])
      (use mapped vals in \<open>simp add: lp_roles_iatom_def map_map o_def lp_map_finite_eval\<close>)
  have source: "SN_on (source P) {lp_cut_state_eval (lpcn_state ?nd) ?env}"
    by (rule table_sound[OF table bound known residual])
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


end
end
