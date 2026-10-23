theory LP_Cut_Table_Resolution
  imports LP_Cut_Table_Link
begin

lemma lpc_plain_link_sound:
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_link fuel Q nds nd s G K [] e"
    and known: "lp_cut_knowledge (set G) K \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval s \<eta>}"
  by (rule lpc_link_sound[OF program checked _ refl known ih])
    (simp add: lp_equations_def)

definition lpc_check_resolution_node where
  "lpc_check_resolution_node fuel P Q nds nd a gs c m es k l A next anchors match_bindings mode yes no =
    (c<length P \<and>
     lpcn_state nd=LPCClause (LPCAtom a#gs) c m#es \<and>
     lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
       lp_cut_check_resolution P fuel k l (lpcn_ground nd) A (lpcn_guards nd)
         a gs c m es next anchors \<and>
       (\<forall>x\<in>set (lpcn_vars nd). length x<k) \<and>
       lpc_check_link fuel Q nds nd (LPCGoals next#es)
         (lpcn_ground nd@sorted_list_of_set (lp_cut_anchor_vars anchors))
         (lpcn_guards nd@[LPCHeadGuard a (fst (P!c)) True])
         (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c))) yes) \<and>
     (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
       lpc_check_link fuel Q nds nd es (lpcn_ground nd)
         (lpcn_guards nd@[LPCHeadGuard a (fst (P!c)) False]) [] no))"

theorem lpc_resolution_node_sound:
  fixes P :: "('a,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_resolution_node fuel P Q nds nd a gs c m es k l A next anchors match_bindings mode yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (rule step_reflects_SN_on)
  fix t assume step: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t) \<in> lp_cut_source P"
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode"
    and source: "(LPCClause (LPCAtom (lp_ieval a \<eta>)#?gs) c m#?es,t)\<in>lp_cut_source P"
    using checked step by (auto simp: lpc_check_resolution_node_def lp_cut_state_map_def)
  from lp_cut_source_clause_cases[OF source] show "SN_on (lp_cut_source P) {t}"
  proof
    assume "\<exists>\<sigma>::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> \<rho> where unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      and result: "t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lp_cut_coverage_failure[OF coverage] unifier by blast
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c m es next anchors"
      and short: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      and link: "lpc_check_link fuel Q nds nd (LPCGoals next#es)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c))) yes"
      using checked possible by (auto simp: lpc_check_resolution_node_def)
    let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
    have kl: "k\<le>l" using resolve by (auto simp: lp_cut_check_resolution_def)
    have equations: "lp_equations (lp_cut_resolution_equations k l ?G a (fst (P!c))) ?env"
      by (rule lp_cut_checked_resolution_equations[OF resolve known unifier])
    have old: "map ?env (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl short])
    have knowledge: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using lp_cut_check_resolution_success(2)[OF resolve known unifier]
      by (simp add: lp_cut_anchor_vars_def)
    have sn: "SN_on (lp_cut_source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule lpc_link_sound[OF program link equations old knowledge ih])
    show ?thesis using sn result lp_cut_check_resolution_success(1)[OF resolve known unifier]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      using lp_cut_coverage_success[OF coverage] failure by blast
    have link: "lpc_check_link fuel Q nds nd es ?G
      (?K@[LPCHeadGuard a (fst (P!c)) False]) [] no"
      using checked possible by (simp add: lpc_check_resolution_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) \<eta>"
      using known failure by (simp add: lp_cut_knowledge_def)
    have "SN_on (lp_cut_source P) {lp_cut_state_eval es \<eta>}"
      by (rule lpc_plain_link_sound[OF program link knowledge ih])
    then show ?thesis using failure by simp
  qed
qed

end
