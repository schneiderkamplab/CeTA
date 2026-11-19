theory LP_Cut_Domain_Nodes
  imports LP_Cut_Domain_Link
begin

context cut_runtime_domain
begin

lemma source_clause_cases:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
  assumes "(LPCClause (LPCAtom a#gs) c m#es,t)\<in>source P"
  shows "(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) gs)#es) \<or>
    (t=es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>))"
  using assms by (cases rule: source.cases) auto

lemma source_unify_cases:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
  assumes "(LPCGoals (LPCUnify a b#gs)#es,t)\<in>source P"
  shows "(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and>
      lp_isubst a \<sigma> = lp_isubst b \<sigma> \<and>
      t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) gs)#es) \<or>
    (t=es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and>
      lp_isubst a \<sigma> = lp_isubst b \<sigma>))"
  using assms by (cases rule: source.cases) auto

theorem resolution_node_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_resolution_node fuel P Q nds nd a gs c m es k l A next anchors match_bindings mode yes no"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (rule step_reflects_SN_on)
  fix t assume step: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t) \<in> source P"
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode"
    and source: "(LPCClause (LPCAtom (lp_ieval a \<eta>)#?gs) c m#?es,t)\<in>source P"
    using checked step by (auto simp: lpc_check_resolution_node_def lp_cut_state_map_def)
  from source_clause_cases[OF source] show "SN_on (source P) {t}"
  proof
    assume "\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> \<rho> where ds: "\<And>x. D (\<sigma> x)"
      and dr: "\<And>x. D (\<rho> x)" and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      and result: "t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lp_cut_coverage_failure[OF coverage] unifier by blast
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c m es next anchors"
      and short: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      and link: "lpc_check_link fuel Q nds nd (LPCGoals next#es)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c))) yes"
      using checked possible by (auto simp: lpc_check_resolution_node_def)
    let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
    have kl: "k\<le>l" using resolve by (auto simp: lp_cut_check_resolution_def)
    have equations: "lp_equations (lp_cut_resolution_equations k l ?G a (fst (P!c))) ?env"
      by (rule resolution_equations[OF resolve known unifier])
    have old: "map ?env (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl short])
    have prior: "knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using resolution_success(2)[OF resolve known unifier ds dr]
      by (simp add: lp_cut_anchor_vars_def)
    have negative: "list_all (\<lambda>g. guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule negative_guards[OF _ _ known ds])
        (use resolve in \<open>auto simp: lp_cut_check_resolution_def\<close>)
    have knowledge: "knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using prior negative by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have sn: "SN_on (source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule link_sound[OF program link equations old knowledge ih])
    show ?thesis using sn result resolution_success(1)[OF resolve known unifier ds dr]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      proof
      assume mode: "mode=LPCAlwaysSuccess"
      have "cut_domain_head D a (fst (P!c)) \<eta>"
        by (rule coverage_success[OF coverage[unfolded mode] knowledge_domain[OF known]])
      then show False using failure by (simp add: cut_domain_head_def)
    qed
    have link: "lpc_check_link fuel Q nds nd es ?G
      (?K@[LPCHeadGuard a (fst (P!c)) False]) [] no"
      using checked possible by (simp add: lpc_check_resolution_node_def)
    have knowledge: "knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) \<eta>"
      using known failure by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have "SN_on (source P) {lp_cut_state_eval es \<eta>}"
      by (rule plain_link_sound[OF program link knowledge ih])
    then show ?thesis using failure by simp
  qed
qed
theorem equality_node_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_equality_node fuel P Q nds nd a b gs es k l next mode yes no"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (rule step_reflects_SN_on)
  fix t assume step: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t) \<in> source P"
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set ?G),b\<cdot>lp_cut_refresh k (set ?G))]"
  have coverage: "lp_cut_check_equality fuel a b mode"
    and source: "(LPCGoals (LPCUnify (lp_ieval a \<eta>) (lp_ieval b \<eta>)#?gs)#?es,t)\<in>source P"
    using checked step by (auto simp: lpc_check_equality_node_def lp_cut_state_map_def)
  from source_unify_cases[OF source] show "SN_on (source P) {t}"
  proof
    assume "\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and>
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma> \<and>
      t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> where ds: "\<And>x. D (\<sigma> x)" and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
      and result: "t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lp_cut_equality_failure coverage unifier by blast
    have resolve: "lp_cut_check_unify fuel k l ?G ?K a b gs es next"
      and short: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      and link: "lpc_check_link fuel Q nds nd (LPCGoals next#es) ?G
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?eqs yes"
      using checked possible by (auto simp: lpc_check_equality_node_def)
    let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<eta>"
    have kl: "k\<le>l" using resolve by (auto simp: lp_cut_check_unify_def)
    have equations: "lp_equations ?eqs ?env"
      by (rule unify_equations[OF resolve known unifier])
    have old: "map ?env (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl short])
    have prior: "knowledge (set ?G) (?K@[LPCEqGuard a b True]) ?env"
      by (rule unify_success(2)[OF resolve known unifier ds])
    have negative: "list_all (\<lambda>g. guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule negative_guards[OF _ _ known ds])
        (use resolve in \<open>auto simp: lp_cut_check_unify_def\<close>)
    have knowledge: "knowledge (set ?G) (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?env"
      using prior negative by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have sn: "SN_on (source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule link_sound[OF program link equations old knowledge ih])
    show ?thesis using sn result unify_success(1)[OF resolve known unifier ds]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and>
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      proof
      assume mode: "mode=LPCAlwaysSuccess"
      have "cut_domain_equality D a b \<eta>"
        by (rule equality_success[OF coverage[unfolded mode]])
      then show False using failure by (simp add: cut_domain_equality_def)
    qed
    have link: "lpc_check_link fuel Q nds nd es ?G (?K@[LPCEqGuard a b False]) [] no"
      using checked possible by (simp add: lpc_check_equality_node_def)
    have knowledge: "knowledge (set ?G) (?K@[LPCEqGuard a b False]) \<eta>"
      using known failure by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have "SN_on (source P) {lp_cut_state_eval es \<eta>}"
      by (rule plain_link_sound[OF program link knowledge ih])
    then show ?thesis using failure by simp
  qed
qed

end
end
