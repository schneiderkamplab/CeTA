theory LP_Cut_Domain_Precise_Resolution
  imports LP_Cut_Domain_Precise_Link LP_Cut_Domain_MGU_Head LP_Cut_Domain_Free_Coverage
begin

text \<open>Domain-specific soundness for the existing executable checks.\<close>

context cut_runtime_domain
begin

lemma precise_clause_cases:
  fixes P :: "('f,string) lp_cut_program"
  assumes "(LPCClause (LPCAtom a#gs) c m#es,t)\<in>precise_source P"
  shows "(\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<and>
    t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) gs)#es) \<or>
    (t=es \<and> \<not>(\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>))"
  using assms by (cases rule: precise_source.cases) auto

theorem precise_resolution_node_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_mgu_check_resolution_node fuel P Q nds Fs nd F a gs c m es k l A next anchors match_bindings mode yes no"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (precise_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (rule step_reflects_SN_on)
  fix t assume step: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t) \<in> precise_source P"
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode \<or>
      (mode=LPCAlwaysSuccess \<and> lpc_check_free_call F a (fst (P!c)))"
    and source: "(LPCClause (LPCAtom (lp_ieval a \<eta>)#?gs) c m#?es,t)\<in>precise_source P"
    using checked step by (auto simp: lpc_mgu_check_resolution_node_def lp_cut_state_map_def)
  from precise_clause_cases[OF source] show "SN_on (precise_source P) {t}"
  proof
    assume "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      mgu_resolve (lp_ieval a \<eta>) ?gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> \<rho> where mgu:
      "mgu_resolve (lp_ieval a \<eta>) ?gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho>"
      and result: "t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    have unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      using mgu by (simp add: mgu_resolve_def)
    have ds: "\<And>x. D (\<sigma> x)" and dr: "\<And>x. D (\<rho> x)"
      using mgu by (auto simp: mgu_resolve_def)
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using coverage lp_cut_coverage_failure[of fuel k a "fst (P!c)" match_bindings mode] unifier by auto
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c m es next anchors"
      and short: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      and link: "lpc_check_link fuel Q nds nd (LPCGoals next#es)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c))) yes"
      and free_link: "lpc_check_link_free fuel (lp_cut_resolution_equations k l ?G a (fst (P!c)))
        (lpc_mgu_result_free F ?G a (fst (P!c)) (snd (P!c)) l) (Fs!lpcl_target yes) (lpcl_bindings yes)"
      using checked possible by (auto simp: lpc_mgu_check_resolution_node_def)
    let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
    have kl: "k\<le>l" using resolve by (auto simp: lp_cut_check_resolution_def)
    have equations: "lp_equations (lp_cut_resolution_equations k l ?G a (fst (P!c))) ?env"
      by (rule resolution_equations[OF resolve known unifier])
    have old: "map ?env (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl short])
    have prior: "knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using resolution_success(2)[OF resolve known unifier ds dr] by (simp add: lp_cut_anchor_vars_def)
    have negative: "list_all (\<lambda>g. guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule negative_guards[OF _ _ known ds])
        (use resolve in \<open>auto simp: lp_cut_check_resolution_def\<close>)
    have knowledge: "knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using prior negative by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (\<eta> x)"
      using known by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have body_free: "lpc_free_knowledge (set (lpc_mgu_result_free F ?G a (fst (P!c)) (snd (P!c)) l)) ?env"
      by (rule mgu_result_free_sound[OF mgu free ground])
    have sn: "SN_on (precise_source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule precise_link_sound[OF program link free_link equations old knowledge body_free ih])
    show ?thesis using sn result resolution_success(1)[OF resolve known unifier ds dr]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
    proof
      assume success: "mode=LPCAlwaysSuccess"
      have unifies: "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
        (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and> lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      proof (cases "lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode")
        case True
        have "cut_domain_head D a (fst (P!c)) \<eta>"
          by (rule coverage_success[OF True[unfolded success] knowledge_domain[OF known]])
        then show ?thesis by (simp add: cut_domain_head_def)
      next
        case False
        then have "lpc_check_free_call F a (fst (P!c))" using coverage by blast
        then show ?thesis by (rule check_free_call_sound[OF _ free])
      qed
      then show False using failure by blast
    qed
    have link: "lpc_check_link fuel Q nds nd es ?G
        (?K@[LPCHeadGuard a (fst (P!c)) False]) [] no"
      and free_link: "lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)"
      using checked possible by (auto simp: lpc_mgu_check_resolution_node_def)
    have knowledge: "knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) \<eta>"
      using known failure by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    have sn: "SN_on (precise_source P) {lp_cut_state_eval es \<eta>}"
      by (rule precise_link_sound[OF program link free_link _ refl knowledge free ih])
        (simp add: lp_equations_def)
    then show ?thesis using failure by simp
  qed
qed

end
end
