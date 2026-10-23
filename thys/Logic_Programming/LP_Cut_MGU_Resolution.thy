theory LP_Cut_MGU_Resolution
  imports LP_Cut_MGU_Link LP_Cut_Table_Resolution LP_Cut_MGU_Head_Knowledge
begin

definition lpc_mgu_body_free where
  "lpc_mgu_body_free h bs l = map (lp_prefix l) (sorted_list_of_set (lpc_body_only_variables h bs))"

lemma lpc_body_only_variables_finite:
  "finite (lpc_body_only_variables h bs)"
  by (simp add: lpc_body_only_variables_def)

lemma lpc_mgu_body_free_sound:
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
  shows "lpc_free_knowledge (set (lpc_mgu_body_free h bs l))
    (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)"
proof -
  let ?F = "lpc_body_only_variables h bs"
  have known: "lpc_free_knowledge ?F \<rho>" by (rule lpc_mgu_body_only_knowledge[OF mgu])
  have env: "\<And>x. lp_cut_resolution_env k l \<eta> \<sigma> \<rho> (lp_prefix l x) = \<rho> x"
    by (simp add: lp_cut_resolution_env_def lp_prefix_def)
  have source: "set (lpc_mgu_body_free h bs l) = lp_prefix l ` ?F"
    by (simp add: lpc_mgu_body_free_def lpc_body_only_variables_finite)
  show ?thesis using known
    by (auto simp: source lpc_free_knowledge_def inj_on_def env)
qed

lemma lpc_mgu_source_clause_cases:
  fixes P :: "('f,string) lp_cut_program"
  assumes "(LPCClause (LPCAtom a#gs) c m#es,t)\<in>lp_cut_mgu_source P"
  shows "(\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<and>
    t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) gs)#es) \<or>
    (t=es \<and> \<not>(\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>))"
  using assms by (cases rule: lp_cut_mgu_source.cases) auto

definition lpc_mgu_check_resolution_node where
  "lpc_mgu_check_resolution_node fuel P Q nds Fs nd F a gs c m es k l A next anchors match_bindings mode yes no =
    (c<length P \<and>
     lpcn_state nd=LPCClause (LPCAtom a#gs) c m#es \<and>
     (lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode \<or>
      (mode=LPCAlwaysSuccess \<and> lpc_check_free_call F a (fst (P!c)))) \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
       lp_cut_check_resolution P fuel k l (lpcn_ground nd) A (lpcn_guards nd)
         a gs c m es next anchors \<and>
       (\<forall>x\<in>set (lpcn_vars nd). length x<k) \<and>
       lpc_check_link fuel Q nds nd (LPCGoals next#es)
         (lpcn_ground nd@sorted_list_of_set (lp_cut_anchor_vars anchors))
         (lpcn_guards nd@lpc_negative_guards k (set (lpcn_ground nd)) (lpcn_guards nd)@[LPCHeadGuard a (fst (P!c)) True])
         (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c))) yes \<and>
       lpc_check_link_free fuel (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c)))
         (lpc_mgu_result_free F (lpcn_ground nd) a (fst (P!c)) (snd (P!c)) l) (Fs!lpcl_target yes) (lpcl_bindings yes)) \<and>
     (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
       lpc_check_link fuel Q nds nd es (lpcn_ground nd)
         (lpcn_guards nd@[LPCHeadGuard a (fst (P!c)) False]) [] no \<and>
       lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)))"

theorem lpc_mgu_resolution_node_sound:
  fixes P :: "('a,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_mgu_check_resolution_node fuel P Q nds Fs nd F a gs c m es k l A next anchors match_bindings mode yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ih: "\<And>j \<nu>. j<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) \<nu> \<Longrightarrow>
      lpc_free_knowledge (set (Fs!j)) \<nu> \<Longrightarrow>
      ([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],
       [(lpcn_pred (nds!j),map \<nu> (lpcn_vars (nds!j)))]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state (nds!j)) \<nu>}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof (rule step_reflects_SN_on)
  fix t assume step: "(lp_cut_state_eval (lpcn_state nd) \<eta>,t) \<in> lp_cut_mgu_source P"
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode \<or>
      (mode=LPCAlwaysSuccess \<and> lpc_check_free_call F a (fst (P!c)))"
    and source: "(LPCClause (LPCAtom (lp_ieval a \<eta>)#?gs) c m#?es,t)\<in>lp_cut_mgu_source P"
    using checked step by (auto simp: lpc_mgu_check_resolution_node_def lp_cut_state_map_def)
  from lpc_mgu_source_clause_cases[OF source] show "SN_on (lp_cut_mgu_source P) {t}"
  proof
    assume "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm.
      lpc_mgu_resolve (lp_ieval a \<eta>) ?gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<and>
      t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> \<rho> where mgu:
      "lpc_mgu_resolve (lp_ieval a \<eta>) ?gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho>"
      and result: "t=LPCGoals (map (lp_cut_bind m (\<lambda>u. lp_ieval u \<rho>)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es" by blast
    have unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      using mgu by (simp add: lpc_mgu_resolve_def)
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
      by (rule lp_cut_checked_resolution_equations[OF resolve known unifier])
    have old: "map ?env (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl short])
    have prior: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using lp_cut_check_resolution_success(2)[OF resolve known unifier] by (simp add: lp_cut_anchor_vars_def)
    have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule lpc_negative_guards_sound[OF _ _ known])
        (use resolve in \<open>auto simp: lp_cut_check_resolution_def\<close>)
    have knowledge: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using prior negative by (simp add: lp_cut_knowledge_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (\<eta> x)"
      using known by (simp add: lp_cut_knowledge_def)
    have body_free: "lpc_free_knowledge (set (lpc_mgu_result_free F ?G a (fst (P!c)) (snd (P!c)) l)) ?env"
      by (rule lpc_mgu_result_free_sound[OF mgu free ground])
    have sn: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule lpc_mgu_link_sound[OF program link free_link equations old knowledge body_free ih])
    show ?thesis using sn result lp_cut_check_resolution_success(1)[OF resolve known unifier]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
    proof
      assume success: "mode=LPCAlwaysSuccess"
      have unifies: "\<exists>\<sigma> \<rho> :: string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm.
        lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
      proof (cases "lp_cut_check_coverage fuel k a (fst (P!c)) match_bindings mode")
        case True then show ?thesis using lp_cut_coverage_success[OF True] success by blast
      next
        case False
        then have "lpc_check_free_call F a (fst (P!c))" using coverage by blast
        then show ?thesis by (rule lpc_check_free_call_sound[OF _ free])
      qed
      then show False using failure by blast
    qed
    have link: "lpc_check_link fuel Q nds nd es ?G
        (?K@[LPCHeadGuard a (fst (P!c)) False]) [] no"
      and free_link: "lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)"
      using checked possible by (auto simp: lpc_mgu_check_resolution_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) \<eta>"
      using known failure by (simp add: lp_cut_knowledge_def)
    have sn: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval es \<eta>}"
      by (rule lpc_mgu_link_sound[OF program link free_link _ refl knowledge free ih])
        (simp add: lp_equations_def)
    then show ?thesis using failure by simp
  qed
qed

end
