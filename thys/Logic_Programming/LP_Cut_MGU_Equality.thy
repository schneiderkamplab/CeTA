theory LP_Cut_MGU_Equality
  imports LP_Cut_MGU_Resolution LP_Cut_Table_Equality
begin

theorem lpc_mgu_equality_node_sound:
  fixes P :: "('a,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_equality_node fuel P Q nds nd a b gs es k l next mode yes no"
    and free_success: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpc_check_link_free fuel [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd)))]
        [] (Fs!lpcl_target yes) (lpcl_bindings yes)"
    and free_failure: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
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
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set ?G),b\<cdot>lp_cut_refresh k (set ?G))]"
  have coverage: "lp_cut_check_equality fuel a b mode"
    and source: "(LPCGoals (LPCUnify (lp_ieval a \<eta>) (lp_ieval b \<eta>)#?gs)#?es,t)\<in>lp_cut_source P"
    using checked step lp_cut_mgu_source_subset[of P] by (auto simp: lpc_check_equality_node_def lp_cut_state_map_def)
  from lp_cut_source_unify_cases[OF source] show "SN_on (lp_cut_mgu_source P) {t}"
  proof
    assume "\<exists>\<sigma>::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma> \<and>
      t=LPCGoals (map (lp_cut_map (\<lambda>u. lp_isubst u \<sigma>)) ?gs)#?es"
    then obtain \<sigma> where unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
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
      by (rule lp_cut_checked_unify_equations[OF resolve known unifier])
    have old: "map ?env (lpcn_vars nd)=map \<eta> (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl short])
    have prior: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b True]) ?env"
      by (rule lp_cut_checked_unify_success(2)[OF resolve known unifier])
    have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule lpc_negative_guards_sound[OF _ _ known])
        (use resolve in \<open>auto simp: lp_cut_check_unify_def\<close>)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?env"
      using prior negative by (simp add: lp_cut_knowledge_def)
    have sn: "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule lpc_mgu_link_sound[OF program link free_success[OF possible] equations old knowledge _ ih])
        (simp add: lpc_free_knowledge_def)
    show ?thesis using sn result lp_cut_checked_unify_success(1)[OF resolve known unifier]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      using lp_cut_equality_success coverage failure by blast
    have link: "lpc_check_link fuel Q nds nd es ?G (?K@[LPCEqGuard a b False]) [] no"
      using checked possible by (simp add: lpc_check_equality_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b False]) \<eta>"
      using known failure by (simp add: lp_cut_knowledge_def)
    have "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval es \<eta>}"
      by (rule lpc_mgu_link_sound[OF program link free_failure[OF possible] _ refl knowledge free ih])
        (simp add: lp_equations_def)
    then show ?thesis using failure by simp
  qed
qed


end

