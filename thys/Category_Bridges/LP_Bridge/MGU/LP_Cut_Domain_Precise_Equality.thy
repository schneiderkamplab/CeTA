theory LP_Cut_Domain_Precise_Equality
  imports LP_Cut_Domain_Precise_Link
begin

text \<open>Domain-specific soundness for the existing executable checks.\<close>

context cut_runtime_domain
begin

theorem precise_equality_node_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lp_cut_source_program P"
    and checked: "lpc_check_equality_node fuel P Q nds nd a b gs es k l next mode yes no"
    and free_success: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpc_check_link_free fuel [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd)))]
        [] (Fs!lpcl_target yes) (lpcl_bindings yes)"
    and free_failure: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpc_check_link_free fuel [] F (Fs!lpcl_target no) (lpcl_bindings no)"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) \<eta>"
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
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set ?G),b\<cdot>lp_cut_refresh k (set ?G))]"
  have coverage: "lp_cut_check_equality fuel a b mode"
    and source: "(LPCGoals (LPCUnify (lp_ieval a \<eta>) (lp_ieval b \<eta>)#?gs)#?es,t)\<in>source P"
    using checked step precise_source_subset[of P] by (auto simp: lpc_check_equality_node_def lp_cut_state_map_def)
  from source_unify_cases[OF source] show "SN_on (precise_source P) {t}"
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
    have sn: "SN_on (precise_source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
      by (rule precise_link_sound[OF program link free_success[OF possible] equations old knowledge _ ih])
        (simp add: lpc_free_knowledge_def)
    show ?thesis using sn result unify_success(1)[OF resolve known unifier ds]
      by (simp add: map_map o_def lp_cut_map_comp)
  next
    assume failure: "t=?es \<and> \<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and> lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>)"
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
    have "SN_on (precise_source P) {lp_cut_state_eval es \<eta>}"
      by (rule precise_link_sound[OF program link free_failure[OF possible] _ refl knowledge free ih])
        (simp add: lp_equations_def)
    then show ?thesis using failure by simp
  qed
qed

end
end
