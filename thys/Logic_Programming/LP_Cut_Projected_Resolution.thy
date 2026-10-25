theory LP_Cut_Projected_Resolution
  imports LP_Cut_Projected_Link
begin

definition lpc_check_projected_resolution_node where
  "lpc_check_projected_resolution_node fuel filtering R P Q nds states nd a gs c m active saved k l A next anchors bindings mode outputs yes no refresh_vars left_term right_term =
    (lpc_check_return_resolution_node fuel P Q nds states nd a gs c m active saved k l A next anchors bindings mode outputs yes no \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow> lpc_check_refreshed_link fuel filtering R k (lpcn_ground nd) refresh_vars
       (lp_cut_resolution_equations k l (lpcn_ground nd) a (fst (P!c))) nd nds yes left_term right_term) \<and>
     (mode\<noteq>LPCAlwaysSuccess \<longrightarrow> lpc_check_projected_link_rule filtering R nd nds no))"

theorem lpc_projected_resolution_node_sound:
  assumes checked: "lpc_check_projected_resolution_node fuel filtering R P Q nds states nd a gs c m active saved k l A next anchors bindings mode outputs yes no refresh_vars left_term right_term"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?a = "lp_ieval a eta"
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?ret = "lpc_return_env active eta"
  have base: "lpc_check_resolution_node fuel P Q nds nd a gs c m (map fst saved) k l A next anchors bindings mode yes no"
    using checked by (simp add: lpc_check_projected_resolution_node_def lpc_check_return_resolution_node_def)
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode"
    using base by (simp add: lpc_check_resolution_node_def)
  have st: "lpc_answer_transition P ((LPCClause (LPCAtom ?a#?gs) c m,?ret)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have cases: "(\<exists>sigma rho.
      lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved) \<or>
    (event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm. \<exists>rho.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho))"
    using st by (cases rule: lpc_answer_transition.cases)
      (auto simp: lpc_mgu_resolve_def)
  from cases show ?thesis
  proof
    assume "\<exists>sigma rho. lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved"
    then obtain sigma rho where eq: "lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho"
      and event: "event=None" and result: "tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs), (\<lambda>n. lp_isubst (?ret n) sigma))#?saved" by blast
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lp_cut_coverage_failure[OF coverage] eq by blast
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c m (map fst saved) next anchors"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_check_resolution_node_def)
    have payload: "lpc_check_return_values fuel k ?G (lp_cut_resolution_equations k l ?G a (fst (P!c)))
      active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpc_check_return_table_link fuel Q nds states nd ((LPCGoals next,outputs)#saved)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c))) yes"
      using checked possible by (auto simp: lpc_check_projected_resolution_node_def lpc_check_return_resolution_node_def)
    let ?env = "lp_cut_resolution_env k l eta sigma rho"
    have same: "tt=lpc_return_eval ?env ((LPCGoals next,outputs)#saved)"
      using result lpc_return_resolution_success[OF resolve known eq payload short]
      by (simp add: map_map o_def lp_cut_map_comp)
    have equations: "lp_equations (lp_cut_resolution_equations k l ?G a (fst (P!c))) ?env"
      by (rule lp_cut_checked_resolution_equations[OF resolve known eq])
    have kl: "k\<le>l" using resolve by (auto simp: lp_cut_check_resolution_def)
    have old: "map ?env (lpcn_vars nd)=map eta (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl parent])
    have prior: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using lp_cut_check_resolution_success(2)[OF resolve known eq]
      by (simp add: lp_cut_anchor_vars_def)
    have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule lpc_negative_guards_sound[OF _ _ known])
        (use resolve in \<open>auto simp: lp_cut_check_resolution_def\<close>)
    have knowledge: "lp_cut_knowledge (set (?G@sorted_list_of_set (lp_cut_anchor_vars anchors)))
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True]) ?env"
      using prior negative by (simp add: lp_cut_knowledge_def)
    have refreshed: "lpc_check_refreshed_link fuel filtering R k ?G refresh_vars
        (lp_cut_resolution_equations k l ?G a (fst (P!c))) nd nds yes left_term right_term"
      using checked possible by (simp add: lpc_check_projected_resolution_node_def)
    have bounds: "2 * k \<le> l" using resolve by (simp add: lp_cut_check_resolution_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)" using known by (simp add: lp_cut_knowledge_def)
    show ?thesis using lpc_projected_refreshed_link_sound[OF refreshed initial link bounds ground equations knowledge]
      event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>('a lp_cut_symbol,string) lp_iterm. \<exists>rho.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      using lp_cut_coverage_success[OF coverage] failure by blast
    have link: "lpc_check_return_table_link fuel Q nds states nd saved ?G
      (?K@[LPCHeadGuard a (fst (P!c)) False]) [] no"
      using checked possible by (simp add: lpc_check_projected_resolution_node_def lpc_check_return_resolution_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) eta"
      using known failure by (simp add: lp_cut_knowledge_def)
    have rule: "lpc_check_projected_link_rule filtering R nd nds no"
      using checked possible by (simp add: lpc_check_projected_resolution_node_def)
    show ?thesis using lpc_projected_checked_link_sound[OF rule initial link _ refl knowledge] failure
      by (simp add: lp_equations_def)
  qed
qed

end
