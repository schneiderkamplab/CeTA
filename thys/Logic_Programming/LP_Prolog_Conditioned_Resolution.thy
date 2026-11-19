theory LP_Prolog_Conditioned_Resolution
 imports LP_Prolog_Conditioned_Equality LP_Prolog_Head_Successor_Facts
begin

text \<open>Resolution acquires separation only in its actual successful clause
environment. The failure branch has an independent transport obligation in the
original environment, including saved alternatives and return interfaces.\<close>

theorem lpp_conditioned_functor_resolution_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m active saved k l A next anchors bindings mode outputs source_context source_functors yes no"
    and success_conditions: "\<And>sigma rho. lpc_mgu_resolve (lp_ieval a eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
      node_conditions (lpcl_target yes)
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
          (lp_cut_resolution_env k l eta sigma rho))"
    and failure_conditions: "node_conditions (lpcl_target no)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions (lpc_return_scope_word swaps tt) u)"
proof -
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?a = "lp_ieval a eta"
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?ret = "lpc_return_env active eta"
  have base: "lpc_return_free_resolution_base fuel P Q nds Fs nd F a gs c m (map fst saved) k l A next anchors bindings mode yes no"
    using checked by (simp add: lpp_check_functor_resolution_node_def)
  have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode \<or>
    (mode=LPCAlwaysSuccess \<and> (lpc_check_free_call F a (fst (P!c)) \<or>
       lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))))"
    using base by (simp add: lpc_return_free_resolution_base_def)
  have st: "lpc_answer_transition P ((LPCClause (LPCAtom ?a#?gs) c m,?ret)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have cases: "(\<exists>sigma rho.
      lpc_mgu_resolve ?a ?gs (fst (P!c)) (snd (P!c)) sigma rho \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved) \<or>
    (event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho))"
    using st by (cases rule: lpc_answer_transition.cases) auto
  from cases show ?thesis
  proof
    assume "\<exists>sigma rho. lpc_mgu_resolve ?a ?gs (fst (P!c)) (snd (P!c)) sigma rho \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs), (\<lambda>n. lp_isubst (?ret n) sigma))#?saved"
    then obtain sigma rho where mgu: "lpc_mgu_resolve ?a ?gs (fst (P!c)) (snd (P!c)) sigma rho"
      and event: "event=None" and result: "tt=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
        map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs), (\<lambda>n. lp_isubst (?ret n) sigma))#?saved" by blast
    have eq: "lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho"
      using mgu by (simp add: lpc_mgu_resolve_def)
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using coverage lp_cut_coverage_failure[of fuel k a "fst (P!c)" bindings mode] eq by auto
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c m (map fst saved) next anchors"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_return_free_resolution_base_def)
    have payload: "lpc_check_return_values fuel k ?G (lp_cut_resolution_equations k l ?G a (fst (P!c)))
      active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpp_check_evaluation_functor_link_free_choices T yes_facts fuel Q nds states contexts Fs functor_contexts nd ((LPCGoals next,outputs)#saved)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c)))
        (lpc_return_resolution_free fuel F ?G a gs (fst (P!c)) (snd (P!c)) k l) (lpp_saved_free k F) (lpp_evaluation_fork_context source_context k (set (lpcn_ground nd))) (lpp_functor_fork_context source_functors k (set ?G)) yes"
      using checked possible by (auto simp: lpp_check_functor_resolution_node_def)
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
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
      using known by (simp add: lp_cut_knowledge_def)
    have bounds: "2 * k \<le> l" using resolve by (simp add: lp_cut_check_resolution_def)
    have body_free: "lpc_free_knowledge (set (lpc_return_resolution_free fuel F ?G a gs (fst (P!c)) (snd (P!c)) k l)) ?env"
      by (rule lpc_return_resolution_free_sound[OF mgu free ground bounds])
    have context_short: "lpp_context_short k source_context"
      using checked possible by (simp add: lpp_check_functor_resolution_node_def)
    have functor_short: "lpp_functor_context_short k source_functors"
      using checked possible by (simp add: lpp_check_functor_resolution_node_def)
    have forked: "list_all (lpp_functor_fact_holds names ?env)
      (lpp_functor_fork_context source_functors k (set ?G))"
      by (rule lpp_functor_context_fork_sound[OF functors functor_short bounds ground])
    have facts: "lpp_stable_context_holds operation SP
      (lpp_evaluation_fork_context source_context k (set ?G)) ?env"
      by (rule lpp_stable_context_fork_sound[OF observed context_short bounds ground])
    have saved_free: "lpc_free_knowledge (set (lpp_saved_free k F)) ?env"
      by (rule lpp_saved_free_sound[OF free]) (use bounds in arith)
    show ?thesis using lpp_conditioned_functor_link_free_choices_sound[where node_conditions=node_conditions, OF compatible program link success_conditions[OF mgu] equations old knowledge body_free saved_free facts forked] event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
    proof
      assume success: "mode=LPCAlwaysSuccess"
      have "\<exists>sigma rho :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_ieval (fst (P!c)) rho"
      proof (cases "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode")
        case True then show ?thesis using lp_cut_coverage_success[OF True] success by blast
      next
        case False
        then have "lpc_check_free_call F a (fst (P!c)) \<or>
          lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))" using coverage by blast
        then show ?thesis
        proof
          assume "lpc_check_free_call F a (fst (P!c))"
          then show ?thesis by (rule lpc_check_free_call_sound[OF _ free])
        next
          assume mixed: "lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))"
          have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
            using known by (simp add: lp_cut_knowledge_def)
          show ?thesis by (rule lpc_check_mixed_free_call_sound[OF mixed ground free])
        qed
      qed
      then show False using failure by blast
    qed
    have link: "lpp_check_evaluation_functor_link T no_facts fuel Q nds states contexts Fs functor_contexts nd saved ?G
      (?K@[LPCHeadGuard a (fst (P!c)) False]) [] F source_context source_functors no"
      using checked possible by (simp add: lpp_check_functor_resolution_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCHeadGuard a (fst (P!c)) False]) eta"
      using known failure by (simp add: lp_cut_knowledge_def)
    show ?thesis using lpp_conditioned_functor_link_sound[where node_conditions=node_conditions, OF compatible program link failure_conditions _ refl knowledge free observed functors] failure
      by (simp add: lp_equations_def)
  qed
qed

ML \<open>
val checked = @{thms lpp_conditioned_functor_resolution_node_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted conditioned resolution action" else ();
\<close>
end
