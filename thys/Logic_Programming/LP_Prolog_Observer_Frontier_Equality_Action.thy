theory LP_Prolog_Observer_Frontier_Equality_Action
 imports LP_Prolog_Observer_Frontier_Link LP_Prolog_Separation_Equality_Action
begin

text \<open>Successful equality transport uses its actual MGU and refreshed
valuation. Failure retains the incoming valuation and has a separate obligation;
no successful-return fact is copied onto that alternative.\<close>

lemma lpp_frontier_separation_functor_link_free_choices_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link_free_choices T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F H source_context source_functors e"
    and target_member: "lpcl_target e\<in>frontier_nodes"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
    and separation: "list_all (lpp_separation_holds eta') source_separation"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and saved_free: "lpc_free_knowledge (set H) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
 have alternatives:
   "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e \<or>
    lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e"
  using checked by (simp add: lpp_check_evaluation_functor_link_free_choices_def)
 from alternatives show ?thesis
 proof
  assume link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
  show ?thesis by (rule lpp_frontier_separation_functor_link_sound[OF compatible program link target_member separation_bound separation_check separation equations old known free observed functors])
 next
  assume link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e"
  show ?thesis by (rule lpp_frontier_separation_functor_link_sound[OF compatible program link target_member separation_bound separation_check separation equations old known saved_free observed functors])
 qed
qed

theorem lpp_frontier_separation_functor_equality_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs active saved k l next mode outputs source_context source_functors yes no"
    and success_member: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpcl_target yes\<in>frontier_nodes"
    and failure_member: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpcl_target no\<in>frontier_nodes"
    and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpcl_target yes<length separation_contexts \<and>
      lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
        (lp_cut_instance_subst (lpcl_bindings yes))"
    and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpcl_target no<length separation_contexts \<and>
      lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
        (lp_cut_instance_subst (lpcl_bindings no))"
    and success_separation: "\<And>sigma. lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
      list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
    and failure_separation: "list_all (lpp_separation_holds eta) no_separation"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_return_scope_word swaps tt) u)"
proof -
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?a = "lp_ieval a eta"
  let ?b = "lp_ieval b eta"
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?ret = "lpc_return_env active eta"
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set ?G),b\<cdot>lp_cut_refresh k (set ?G))]"
  have base: "lpc_check_free_equality_node fuel P Q nds nd F a b gs (map fst saved) k l next mode yes no"
    using checked by (simp add: lpp_check_functor_equality_node_def)
  have coverage: "lpc_check_free_equality fuel F a b mode"
    using base by (simp add: lpc_check_free_equality_node_def)
  have st: "lpc_answer_transition P ((LPCGoals (LPCUnify ?a ?b#?gs),?ret)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have cases: "(\<exists>sigma. lpc_mgu_unify ?a ?b ?gs sigma \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved) \<or>
    (event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_isubst ?b sigma))"
    using st by (cases rule: lpc_answer_transition.cases) auto
  from cases show ?thesis
  proof
    assume "\<exists>sigma. lpc_mgu_unify ?a ?b ?gs sigma \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved"
    then obtain sigma where mgu: "lpc_mgu_unify ?a ?b ?gs sigma"
      and event: "event=None" and result: "tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved" by blast
    have eq: "lp_isubst ?a sigma = lp_isubst ?b sigma"
      using mgu by (simp add: lpc_mgu_unify_def)
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lpc_free_equality_failure coverage eq by blast
    have unify: "lp_cut_check_unify fuel k l ?G ?K a b gs (map fst saved) next"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_check_free_equality_node_def)
    have payload: "lpc_check_return_values fuel k ?G ?eqs active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpp_check_evaluation_functor_link_free_choices T yes_facts fuel Q nds states contexts Fs functor_contexts nd ((LPCGoals next,outputs)#saved) ?G
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?eqs (lpp_context_unify_free source_context F ?G a b gs k) (lpp_saved_free k F) (lpp_context_with_equations (lpp_evaluation_fork_context source_context k (set ?G)) ?eqs) (lpp_functor_fork_context source_functors k (set ?G)) yes"
      using checked possible by (auto simp: lpp_check_functor_equality_node_def)
    let ?env = "lp_cut_resolution_env k l eta sigma eta"
    have same: "tt=lpc_return_eval ?env ((LPCGoals next,outputs)#saved)"
      using result lpc_return_unification_success[OF unify known eq payload short]
      by (simp add: map_map o_def lp_cut_map_comp)
    have equations: "lp_equations ?eqs ?env" by (rule lp_cut_checked_unify_equations[OF unify known eq])
    have kl: "k\<le>l" using unify by (auto simp: lp_cut_check_unify_def)
    have old: "map ?env (lpcn_vars nd)=map eta (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl parent])
    have prior: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b True]) ?env"
      by (rule lp_cut_checked_unify_success(2)[OF unify known eq])
    have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule lpc_negative_guards_sound[OF _ _ known])
        (use unify in \<open>auto simp: lp_cut_check_unify_def\<close>)
    have knowledge: "lp_cut_knowledge (set ?G)
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?env"
      using prior negative by (simp add: lp_cut_knowledge_def)
    have context_short: "lpp_context_short k source_context"
      using checked possible by (simp add: lpp_check_functor_equality_node_def)
    have bounds: "2 * k \<le> l" using unify by (auto simp: lp_cut_check_unify_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
      using known by (simp add: lp_cut_knowledge_def)
    have functor_short: "lpp_functor_context_short k source_functors"
      using checked possible by (simp add: lpp_check_functor_equality_node_def)
    have forked: "list_all (lpp_functor_fact_holds names ?env)
      (lpp_functor_fork_context source_functors k (set ?G))"
      by (rule lpp_functor_context_fork_sound[OF functors functor_short bounds ground])
    have facts: "lpp_stable_context_holds operation SP
      (lpp_evaluation_fork_context source_context k (set ?G)) ?env"
      by (rule lpp_stable_context_fork_sound[OF observed context_short bounds ground])
    have initialized: "lpp_stable_context_holds operation SP
      (lpp_context_with_equations (lpp_evaluation_fork_context source_context k (set ?G)) ?eqs) ?env"
      by (rule lpp_stable_functor_equations[OF facts equations])
    have preserved: "lpc_free_knowledge (set (lpp_context_unify_free source_context F ?G a b gs k)) ?env"
      by (rule lpp_context_unify_free_sound[where E="lpp_stable_scalar_evaluation operation" and SP=SP,
        OF mgu ground free bounds]) (use observed in \<open>simp add: lpp_stable_context_holds_def\<close>)
    have saved_free: "lpc_free_knowledge (set (lpp_saved_free k F)) ?env"
      by (rule lpp_saved_free_sound[OF free]) (use bounds in arith)
    have sep_bound: "lpcl_target yes<length separation_contexts"
      and sep_check: "lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
        (lp_cut_instance_subst (lpcl_bindings yes))"
      using success_transport[OF possible] by auto
    show ?thesis using lpp_frontier_separation_functor_link_free_choices_sound[OF compatible program link success_member[OF possible] sep_bound sep_check success_separation[OF mgu] equations old knowledge preserved saved_free initialized forked] event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_isubst ?b sigma)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      using lpc_free_equality_success coverage free failure by blast
    have link: "lpp_check_evaluation_functor_link T no_facts fuel Q nds states contexts Fs functor_contexts nd saved ?G (?K@[LPCEqGuard a b False]) [] F source_context source_functors no"
      using checked possible by (simp add: lpp_check_functor_equality_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b False]) eta"
      using known failure by (simp add: lp_cut_knowledge_def)
    have sep_bound: "lpcl_target no<length separation_contexts"
      and sep_check: "lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
        (lp_cut_instance_subst (lpcl_bindings no))"
      using failure_transport[OF possible] by auto
    show ?thesis using lpp_frontier_separation_functor_link_sound[OF compatible program link failure_member[OF possible] sep_bound sep_check failure_separation _ refl knowledge free observed functors] failure
      by (simp add: lp_equations_def)
  qed
qed

ML \<open>
val checked = @{thms lpp_frontier_separation_functor_link_free_choices_sound lpp_frontier_separation_functor_equality_node_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation equality action" else ();
\<close>
end
