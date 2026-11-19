theory LP_Prolog_Conditioned_Equality
 imports LP_Prolog_Separation_Equality_Action LP_Prolog_Parameter_Coordinate_Link
begin

text \<open>Successor premises are checked in the actual link valuation. This
keeps parameter identity and branch facts in the same witness as context and
separation, and makes the lower contract usable by a strengthened family.
The success and failure premises are distinct; failure uses the saved valuation.\<close>

lemma lpp_conditioned_functor_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and conditions: "node_conditions (lpcl_target e)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j="lpcl_target e"
  have enriched: "lpp_stable_context_holds operation SP (lpp_functor_shape_context source_context source_functors) eta'"
    by (rule lpp_functor_shape_context_stable[OF observed functors])
  have base: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F
    (lpp_functor_shape_context source_context source_functors) e"
    using checked by (simp add: lpp_check_evaluation_functor_link_def)
  have transported: "list_all (lpp_functor_fact_holds names
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')) (functor_contexts!?j)"
    by (rule lpp_check_functor_equation_transport_sound[where fuel=fuel, OF _ equations functors])
      (use checked in \<open>simp add: lpp_check_evaluation_functor_link_def\<close>)
  obtain nu where same: "lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!?j))"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child_free: "lpc_free_knowledge (set (Fs!?j)) nu"
    and context_holds: "lpp_stable_context_holds operation SP (contexts!?j) nu"
    and child_separation: "node_conditions ?j nu"
    and child_functors: "list_all (lpp_functor_fact_holds names nu) (functor_contexts!?j)"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_stable_link_witness_with_observation[where J="\<lambda>nu.
        list_all (lpp_functor_fact_holds names nu) (functor_contexts!?j) \<and>
        node_conditions ?j nu",
      OF compatible program base equations old known free enriched conjI[OF transported conditions]] by blast
  have bounds: "?j<length nds" "?j<length states" "?j<length contexts" "?j<length Fs" "?j<length functor_contexts"
    using checked by (auto simp: lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def
      lpc_check_return_link_def lpc_check_link_def)
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions
      (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
      [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_premised_functor_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu]) (use bounds inverse knowledge child_free context_holds child_functors child_separation in auto)
  show ?thesis using edge rep by blast
qed

lemma lpp_conditioned_functor_link_free_choices_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link_free_choices T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F H source_context source_functors e"
    and conditions: "node_conditions (lpcl_target e)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and saved_free: "lpc_free_knowledge (set H) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
 have alternatives:
   "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e \<or>
    lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e"
  using checked by (simp add: lpp_check_evaluation_functor_link_free_choices_def)
 from alternatives show ?thesis
 proof
  assume link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
  show ?thesis by (rule lpp_conditioned_functor_link_sound[where node_conditions=node_conditions, OF compatible program link conditions equations old known free observed functors])
 next
  assume link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e"
  show ?thesis by (rule lpp_conditioned_functor_link_sound[where node_conditions=node_conditions, OF compatible program link conditions equations old known saved_free observed functors])
 qed
qed

theorem lpp_conditioned_functor_equality_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs active saved k l next mode outputs source_context source_functors yes no"
    and success_conditions: "\<And>sigma. lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
      node_conditions (lpcl_target yes)
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x)
          (lp_cut_resolution_env k l eta sigma eta))"
    and failure_conditions: "node_conditions (lpcl_target no)
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions (lpc_return_scope_word swaps tt) u)"
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
    show ?thesis using lpp_conditioned_functor_link_free_choices_sound[where node_conditions=node_conditions, OF compatible program link success_conditions[OF mgu] equations old knowledge preserved saved_free initialized forked] event same by simp
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
    show ?thesis using lpp_conditioned_functor_link_sound[where node_conditions=node_conditions, OF compatible program link failure_conditions _ refl knowledge free observed functors] failure
      by (simp add: lp_equations_def)
  qed
qed

ML \<open>
val checked = @{thms lpp_conditioned_functor_link_sound
 lpp_conditioned_functor_link_free_choices_sound lpp_conditioned_functor_equality_node_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted conditioned equality" else ();
\<close>
end
