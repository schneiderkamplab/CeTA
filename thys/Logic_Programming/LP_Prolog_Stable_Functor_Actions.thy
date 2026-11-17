theory LP_Prolog_Stable_Functor_Actions
 imports LP_Prolog_Stable_Functor_Representation LP_Prolog_Stable_Refresh
   LP_Prolog_Functor_Cut_Actions LP_Prolog_Functor_Term_Test
begin

text \<open>The same Boolean action checks preserve the full stable comparison
context as well as functor facts. No graph or certificate state is reconstructed
with an empty or weaker incoming context.\<close>

lemma lpp_stable_functor_equations:
 "lpp_stable_context_holds operation SP ctx eta \<Longrightarrow> lp_equations eqs eta \<Longrightarrow>
  lpp_stable_context_holds operation SP (lpp_context_with_equations ctx eqs) eta"
 by (cases ctx)
  (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def lp_equations_def list_all_iff)

theorem lpp_stable_functor_equality_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs active saved k l next mode outputs source_context source_functors yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
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
    show ?thesis using lpp_stable_functor_link_free_choices_sound[OF compatible program link equations old knowledge preserved saved_free initialized forked] event same by simp
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
    show ?thesis using lpp_stable_functor_link_sound[OF compatible program link _ refl knowledge free observed functors] failure
      by (simp add: lp_equations_def)
  qed
qed

theorem lpp_stable_functor_resolution_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m active saved k l A next anchors bindings mode outputs source_context source_functors yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
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
    show ?thesis using lpp_stable_functor_link_free_choices_sound[OF compatible program link equations old knowledge body_free saved_free facts forked] event same by simp
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
    show ?thesis using lpp_stable_functor_link_sound[OF compatible program link _ refl knowledge free observed functors] failure
      by (simp add: lp_equations_def)
  qed
qed

theorem lpp_stable_functor_admin_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts nd F ss source_context source_functors returned arity event next e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) actual tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. actual=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof -
  have admin: "lpc_return_admin ss=Some (event,next)"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd next (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    and emit: "case event of None\<Rightarrow>True | Some ts\<Rightarrow>lpc_check_return_emit Q nd returned arity ts"
    using checked by (auto simp: lpp_check_functor_admin_node_def)
  have evaluated: "lpc_return_admin (lpc_return_eval eta ss) =
    Some (map_option (\<lambda>ts. lpc_return_env ts eta) event,lpc_return_eval eta next)"
    by (simp add: lpc_return_eval_admin admin)
  have same: "actual=map_option (\<lambda>ts. lpc_return_env ts eta) event \<and> tt=lpc_return_eval eta next"
    by (rule lpc_return_admin_unique[OF evaluated step])
  have successor: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u"
    using lpp_stable_functor_link_sound[OF compatible program link _ refl known free observed functors] same
    by (simp add: lp_equations_def)
  have returns: "\<forall>rho. actual=Some rho \<longrightarrow>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  proof (intro allI impI)
    fix rho assume actual: "actual=Some rho"
    obtain ts where event: "event=Some ts" and rho: "rho=lpc_return_env ts eta"
      using same actual by (cases event) auto
    have check: "lpc_check_return_emit Q nd returned arity ts" using emit event by simp
    show "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
      using lpc_return_emit_sound[OF check, of eta] rho by auto
  qed
  show ?thesis using successor returns by blast
qed

theorem lpp_stable_functor_case_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts nd F source_context source_functors m f ts gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_case P m f ts gs (map fst saved)
    (map fst (lpc_return_case P m f ts gs active saved))"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd (lpc_return_case P m f ts gs active saved)
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    using checked by (auto simp: lpp_check_functor_case_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))"
    using lpc_return_case_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps (lpc_return_eval eta (lpc_return_case P m f ts gs active saved))) u"
    using lpp_stable_functor_link_sound[OF compatible program link _ refl known free observed functors] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

theorem lpp_stable_functor_meta_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_meta_node T fs fuel Q nds states contexts Fs functor_contexts nd F source_context source_functors m a gs active saved body e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have check: "lp_cut_check_meta m a gs (map fst saved) body"
    and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd
      ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved) (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
    using checked by (auto simp: lpp_check_functor_meta_node_def)
  obtain n where event: "event=None" and same: "tt=lpc_return_scope_word [(m,n)]
    (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))"
    using lpc_return_meta_covers[OF check step] by auto
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps
      (lpc_return_eval eta ((LPCGoals (body@gs),active)#(LPCBarrier m,active)#saved))) u"
    using lpp_stable_functor_link_sound[OF compatible program link _ refl known free observed functors] by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed


theorem lpp_stable_functor_cut_action_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F ss source_context source_functors returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case LPCRTerminal
  then have "ss=[]" using checked by simp
  then show ?thesis using step by (auto simp: lpc_return_eval_def elim: lpc_answer_transition.cases)
next
  case LPCRInconsistent
  have "lp_cut_check_inconsistent (lpcn_guards nd)" using checked LPCRInconsistent by simp
  then show ?thesis using lp_cut_checked_inconsistent[OF _ known] by blast
next
  case (LPCRAdmin emitted successor e)
  then show ?thesis using lpp_stable_functor_admin_node_sound[OF compatible program _ known free observed functors step] checked by simp
next
  case (LPCRCase m f ts gs active saved e)
  have check: "lpp_check_functor_case_node T yes_facts fuel P Q nds states contexts Fs functor_contexts nd F source_context source_functors m f ts gs active saved e"
    and ss: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
    using checked LPCRCase by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_stable_functor_case_node_sound[OF compatible program check known free observed functors source] by auto
next
  case (LPCRMeta m a gs active saved body e)
  have check: "lpp_check_functor_meta_node T yes_facts fuel Q nds states contexts Fs functor_contexts nd F source_context source_functors m a gs active saved body e"
    and ss: "ss=(LPCGoals (LPCMeta a#gs),active)#saved"
    using checked LPCRMeta by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_stable_functor_meta_node_sound[OF compatible program check known free observed functors source] by auto
next
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  have check: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs active saved k l successor mode outputs source_context source_functors yes no"
    and ss: "ss=(LPCGoals (LPCUnify a b#gs),active)#saved"
    using checked LPCREquality by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_stable_functor_equality_node_sound[OF compatible program check known free observed functors source] by auto
next
  case (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)
  have check: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m active saved k l A successor anchors bindings mode outputs source_context source_functors yes no"
    and ss: "ss=(LPCClause (LPCAtom a#gs) c m,active)#saved"
    using checked LPCRResolution by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_stable_functor_resolution_node_sound[OF compatible program check known free observed functors source] by auto
qed



theorem lpp_stable_functor_term_test_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts nd F ss source_context source_functors f a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps tt) u)"
proof -
  let ?holds = "lpp_var_holds f (lp_ieval a eta)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  have name: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked by (auto simp: lpp_check_functor_term_test_def)
  have coverage: "?holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a)"
    by (rule lpp_var_outcomes_cover[OF name known])
  have link: "lpp_check_evaluation_functor_link T (if ?holds then yes_facts else no_facts)
    fuel Q nds states contexts Fs functor_contexts nd ?next (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors
    (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_functor_term_test_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_univ_term_test_step[OF name] split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpp_stable_functor_link_sound[OF compatible program link equations refl known free observed functors] actual by auto
qed

ML \<open>
val checked = [@{thm lpp_stable_functor_cut_action_sound}, @{thm lpp_stable_functor_term_test_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted stable functor action dependency" else ();
\<close>
end
