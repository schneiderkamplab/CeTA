theory LP_Prolog_Separation_Empty_Test
 imports LP_Prolog_Separation_Empty_Actions
begin

theorem lpp_empty_separation_term_test_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts nd F ss source_context source_functors f a gs active saved yes no"
    and empty_targets: "\<And>holds. holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a) \<Longrightarrow>
      lpcl_target (if holds then yes else no)<length separation_contexts \<and>
      separation_contexts!lpcl_target (if holds then yes else no)=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
    and step: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation) (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps tt) u)"
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
  have bound: "lpcl_target (if ?holds then yes else no)<length separation_contexts"
    and empty: "separation_contexts!lpcl_target (if ?holds then yes else no)=[]"
    using empty_targets[OF coverage] by auto
  show ?thesis using lpp_empty_separation_functor_link_sound[OF compatible program link bound empty equations refl known free observed functors] actual by auto
qed

ML \<open>
val checked = @{thms lpp_empty_separation_term_test_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted empty separation term test" else ();
\<close>
end
