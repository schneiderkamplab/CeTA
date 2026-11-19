theory LP_Prolog_Observer_Conditioned_Matching
 imports LP_Prolog_Conditioned_Resolution LP_Prolog_Restricted_Matching_Leaf
  LP_Prolog_Observer_Resolution_Contract
begin

lemma lpp_checked_observer_conditioned_matching:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m helper_payload helper_saved k l A next anchors bindings mode outputs source_context source_functors yes no"
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
 and matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and ground_templates: "\<And>v. v\<in>allowed_templates \<Longrightarrow> vars_term v={}"
 and shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
   map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>x. combined_env (Inr x)))) rest)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_leaf_stack_invariant allowed_templates specs
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) event result"
 shows "event=None \<and> (\<exists>tt u swaps.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None tt \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) tt) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps tt)) u \<and>
   lpp_leaf_stack_invariant allowed_templates specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 have active_prefix: "lpc_prefix_active runtime" by (simp add: shape)
 obtain tt where silent: "event=None" and joint: "?T runtime None tt"
 and helper_step: "?T (lpc_reinterface ?L runtime) None (lpc_reinterface ?L tt)"
 and returned: "result=lpc_attach_answers rest (lpc_reinterface ?R tt)"
  using lpp_attached_observer_product_step[OF active_prefix step] by blast
 have helper_base: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved))
   None (lpc_reinterface ?L tt)"
  using helper_step[unfolded represented]
  by (auto simp: lpc_return_eval_def intro: lpp_observer_clause_base)
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and next_context: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions
   (lpc_return_scope_word swaps (lpc_reinterface ?L tt)) u"
  using lpp_conditioned_functor_resolution_node_sound[where node_conditions=node_conditions, OF compatible program checked
   success_conditions failure_conditions known free observed functors helper_base] by blast
 have caller_base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     ?R combined_env)#lpc_reinterface ?R combined_saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_clause_base)
 have matched: "lp_ieval (fst (P!c)) (\<lambda>x. lp_ieval (lp_cut_match_subst match_bindings x) eta)=lp_ieval a eta"
  using matching unfolding lp_cut_check_match_def by (simp add: lp_ieval_finite_subst[symmetric])
 have live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
 have caller_invariant: "lpp_leaf_stack_invariant allowed_templates specs result"
  by (rule lpp_attached_restricted_matching_leaf_base_step[OF caller_base _ ground_templates matched finite_call finite_rest live])
   (use invariant in \<open>simp add: shape lpc_reinterface_def\<close>)
 show ?thesis by (intro conjI silent exI[of _ tt] exI[of _ u] exI[of _ swaps])
  (use joint returned strict next_context caller_invariant in
   \<open>simp_all add: lpp_observer_reinterface_scopes lpp_leaf_stack_scopes lpp_leaf_stack_attachment\<close>)
qed

lemma lpp_checked_observer_conditioned_matching_contract:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m helper_payload helper_saved k l A next anchors bindings mode outputs source_context source_functors yes no"
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
 and matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and ground_templates: "\<And>v. v\<in>allowed_templates \<Longrightarrow> vars_term v={}"
 and shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"

 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant allowed_templates specs rest runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant allowed_templates specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof (rule lpp_observer_silent_contract[OF _ lower])
 fix event result
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R runtime)) event result"
 have leaf: "lpp_leaf_stack_invariant allowed_templates specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using invariant by (simp_all add: lpp_observer_invariant_def)
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
   map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)"
  using finite by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 obtain child u swaps where silent: "event=None"
 and actual: "result=lpc_attach_answers rest (lpc_reinterface ?R child)"
 and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions (lpc_reinterface ?L (lpc_return_scope_word swaps child)) u"
 and child_leaf: "lpp_leaf_stack_invariant allowed_templates specs (lpc_reinterface ?R (lpc_return_scope_word swaps child))"
  using lpp_checked_observer_conditioned_matching[where node_conditions=node_conditions, OF compatible program checked success_conditions
    failure_conditions known free observed functors matching ground_templates shape represented
    finite_call finite_rest covered leaf step] by blast
 have base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
    ?R combined_env)#lpc_reinterface ?R combined_saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_clause_base)
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_finite_attached_matching_step[OF base _ matching])
   (use finite in \<open>simp add: shape lpc_reinterface_def\<close>)
 have child_invariant: "lpp_observer_invariant allowed_templates specs rest child"
  using child_leaf child_finite actual
  by (simp add: lpp_observer_invariant_def lpp_observer_reinterface_scopes lpp_leaf_stack_scopes)
 have module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions (lpc_reinterface ?L child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def lpp_observer_reinterface_scopes)
 show "event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface ?R child) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface ?L child) u \<and>
   lpp_observer_invariant allowed_templates specs rest child)"
  using silent actual strict module child_invariant by blast
qed

ML \<open>
val checked = @{thms lpp_checked_observer_conditioned_matching lpp_checked_observer_conditioned_matching_contract
 lpp_attached_restricted_matching_leaf_base_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted conditioned matching contract" else ();
\<close>
end
