theory LP_Prolog_Observer_Continuing_Block
 imports LP_Prolog_Observer_Continuing_Module
begin


lemma lpp_checked_univ_module_step_continuing:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and continuing: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_has_continuation (states!j)"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) xs t"
 and finite: "lpp_finite_execution xs"
 and frame: "lpp_observer_univ_frame xs"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain xs ev ys"
 shows "ev=None \<and> (ys=[] \<or> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) ys u))"
proof (rule lpp_observer_domain_module_step[where eligible=lpp_observer_univ_frame and node_conditions="lpp_separation_node_conditions separation_contexts", OF program _ _ represented finite frame step])
 show "\<And>swaps xs. lpp_observer_univ_frame xs \<Longrightarrow> lpp_observer_univ_frame (lpc_return_scope_word swaps xs)"
  by (simp add: lpp_observer_univ_frame_scopes)
next
 fix i eta ev ys
 assume bound: "i<length nds"
 and frame: "lpp_observer_univ_frame (lpc_return_eval eta (states!i))"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_return_eval eta (states!i)) ev ys"
 obtain value_var name_var args_var middle facts pair_symbol output_name output_args where
 check: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts)"
 and extra: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
  using univ_coverage[OF bound frame] by blast
 have tail: "lpp_observer_has_continuation (states!i)" by (rule continuing[OF bound frame])
 show "ev=None \<and> (ys=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) ys u))"
  apply (rule lpp_checked_continuing_separation_univ_source_step[OF compatible transfer check tail extra program _
    conditions known free observed functors finite actual])
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  done
qed

lemma lpp_checked_fresh_univ_source_block_continuing:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and continuing: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_has_continuation (states!j)"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and resolution: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and first_step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_return_eval eta (states!i)) first_event middle_state"
 and second_step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    middle_state second_event result_state"
 shows "first_event=None \<and> second_event=None \<and> (result_state=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result_state u))"
proof -
 let ?start = "[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 have first_base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) first_event middle_state"
  using first_step by (auto simp: shape lpc_return_eval_def intro: lpp_observer_clause_base)
 obtain t where silent: "first_event=None" and finite_middle: "lpp_finite_execution middle_state"
 and edge: "(?start,t)\<in>(lp_ild Q)\<^sup>+"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) middle_state t"
  using resolution[unfolded lpp_observer_node_simulation_def, rule_format,
    OF conditions known free observed functors finite first_base] by blast
 have frame: "lpp_observer_univ_frame middle_state"
  apply (rule lpp_fresh_matching_resolution_univ_frame[OF matching fresh])
  using first_step by (simp add: shape lpc_return_eval_def)
 have last: "second_event=None \<and> (result_state=[] \<or> (\<exists>u. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result_state u))"
  apply (rule lpp_checked_univ_module_step_continuing[where fuel=fuel and returned=returned and arity=arity, OF compatible transfer program _ _ _ represented finite_middle frame second_step])
  subgoal for j nu by (rule continuing[of j nu]) assumption+
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
  done
 show ?thesis using silent edge last by (meson trancl_trans)
qed



lemma lpp_checked_frontier_fresh_univ_observer_contract_continuing:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and continuing: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_has_continuation (states!j)"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and resolution: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 and template_shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c (LPPSMatching bindings)"
 and runtime_shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#runtime_goals) c m,combined_env)#combined_saved"
 and helper_shape: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) runtime=lpc_return_eval eta (states!i)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest runtime"
 and frontier_shapes: "lpp_check_observer_frontier_shapes frontier_nodes states"
 and exit_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_check_observer_univ_exit (Fs!j) (states!j)"
 and lower: "\<And>child u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpc_reinterface (\<lambda>env slot. env (Inl slot)) child) u \<Longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) child)) (lp_ild Q) u final_return"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] final_return"
proof (rule lpp_checked_fresh_univ_observer_contract[where node_conditions="lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)",
 OF head fresh known observed runtime_shape covered invariant _ lower])
 fix helper_middle helper_result
 assume first_step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_reinterface (\<lambda>env slot. env (Inl slot)) runtime) None helper_middle"
 and second_step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    helper_middle None helper_result"
 have simulated: "(None :: (nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm) option)=None \<and> (None :: (nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm) option)=None \<and> (helper_result=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) helper_result u))"
  apply (rule lpp_checked_fresh_univ_source_block_continuing[where fuel=fuel and returned=returned and arity=arity,
    OF compatible transfer program _ _ _ resolution template_shape matching fresh conditions known free observed functors finite
     first_step[unfolded helper_shape] second_step])
  subgoal for j nu by (rule continuing[of j nu]) assumption+
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
  done
 have exit_shape: "\<not>lpp_observer_internal_frame helper_result"
  apply (rule lpp_checked_fresh_univ_exit[OF program _ resolution template_shape matching fresh
   conditions known free observed functors finite first_step[unfolded helper_shape] second_step])
  subgoal for j nu by (rule exit_coverage[of j nu]) assumption+
  done
 have lift: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) helper_result u"
  if child_rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) helper_result u" for u
  by (rule lpp_observer_exit_frontier_rep[OF frontier_shapes child_rep exit_shape])
 show "helper_result=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) helper_result u)"
  using simulated lift by blast

qed



lemma lpp_observer_frontier_fresh_univ_node_contract_continuing:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and continuing: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_has_continuation (states!j)"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) source_returned source_arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and resolution: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 and source_shape: "states!i=((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and clear: "lpc_rest_scopes rest={}"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c (LPPSMatching bindings)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and frontier_shapes: "lpp_check_observer_frontier_shapes frontier_nodes states"
 and exit_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_check_observer_univ_exit (Fs!j) (states!j)"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_invariant {v. vars_term v={}} specs rest runtime \<Longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_invariant_scopes[OF clear])
next
 fix eta runtime
 show "lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts) i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant {v. vars_term v={}} specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 proof (intro impI)
  assume frontier_conditions: "lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts) i eta"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
  and free: "lpc_free_knowledge (set (Fs!i)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
  and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i)"
  and invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant {v. vars_term v={}} specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    (LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
   using represented by (simp add: source_shape lpc_return_eval_def)
  obtain combined_env combined_saved where runtime_shape: "runtime =
    (LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     combined_env)#combined_saved"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  have conditions: "lpp_separation_node_conditions separation_contexts i eta"
   using frontier_conditions by (simp add: lpp_observer_frontier_conditions_def)
  have finite_helper: "lpp_finite_execution (lpc_return_eval eta (states!i))"
   using lpp_observer_invariant_finite_helper[OF invariant] by (simp only: represented)
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
   apply (rule lpp_checked_frontier_fresh_univ_observer_contract_continuing[where fuel=fuel and returned=source_returned and arity=source_arity,
    OF compatible transfer program _ _ _ resolution source_shape matching fresh conditions known free observed functors finite_helper
      head runtime_shape represented covered invariant frontier_shapes _])
   subgoal for j nu by (rule continuing[of j nu]) assumption+
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
   subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
   subgoal for j nu by (rule exit_coverage[of j nu]) assumption+
   subgoal for child u using lower by blast
   done
 qed
qed



lemma lpp_checked_frontier_observer_fresh_univ_node_contract_continuing:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and continuing: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_has_continuation (states!j)"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) source_returned source_arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m helper_payload helper_saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and source_shape: "states!i=((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"
 and extra: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and frontier_shapes: "lpp_check_observer_frontier_shapes frontier_nodes states"
 and exit_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_check_observer_univ_exit (Fs!j) (states!j)"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 have simulation: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
  by (rule lpp_checked_separation_fresh_node_simulation[OF compatible transfer checked source_shape extra])
 have matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c (LPPSMatching match_bindings)"
  using extra by (auto simp: lpp_check_separation_fresh_def)
 show ?thesis
  apply (rule lpp_observer_frontier_fresh_univ_node_contract_continuing[where fuel=fuel and source_returned=source_returned and source_arity=source_arity,
   OF compatible transfer program _ _ _ simulation source_shape matching fresh clear head covered frontier_shapes _])
  subgoal for j nu by (rule continuing[of j nu]) assumption+
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
  subgoal for j nu by (rule exit_coverage[of j nu]) assumption+
  done
qed

ML \<open>
val thms = @{thms lpp_checked_frontier_observer_fresh_univ_node_contract_continuing};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted continuing block" else ();
\<close>
end
