theory LP_Prolog_Observer_Fresh_Univ_Source_Block
 imports LP_Prolog_Observer_Univ_Module
begin

lemma lpp_checked_fresh_univ_source_block:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
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
  apply (rule lpp_checked_univ_module_step[where fuel=fuel and returned=returned and arity=arity, OF compatible transfer program _ _ represented finite_middle frame second_step])
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
  done
 show ?thesis using silent edge last by (meson trancl_trans)
qed

ML \<open>
val checked = @{thms lpp_checked_fresh_univ_source_block lpp_checked_univ_module_step
 lpp_fresh_matching_resolution_univ_frame lpp_observer_univ_frame_scope lpp_observer_univ_frame_scopes};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted fresh-univ source block" else ();
\<close>
end
