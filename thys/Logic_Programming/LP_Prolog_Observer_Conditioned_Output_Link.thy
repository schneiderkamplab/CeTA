theory LP_Prolog_Observer_Conditioned_Output_Link
 imports LP_Prolog_Observer_Output_Rebase LP_Prolog_Parameter_Coordinate_Link
begin

text \<open>Use the full target node conditions at a module boundary. They must
hold for the actual checked binding valuation, not an unrelated witness or a
weaker separation-only representation.\<close>

lemma lpp_conditioned_functor_module_link:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd) = map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and target_conditions: "node_conditions (lpcl_target e)
   (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
 shows "\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u) \<in> (lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_return_eval eta' ss) u"
proof -
 let ?j = "lpcl_target e"
 obtain nu where same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states ! ?j))"
 and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds ! ?j))) (lpcn_guards (nds ! ?j)) nu"
 and child_free: "lpc_free_knowledge (set (Fs ! ?j)) nu"
 and context_holds: "lpp_stable_context_holds operation SP (contexts ! ?j) nu"
 and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds ! ?j),map nu (lpcn_vars (nds ! ?j)))]) \<in> lp_ild Q"
 and child_functors: "list_all (lpp_functor_fact_holds names nu) (functor_contexts ! ?j)"
 and conditions: "node_conditions ?j nu"
  using lpp_stable_functor_link_with_parameter_facts[where J="node_conditions ?j",
    OF compatible program checked equations old known free observed functors target_conditions] by blast
 have bounds: "?j < length nds" "?j < length states" "?j < length contexts" "?j < length Fs" "?j < length functor_contexts"
  using checked by (auto simp: lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def
    lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss) = lpc_return_eval nu (states ! ?j)"
  by (simp add: same lpc_return_scope_word_inverse)
 have represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   node_conditions (lpc_return_eval eta' ss) [(lpcn_pred (nds ! ?j),map nu (lpcn_vars (nds ! ?j)))]"
  unfolding lpp_premised_functor_module_rep_def
  apply (rule exI[of _ "rev (lpcl_swaps e)"])
  unfolding lpp_premised_functor_rep_def
  apply (rule exI[of _ ?j], rule exI[of _ nu])
  using bounds inverse knowledge child_free context_holds child_functors conditions by simp
 show ?thesis using edge represented by blast
qed

lemma lpp_scalar_parameter_coordinate_transport:
 assumes coordinate: "lpp_check_parameter_coordinate before_term after_term bindings"
 and scalar_value: "lp_ieval before_term eta = LPIFun (LPCUser scalar) []"
 and ground: "vars_term initial_parameter = {}"
 shows "lp_ieval after_term (\<lambda>x. lp_ieval (bindings x) eta) = LPIFun (LPCUser scalar) [] \<and>
   lpp_runtime_parameter initial_parameter (lp_ieval after_term (\<lambda>x. lp_ieval (bindings x) eta))"
 using lpp_checked_parameter_coordinate_value[OF coordinate, of eta] scalar_value ground
 by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def)

lemma lpp_checked_conditioned_output_module_link_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q target_nodes target_states target_contexts target_free target_functors nd source_rows G K eqs F source_context source_functors e"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and target_conditions: "node_conditions (lpcl_target e)
   (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
 and representation: "lpc_reinterface (\<lambda>env x. env (Inl x)) (lpp_observer_rebase helper runtime)=lpc_return_eval eta' source_rows"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and output_coordinate: "\<And>source_entry env. (source_entry,env) \<in> set runtime \<Longrightarrow> helper source_entry env new_oi = env (Inl oi)"
 and target: "\<And>child u.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    node_conditions
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_output_invariant A specs rest new_oi hi child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 let ?child = "lpp_observer_rebase helper runtime"
 obtain u where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
   node_conditions (lpc_return_eval eta' source_rows) u"
  using lpp_conditioned_functor_module_link[where node_conditions=node_conditions, OF compatible program checked equations old known free observed functors target_conditions] by blast
 have module: "lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
   node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) ?child) u"
  using rep representation by simp
 have inv: "lpp_observer_output_invariant A specs rest new_oi hi ?child"
  by (rule lpp_observer_output_rebase_invariant[where helper=helper and new_oi=new_oi, OF invariant output_coordinate])
 have result: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) ?child))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
  by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] target[OF strict module inv]])
 show ?thesis using result by (simp add: lpp_observer_rebase_caller)
qed

ML \<open>
val checked = @{thms lpp_conditioned_functor_module_link lpp_scalar_parameter_coordinate_transport
 lpp_checked_conditioned_output_module_link_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted conditioned output link" else ();
\<close>
end
