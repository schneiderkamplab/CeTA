theory LP_Prolog_Observer_Frontier_Table
 imports LP_Prolog_Observer_Fresh_Univ_Check
begin

text \<open>A proof frontier_nodes chooses where caller contracts resume. The original
source table and its checks remain intact. Internal block rows do not become
unconditionally valid nodes: they are excluded from the induction relation,
and every block must establish frontier_nodes representation at its exits.\<close>

definition lpp_observer_frontier_conditions where
 "lpp_observer_frontier_conditions frontier_nodes base_conditions i eta = (i\<in>frontier_nodes \<and> base_conditions i eta)"

lemma lpp_observer_outside_frontier_contract:
 assumes "i\<notin>frontier_nodes"
 shows "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes base_conditions) J rest returned i"
 using assms by (simp add: lpp_observer_node_contract_def lpp_observer_frontier_conditions_def)

lemma lpp_observer_frontier_table_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned_symbol arity actions"
 and local: "\<And>j action. j<length nds \<Longrightarrow> j\<in>frontier_nodes \<Longrightarrow> actions!j=Some action \<Longrightarrow>
   lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes base_conditions) J rest returned j"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> j\<in>frontier_nodes \<Longrightarrow> actions!j=None \<Longrightarrow>
   lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes base_conditions) J rest returned j"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes base_conditions) (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject"
 and invariant: "J runtime"
 and residual: "SN_on (lp_ild Q) {subject}"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) subject returned"
proof (rule lpp_observer_table_contract[where node_conditions="lpp_observer_frontier_conditions frontier_nodes base_conditions" and J=J, OF checked _ _ represented invariant residual])
 fix j action assume bound: "j<length nds" and action: "actions!j=Some action"
 show "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes base_conditions) J rest returned j"
  by (cases "j\<in>frontier_nodes") (use local[OF bound _ action] lpp_observer_outside_frontier_contract in auto)
next
 fix j assume bound: "j<length nds" and action: "actions!j=None"
 show "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes base_conditions) J rest returned j"
  by (cases "j\<in>frontier_nodes") (use boundary[OF bound _ action] lpp_observer_outside_frontier_contract in auto)
qed

lemma lpp_observer_frontier_rep_forget:
 assumes "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes base_conditions) ss t"
 shows "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts base_conditions ss t"
 using assms by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def lpp_observer_frontier_conditions_def)

ML \<open>
val checked = @{thms lpp_observer_outside_frontier_contract lpp_observer_frontier_table_contract lpp_observer_frontier_rep_forget};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted observer frontier_nodes assembly" else ();
\<close>
end
