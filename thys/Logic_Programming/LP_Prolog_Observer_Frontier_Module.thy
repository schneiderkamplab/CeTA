theory LP_Prolog_Observer_Frontier_Module
 imports LP_Prolog_Observer_Frontier_Dispatch LP_Prolog_Observer_Frontier_Fresh_Check
begin

definition lpp_check_frontier_observer_module where
 "lpp_check_frontier_observer_module frontier_nodes block_nodes P nds states contexts separation_contexts actions witnesses =
  (length witnesses=length nds \<and> length separation_contexts=length nds \<and>
   lpp_check_observer_frontier_shapes frontier_nodes states \<and>
   list_all (\<lambda>i. i\<notin>frontier_nodes \<or>
    (case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
      i\<in>block_nodes \<or> lpp_check_frontier_observer_local frontier_nodes P (nds!i) (contexts!i)
       separation_contexts i (states!i) action (witnesses!i))) [0..<length nds])"

theorem lpp_checked_frontier_observer_module_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts source_returned arity actions"
 and extra: "lpp_check_frontier_observer_module frontier_nodes block_nodes P nds states contexts separation_contexts actions witnesses"
 and blocks: "\<And>j action. j<length nds \<Longrightarrow> j\<in>frontier_nodes \<Longrightarrow>
   j\<in>block_nodes \<Longrightarrow> actions!j=Some action \<Longrightarrow>
   lpp_observer_node_contract names operation SP P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned j"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> j\<in>frontier_nodes \<Longrightarrow> actions!j=None \<Longrightarrow>
   lpp_observer_node_contract names operation SP P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned j"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject"
 and invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest runtime"
 and residual: "SN_on (lp_ild Q) {subject}"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) subject returned"
proof (rule lpp_observer_frontier_table_contract[OF checked _ boundary represented invariant residual])
 fix j action
 assume bound: "j<length nds" and member: "j\<in>frontier_nodes" and action: "actions!j=Some action"
 show "lpp_observer_node_contract names operation SP P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned j"
 proof (cases "j\<in>block_nodes")
  case True show ?thesis by (rule blocks[OF bound member True action])
 next
  case False
  have local: "lpp_check_frontier_observer_local frontier_nodes P (nds!j) (contexts!j)
       separation_contexts j (states!j) action (witnesses!j)"
   using extra bound member action False by (auto simp: lpp_check_frontier_observer_module_def list_all_iff)
  have source: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!j) (Fs!j) (states!j) (contexts!j) (functor_contexts!j) source_returned arity action"
   by (rule lpp_functor_control_complete(3)[OF checked bound action])
  show ?thesis by (rule lpp_checked_frontier_local_contract[OF program clear covered compatible transfer source local])
 qed
qed

end
