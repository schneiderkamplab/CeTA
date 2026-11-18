theory LP_Prolog_Observer_Checked_Boundaries
 imports LP_Prolog_Observer_Boundary_Contracts
begin

lemma lpp_checked_observer_trim_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors returned_symbol arity (LPPFTrim successor barriers e fs)"
 and separation_bound: "lpcl_target e<length separation_contexts"
 and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
 and separation: "list_all (lpp_separation_holds eta) source_separation"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and lower: "\<And>u swaps.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps (take (length successor) runtime))) u \<Longrightarrow>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps (take (length successor) runtime))) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) (take (length successor) runtime))) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?active = "take (length successor) runtime"
 let ?saved = "drop (length successor) runtime"
 have source_shape: "source_rows=successor@barriers"
 and barrier_check: "lp_cut_barriers (map fst barriers)"
 and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd successor
   (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors e"
  using checked by (auto simp: lpp_check_functor_source_action_def)
 have represented_split: "lpc_reinterface ?L runtime=lpc_return_eval eta successor@lpc_return_eval eta barriers"
  using represented by (simp add: source_shape lpc_return_eval_def)
 have projections: "lpc_reinterface ?L ?active=lpc_return_eval eta successor"
   "lpc_reinterface ?L ?saved=lpc_return_eval eta barriers"
  using lpp_observer_projected_split[OF represented_split]
  by (simp_all add: lpc_return_eval_def)
 have leaf: "lpp_leaf_stack_invariant A specs (lpc_reinterface ?R ?active)"
  by (rule lpp_observer_substack_leaf[OF _ invariant]) (rule set_take_subset)
 have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
 have child: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface ?R ?active))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
  by (rule lpp_checked_observer_link_contract[OF compatible program link separation_bound separation_check
    separation equations refl known free observed functors projections(1) leaf lower])
 have erased: "map fst ?saved=map fst (lpc_return_eval eta barriers)"
  using arg_cong[OF projections(2), of "map fst"]
  by (simp add: lpc_reinterface_def map_map o_def split_def)
 have runtime_barriers: "lp_cut_barriers (map fst ?saved)"
  using barrier_check by (simp add: erased lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
 show ?thesis using lpp_observer_attached_trim_contract[OF child runtime_barriers] by simp
qed

lemma lpp_checked_observer_parallel_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors returned_symbol arity (LPPFParallel links factss)"
 and separation_bound: "\<And>j. j<length source_rows \<Longrightarrow> lpcl_target (links!j)<length separation_contexts"
 and separation_check: "\<And>j. j<length source_rows \<Longrightarrow> lpp_check_separation_transport source_separation (separation_contexts!lpcl_target (links!j))
      (lp_cut_instance_subst (lpcl_bindings (links!j)))"
 and separation: "list_all (lpp_separation_holds eta) source_separation"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and lower: "\<And>j u swaps. j<length source_rows \<Longrightarrow>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps [runtime!j])) u \<Longrightarrow>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps [runtime!j])) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) [runtime!j])) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof (rule lpp_observer_attached_parallel_contract)
 fix frame assume member: "frame\<in>set runtime"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 obtain j where runtime_bound: "j<length runtime" and frame: "frame=runtime!j"
  using member by (auto simp: in_set_conv_nth)
 have lengths: "length runtime=length source_rows"
  using arg_cong[OF represented, of length] by (simp add: lpc_reinterface_def lpc_return_eval_def)
 have source_bound: "j<length source_rows" using runtime_bound lengths by simp
 have link: "lpp_check_evaluation_functor_link T (factss!j) fuel Q nds states contexts Fs functor_contexts nd
   [source_rows!j] (lpcn_ground nd) (lpcn_guards nd) [] F source_context source_functors (links!j)"
  using checked source_bound by (auto simp: lpp_check_functor_source_action_def list_all_iff)
 have projection: "lpc_reinterface ?L [runtime!j]=lpc_return_eval eta [source_rows!j]"
  using arg_cong[OF represented, of "\<lambda>xs. xs!j"] runtime_bound source_bound
  by (simp add: lpc_reinterface_def lpc_return_eval_def)
 have leaf: "lpp_leaf_stack_invariant A specs (lpc_reinterface ?R [runtime!j])"
  by (rule lpp_observer_substack_leaf[OF _ invariant]) (use member frame in auto)
 have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
 have child: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface ?R [runtime!j]))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
  by (rule lpp_checked_observer_link_contract[OF compatible program link separation_bound[OF source_bound]
    separation_check[OF source_bound] separation equations refl known free observed functors projection leaf lower[OF source_bound]])
 show "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface ?R [frame]))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
  using child by (simp only: frame)
qed

ML \<open>
val checked = @{thms lpp_checked_observer_trim_contract lpp_checked_observer_parallel_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked observer boundaries" else ();
\<close>
end
