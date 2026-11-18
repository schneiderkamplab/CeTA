theory LP_Prolog_Observer_Boundary_Contracts
 imports LP_Prolog_Attached_Univ_Equality_Steps
begin

text \<open>Boundary assembly uses the existing domain-aware answer contracts.
Every saved alternative keeps its own caller environment. In particular,
parallel assembly requires a full contract for every frame, including its
attached continuation; helper termination by itself is not sufficient.\<close>

lemma lpp_observer_attached_parallel_contract:
 assumes children: "\<And>frame. frame\<in>set runtime \<Longrightarrow>
  lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe [frame])) R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe runtime)) R subject returned"
proof (rule lpp_domain_contract_singletons)
 fix result_frame
 assume member: "result_frame\<in>set (lpc_attach_answers rest (lpc_reinterface observe runtime))"
 obtain frame where source_member: "frame\<in>set runtime"
 and exact: "[result_frame]=lpc_attach_answers rest (lpc_reinterface observe [frame])"
  using member by (auto simp: lpc_reinterface_def lpc_attach_answers_def)
 show "lp_answer_contract (lpp_domain_answers P B U D) [result_frame] R subject returned"
  unfolding exact by (rule children[OF source_member])
qed

lemma lpp_observer_attached_trim_contract:
 assumes child: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe active_rows)) R subject returned"
 and barriers: "lp_cut_barriers (map fst barrier_rows)"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe (active_rows@barrier_rows))) R subject returned"
proof -
 have each: "lp_cut_is_barrier frame_entry \<Longrightarrow>
   lp_cut_is_barrier (lpc_attach_frame rest (frame_entry,observe env))" for frame_entry env
  by (cases frame_entry) auto
 have suffix: "lp_cut_barriers (map fst (lpc_attach_answers rest (lpc_reinterface observe barrier_rows)))"
  using barriers by (fastforce simp: lpc_reinterface_def lpc_attach_answers_def list_all_iff intro: each)
 have full: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe active_rows) @
    lpc_attach_answers rest (lpc_reinterface observe barrier_rows)) R subject returned"
  by (rule lpp_domain_contract_append_barriers[OF child suffix])
 show ?thesis using full by (simp add: lpc_reinterface_def)
qed

lemma lpp_observer_substack_leaf:
 assumes contained: "set selected_rows \<subseteq> set runtime"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_reinterface observe runtime)"
 shows "lpp_leaf_stack_invariant A specs (lpc_reinterface observe selected_rows)"
 using contained invariant by (fastforce simp: lpp_leaf_stack_invariant_def lpc_reinterface_def list_all_iff)

lemma lpp_observer_projected_split:
 assumes represented: "lpc_reinterface observe runtime=left@right"
 shows "lpc_reinterface observe (take (length left) runtime)=left"
 and "lpc_reinterface observe (drop (length left) runtime)=right"
 using arg_cong[OF represented, of "take (length left)"]
   arg_cong[OF represented, of "drop (length left)"]
 by (simp_all add: lpc_reinterface_def take_map drop_map)

lemma lpp_checked_observer_link_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd source_rows G K eqs F source_context source_functors e"
 and separation_bound: "lpcl_target e<length separation_contexts"
 and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
 and separation: "list_all (lpp_separation_holds eta') source_separation"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta' source_rows"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and lower: "\<And>u swaps.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)) u \<Longrightarrow>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime)) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and child: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)) u"
 and leaf: "lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime))"
  using lpp_checked_observer_context_link[OF compatible program checked separation_bound separation_check
    separation equations old known free observed functors represented invariant] by blast
 show ?thesis by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict child leaf]])
qed

ML \<open>
val checked = @{thms lpp_observer_attached_parallel_contract lpp_observer_attached_trim_contract
 lpp_observer_substack_leaf lpp_observer_projected_split lpp_checked_observer_link_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer boundary contracts" else ();
\<close>
end
