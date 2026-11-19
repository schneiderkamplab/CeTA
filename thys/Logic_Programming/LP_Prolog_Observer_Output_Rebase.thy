theory LP_Prolog_Observer_Output_Rebase
 imports LP_Prolog_Observer_Output_Copy_Node LP_Prolog_Observer_Module_Link
begin

text \<open>The equality module adds its scalar operand to the helper tuple;
it is not a projection of the old tuple. Rebase the helper observation while
retaining the caller in each frame. Output correspondence is checked separately
from the complete new helper representation.\<close>

lemma lpp_observer_output_rebase_invariant:
 assumes invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and coordinate: "\<And>source_entry env. (source_entry,env) \<in> set runtime \<Longrightarrow>
   helper source_entry env new_oi = env (Inl oi)"
 shows "lpp_observer_output_invariant A specs rest new_oi hi (lpp_observer_rebase helper runtime)"
proof -
 have old: "lpp_observer_invariant A specs rest runtime"
 and shared: "lpp_observer_output_alias oi hi runtime"
  using invariant by (simp_all add: lpp_observer_output_invariant_def)
 have new_shared: "lpp_observer_output_alias new_oi hi (lpp_observer_rebase helper runtime)"
  using shared coordinate
  by (fastforce simp: lpp_observer_output_alias_def lpp_observer_rebase_def list_all_iff)
 show ?thesis using old new_shared
  by (simp add: lpp_observer_output_invariant_def lpp_observer_rebase_invariant)
qed

lemma lpp_observer_singleton_output_rebase:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta [(source_entry,old_payload)]"
 and coordinate: "oi < length old_payload" "new_oi < length new_payload"
   "old_payload ! oi = new_payload ! new_oi"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 defines child_def: "child \<equiv> lpp_observer_rebase (\<lambda>_ _. lpc_return_env new_payload eta) runtime"
 shows "lpc_reinterface (\<lambda>env x. env (Inl x)) child = lpc_return_eval eta [(source_entry,new_payload)] \<and>
   lpp_observer_output_invariant A specs rest new_oi hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
proof -
 obtain frame env where shape: "runtime = [(frame,env)]"
 and frame: "frame = lp_cut_entry_map (\<lambda>t. lp_ieval t eta) source_entry"
 and helper_env: "(\<lambda>x. env (Inl x)) = lpc_return_env old_payload eta"
  using represented by (auto simp: lpc_reinterface_def lpc_return_eval_def map_eq_Cons_conv)
 have same: "lpc_return_env new_payload eta new_oi = env (Inl oi)"
  using fun_cong[OF helper_env, of oi] coordinate by (simp add: lpc_return_env_def)
 have child_invariant: "lpp_observer_output_invariant A specs rest new_oi hi child"
  unfolding child_def
  apply (rule lpp_observer_output_rebase_invariant[OF invariant])
  using shape same by auto
 show ?thesis using child_invariant
  by (simp add: child_def shape frame lpp_observer_rebase_singleton lpc_reinterface_def
    lpc_return_eval_def lpp_observer_rebase_caller)
qed

lemma lpp_checked_observer_output_module_link_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q target_nodes target_states target_contexts target_free target_functors nd source_rows G K eqs F source_context source_functors e"
 and member: "lpcl_target e\<in>target_frontier"
 and bound: "lpcl_target e<length target_separation"
 and transport: "lpp_check_separation_transport source_separation (target_separation!lpcl_target e)
   (lp_cut_instance_subst (lpcl_bindings e))"
 and separation: "list_all (lpp_separation_holds eta') source_separation"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and representation: "lpc_reinterface (\<lambda>env x. env (Inl x)) (lpp_observer_rebase helper runtime)=lpc_return_eval eta' source_rows"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and output_coordinate: "\<And>source_entry env. (source_entry,env) \<in> set runtime \<Longrightarrow> helper source_entry env new_oi = env (Inl oi)"
 and target: "\<And>child u.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_output_invariant A specs rest new_oi hi child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 let ?child = "lpp_observer_rebase helper runtime"
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_return_scope_word swaps (lpc_return_eval eta' source_rows)) u"
  using lpp_frontier_separation_functor_link_sound[OF compatible program checked member bound transport
    separation equations old known free observed functors] by blast
 have module: "lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) ?child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def representation)
 have inv: "lpp_observer_output_invariant A specs rest new_oi hi ?child"
  by (rule lpp_observer_output_rebase_invariant[where helper=helper and new_oi=new_oi, OF invariant output_coordinate])
 have result: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) ?child))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
  by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] target[OF strict module inv]])
 show ?thesis using result by (simp add: lpp_observer_rebase_caller)
qed

ML \<open>
val checked = @{thms lpp_observer_output_rebase_invariant lpp_observer_singleton_output_rebase
 lpp_checked_observer_output_module_link_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output rebase" else ();
\<close>
end
