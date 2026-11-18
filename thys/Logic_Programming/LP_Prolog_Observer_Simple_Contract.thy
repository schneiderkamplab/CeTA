theory LP_Prolog_Observer_Simple_Contract
 imports LP_Prolog_Observer_Parallel_Node
begin

text \<open>Administrative and clause-selection simulations feed the same
parent contract. The finite-state obligation includes every suspended caller;
it is transported through the actual step, independently of graph simulation.\<close>

lemma lpp_observer_simple_contract:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and simple: "lpp_simple_control_frame source_rows"
 and clear: "lpp_no_builtin_frame source_rows"
 and active: "lpc_prefix_active runtime"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 and source_step: "\<And>ys. lpc_answer_transition P (lpc_return_eval eta source_rows) None ys \<Longrightarrow>
   \<exists>u swaps. (subject,u)\<in>R\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_return_scope_word swaps ys) u"
 and lower: "\<And>child u. (subject,u)\<in>R\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant A specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) R u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature
    (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof (rule lpp_observer_silent_contract[OF _ lower])
 fix event result
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R runtime)) event result"
 have leaf: "lpp_leaf_stack_invariant A specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using invariant by (simp_all add: lpp_observer_invariant_def)
 obtain child u swaps where silent: "event=None"
 and actual: "result=lpc_attach_answers rest (lpc_reinterface ?R child)"
 and strict: "(subject,u)\<in>R\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions
   (lpc_reinterface ?L (lpc_return_scope_word swaps child)) u"
 and child_leaf: "lpp_leaf_stack_invariant A specs (lpc_reinterface ?R (lpc_return_scope_word swaps child))"
  using lpp_observer_control_step[OF represented simple clear active source_step leaf step] by blast
 have active_caller: "lpc_prefix_active (lpc_reinterface ?R runtime)"
  using active by (simp only: lpp_observer_reindex_active)
 have clear_helper: "\<not>lpp_builtin_active lpp_builtin_signature (map fst (lpc_reinterface ?L runtime))"
  using lpp_no_builtin_frame_sound[OF clear, of eta] by (simp add: represented)
 have clear_caller: "\<not>lpp_builtin_active lpp_builtin_signature
   (map fst (lpc_attach_answers rest (lpc_reinterface ?R runtime)))"
  using clear_helper by (simp add: lpp_builtin_active_attach[OF active_caller])
 have simple_helper: "lpp_simple_control_frame (lpc_reinterface ?L runtime)"
  by (simp add: represented lpp_simple_control_frame_eval simple)
 have simple_caller: "lpp_simple_control_frame (lpc_reinterface ?R runtime)"
  using simple_helper by (simp only: lpp_observer_simple_reinterface)
 have base: "lpc_answer_transition P (lpc_attach_answers rest (lpc_reinterface ?R runtime)) event result"
  by (rule lpp_observer_clear_base[OF clear_caller step])
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_finite_attached_simple_step[OF simple_caller active_caller base finite])
 have child_invariant: "lpp_observer_invariant A specs rest child"
  using child_leaf child_finite actual
  by (simp add: lpp_observer_invariant_def lpp_observer_reinterface_scopes lpp_leaf_stack_scopes)
 have module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
   (lpc_reinterface ?L child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def lpp_observer_reinterface_scopes)
 show "event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface ?R child) \<and>
   (subject,u)\<in>R\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_reinterface ?L child) u \<and> lpp_observer_invariant A specs rest child)"
  using silent actual strict module child_invariant by blast
qed

ML \<open>
val checked = @{thms lpp_observer_simple_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer simple contract" else ();
\<close>
end
