theory LP_Prolog_Observer_Control
 imports LP_Prolog_Observer_Term_Test LP_Prolog_Attached_Finite_Actions
begin

lemma lpp_observer_simple_reinterface:
 "lpp_simple_control_frame (lpc_reinterface F ss)=lpp_simple_control_frame ss"
 by (induct ss rule: lpp_simple_control_frame.induct)
  (simp_all add: lpc_reinterface_def)

lemma lpp_observer_clear_base:
 assumes clear: "\<not>lpp_builtin_active lpp_builtin_signature (map fst ss)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain ss event tt"
 shows "lpc_answer_transition P ss event tt"
proof -
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst ss)"
  by (rule lpp_no_builtin_domain_bad[OF clear])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation) ss event tt"
  using step supported by (simp add: lpp_domain_answers_def)
 show ?thesis using actual clear by (cases rule: lpp_answer_transition.cases)
  (auto simp: lpp_builtin_active_def dest: lpp_univ_source_selected)
qed

text \<open>Administrative and clause-selection rows share this lifting rule.
The source-row simulation remains an explicit premise supplied by the existing
checked action. Active-prefix coverage prevents executing a suspended caller
as if it belonged to an exhausted helper.\<close>

lemma lpp_observer_control_step:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and simple: "lpp_simple_control_frame source_rows"
 and clear: "lpp_no_builtin_frame source_rows"
 and active: "lpc_prefix_active runtime"
 and source_step: "\<And>ys. lpc_answer_transition P (lpc_return_eval eta source_rows) None ys \<Longrightarrow>
   \<exists>u swaps. (subject,u)\<in>R \<and> C (lpc_return_scope_word swaps ys) u"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) event result"
 shows "event=None \<and> (\<exists>tt u swaps.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None tt \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) tt) \<and>
   (subject,u)\<in>R \<and>
   C (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps tt)) u \<and>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof -
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 have clear_helper: "\<not>lpp_builtin_active lpp_builtin_signature (map fst (lpc_reinterface ?L runtime))"
  using lpp_no_builtin_frame_sound[OF clear, of eta] by (simp add: represented)
 have active_caller: "lpc_prefix_active (lpc_reinterface ?R runtime)"
  using active by (simp only: lpp_observer_reindex_active)
 have clear_caller: "\<not>lpp_builtin_active lpp_builtin_signature
   (map fst (lpc_attach_answers rest (lpc_reinterface ?R runtime)))"
  using clear_helper by (simp add: lpp_builtin_active_attach[OF active_caller])
 have simple_helper: "lpp_simple_control_frame (lpc_reinterface ?L runtime)"
  by (simp add: represented lpp_simple_control_frame_eval simple)
 have simple_caller: "lpp_simple_control_frame (lpc_reinterface ?R runtime)"
  using simple_helper by (simp only: lpp_observer_simple_reinterface)
 have caller_base: "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_reinterface ?R runtime)) event result"
  by (rule lpp_observer_clear_base[OF clear_caller step])
 have preserved: "lpp_leaf_stack_invariant A specs result"
  by (rule lpp_leaf_simple_base_step[OF lpp_simple_active_attachment[OF simple_caller active_caller] caller_base])
   (use invariant in \<open>simp only: lpp_leaf_stack_attachment\<close>)
 have local_context: "\<exists>u swaps. (subject,u)\<in>R \<and> C (lpc_return_scope_word swaps ys) u"
  if local_step: "?T (lpc_reinterface ?L runtime) None ys" for ys
  using source_step lpp_observer_clear_base[OF clear_helper local_step] by (simp add: represented)
 show ?thesis by (rule lpp_observer_step[OF active step local_context preserved])
qed

ML \<open>
val checked = @{thms lpp_observer_simple_reinterface lpp_observer_clear_base lpp_observer_control_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer control" else ();
\<close>
end
