theory LP_Prolog_Observer_Step
 imports LP_Prolog_Observer_Ground_Equality
begin

text \<open>One composition rule joins an existing local source simulation with
caller preservation. Both results refer to the same successor of the shared
answer machine. This does not discharge either local premise or prove a cycle
terminating.\<close>

lemma lpp_observer_step:
 assumes active: "lpc_prefix_active runtime"
 and step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) event result"
 and source_step: "\<And>ys. lpp_domain_answers P B U D
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) None ys \<Longrightarrow>
   \<exists>u swaps. (subject,u)\<in>R \<and> C (lpc_return_scope_word swaps ys) u"
 and preserved: "lpp_leaf_stack_invariant A specs result"
 shows "event=None \<and> (\<exists>tt u swaps.
   lpp_domain_answers P B U D runtime None tt \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) tt) \<and>
   (subject,u)\<in>R \<and>
   C (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps tt)) u \<and>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof -
 obtain tt where silent: "event=None" and joint: "lpp_domain_answers P B U D runtime None tt"
 and helper: "lpp_domain_answers P B U D
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) None
   (lpc_reinterface (\<lambda>env x. env (Inl x)) tt)"
 and actual: "result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) tt)"
  using lpp_attached_observer_product_step[OF active step] by blast
 obtain u swaps where related: "(subject,u)\<in>R"
 and represented: "C (lpc_return_scope_word swaps (lpc_reinterface (\<lambda>env x. env (Inl x)) tt)) u"
  using source_step[OF helper] by blast
 show ?thesis by (intro conjI silent exI[of _ tt] exI[of _ u] exI[of _ swaps])
  (use joint actual related represented preserved in
   \<open>simp_all add: lpp_observer_reinterface_scopes lpp_leaf_stack_scopes lpp_leaf_stack_attachment\<close>)
qed

lemma lpp_observer_frame_shape:
 assumes "lpc_reinterface F ss=(frame_entry,env)#saved"
 obtains raw_env raw_saved where "ss=(frame_entry,raw_env)#raw_saved"
  "F raw_env=env" "lpc_reinterface F raw_saved=saved"
 using assms by (cases ss) (auto simp: lpc_reinterface_def split: prod.splits)

ML \<open>
val checked = @{thms lpp_observer_step lpp_observer_frame_shape};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer step composition" else ();
\<close>
end
