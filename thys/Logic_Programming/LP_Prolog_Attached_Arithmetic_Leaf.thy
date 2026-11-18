theory LP_Prolog_Attached_Arithmetic_Leaf
 imports LP_Prolog_Checked_Head_Return_Effect
begin

text \<open>Scalar arithmetic preserves caller leaf effects directly on the
shared answer machine. The actual continuation may contain arbitrary pending
goals; no source-coordinate identity or integer-only input premise is needed.
Failure, error and unsupported-domain branches remain in the transition.\<close>

lemma lpp_univ_source_is_leaf_transport:
 assumes success: "lpp_univ_source_builtin names operation ''2:is'' [a,e] (LPPBuiltinSuccess sigma)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs eta sigma"
proof -
 have arithmetic: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess sigma)"
  using success by (simp add: lpp_univ_source_builtin_def lpp_stable_source_builtin_def)
 show ?thesis by (rule lpp_leaf_environment_arithmetic[OF arithmetic]) auto
qed

lemma lpp_actual_is_leaf_stack_step:
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_leaf_stack_domain_step[OF step invariant])
 fix event tt
 assume base: "lpc_answer_transition P
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
 show "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
  by (rule lpp_leaf_stack_base_step[OF base invariant]) auto
next
 fix f ts rest rho es sigma
 assume shape: "((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)=
   (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#rest),rho)#es"
 and success: "lpp_univ_source_builtin names operation f ts (LPPBuiltinSuccess sigma)"
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs rho sigma"
  using shape success lpp_univ_source_is_leaf_transport by auto
qed

lemma lpp_actual_term_test_leaf_stack_step:
 assumes name: "lpp_var_name f"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a])#gs),eta)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant A specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a])#gs),eta)#saved)"
 shows "lpp_leaf_stack_invariant A specs tt"
 using step invariant
 by (auto simp: lpp_domain_answers_def lpp_univ_term_test_step[OF name]
   lpp_leaf_stack_invariant_def split: if_splits)

lemma lpp_attached_is_leaf_stack_step:
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved))"
  using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
  apply (rule lpp_actual_is_leaf_stack_step)
   using step attached
   apply (simp add: lpc_attach_answers_def)
  using attached by (simp add: lpc_attach_answers_def)

qed

ML \<open>
val checked = @{thms lpp_univ_source_is_leaf_transport lpp_actual_is_leaf_stack_step
 lpp_actual_term_test_leaf_stack_step lpp_attached_is_leaf_stack_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual arithmetic leaf transport" else ();
\<close>
end
