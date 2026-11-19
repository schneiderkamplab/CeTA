theory LP_Prolog_Attached_Subterm_Arithmetic
 imports LP_Prolog_Attached_Arithmetic_Leaf LP_Prolog_Parameter_Subterms LP_Prolog_Runtime_Parameter
begin

text \<open>Scalar arithmetic preserves caller leaf effects directly on the
shared answer machine. The actual continuation may contain arbitrary pending
goals; no source-coordinate identity or integer-only input premise is needed.
Failure, error and unsupported-domain branches remain in the transition.\<close>

lemma lpp_univ_source_is_subterm_transport:
 assumes ground_parameter: "vars_term initial_parameter = {}"
 and success: "lpp_univ_source_builtin names operation ''2:is'' [a,e] (LPPBuiltinSuccess sigma)"
 shows "lpp_leaf_environment_transport (lpp_parameter_subterm_templates marker tag initial_parameter) specs eta sigma"
proof -
 have arithmetic: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess sigma)"
  using success by (simp add: lpp_univ_source_builtin_def lpp_stable_source_builtin_def)
 have atoms: "Fun (LPCUser f) []\<in>lpp_parameter_subterm_templates marker tag initial_parameter" for f
  using lpp_parameter_subterm_templates_include[of marker tag initial_parameter]
  by (auto simp: lpp_parameter_leaf_templates_def)
 show ?thesis by (rule lpp_leaf_environment_arithmetic[OF arithmetic atoms])
  (rule lpp_parameter_subterm_templates_ground[OF ground_parameter])
qed

lemma lpp_univ_source_is_subterm_parameter:
 assumes ground: "vars_term initial_parameter = {}"
 and success: "lpp_univ_source_builtin names operation ''2:is'' [a,e] (LPPBuiltinSuccess sigma)"
 shows "lpp_leaf_environment_transport (lpp_parameter_subterm_templates marker tag initial_parameter) specs eta sigma \<and>
   lpp_runtime_parameter initial_parameter (lp_isubst a sigma)"
proof -
 have arithmetic: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess sigma)"
  using success by (simp add: lpp_univ_source_builtin_def lpp_stable_source_builtin_def)
 show ?thesis using lpp_univ_source_is_subterm_transport[OF ground success]
   lpp_runtime_parameter_scalar[OF ground arithmetic] by blast
qed

lemma lpp_actual_is_subterm_stack_step:
 assumes ground_parameter: "vars_term initial_parameter = {}"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)"
 shows "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs tt"
proof (rule lpp_leaf_stack_domain_step[OF step invariant])
 fix event tt
 assume base: "lpc_answer_transition P
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
 show "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs tt"
  by (rule lpp_leaf_stack_base_step[OF base invariant]) auto
next
 fix f ts rest rho es sigma
 assume shape: "((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)=
   (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#rest),rho)#es"
 and success: "lpp_univ_source_builtin names operation f ts (LPPBuiltinSuccess sigma)"
 show "lpp_leaf_environment_transport (lpp_parameter_subterm_templates marker tag initial_parameter) specs rho sigma"
  using shape success lpp_univ_source_is_subterm_transport[OF ground_parameter] by auto
qed

lemma lpp_attached_is_subterm_stack_step:
 assumes ground_parameter: "vars_term initial_parameter = {}"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)"
 shows "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved))"
  using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
  apply (rule lpp_actual_is_subterm_stack_step[OF ground_parameter])
   using step attached
   apply (simp add: lpc_attach_answers_def)
  using attached by (simp add: lpc_attach_answers_def)

qed

ML \<open>
val checked = @{thms lpp_univ_source_is_subterm_parameter lpp_univ_source_is_subterm_transport lpp_actual_is_subterm_stack_step
 lpp_attached_is_subterm_stack_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual arithmetic leaf transport" else ();
\<close>
end
