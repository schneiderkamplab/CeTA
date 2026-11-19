theory LP_Prolog_Attached_Arithmetic_Finite
 imports LP_Prolog_Attached_Subterm_Arithmetic LP_Prolog_Finite_Execution_Builtin
begin

lemma lpp_actual_is_finite_step:
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) event tt"
 and finite: "lpp_finite_execution ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_domain_answer_step[OF step finite])
 fix ev us
 assume base: "lpc_answer_transition P ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) ev us"
 show "lpp_finite_execution us"
  by (rule lpp_finite_base_answer_step[OF base finite]) auto
next
 fix f ts rest rho es outcome
 assume shape: "((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved) =
   (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#rest),rho)#es"
 and success: "lpp_univ_source_builtin names operation f ts outcome"
 have arithmetic: "lpp_stable_is_outcome operation a e outcome"
  using shape success by (auto simp: lpp_univ_source_builtin_def lpp_stable_source_builtin_def)
 have finite_rest: "lpp_finite_goals rest"
  using finite shape by (simp add: lpp_finite_execution_def lpp_finite_goals_def)
 show "lpp_finite_execution_outcome rest outcome"
 proof (cases outcome)
  case (LPPBuiltinSuccess sigma)
  show ?thesis using lpp_stable_is_finite_goals[OF arithmetic[unfolded LPPBuiltinSuccess] finite_rest]
   by (simp add: LPPBuiltinSuccess)
 qed (use arithmetic in \<open>auto simp: lpp_stable_is_outcome_def split: option.splits\<close>)
qed

lemma lpp_attached_is_finite_step:
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)) event tt"
 and finite: "lpp_finite_execution (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved))"
 shows "lpp_finite_execution tt"
 by (rule lpp_actual_is_finite_step[OF step[unfolded lpc_attach_answers_def, simplified] finite[unfolded lpc_attach_answers_def, simplified]])

lemma lpp_attached_is_subterm_invariants:
 assumes ground: "vars_term initial_parameter = {}"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)) event tt"
 and finite: "lpp_finite_execution (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved))"
 and leaf: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),eta)#saved)"
 shows "lpp_finite_execution tt \<and>
   lpp_leaf_stack_invariant (lpp_parameter_subterm_templates marker tag initial_parameter) specs tt"
 using lpp_attached_is_finite_step[OF step finite]
   lpp_attached_is_subterm_stack_step[OF ground step leaf] by blast

ML \<open>
val checked = @{thms lpp_attached_is_subterm_invariants lpp_actual_is_finite_step lpp_attached_is_finite_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic finiteness" else ();
\<close>
end
