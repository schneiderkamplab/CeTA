theory LP_Prolog_NO_Return_Trace_Test
 imports LP_Prolog_NO_Return_Trace
begin

definition return_machine_saved :: "((string lp_cut_symbol,string) term lp_cut_entry \<times> (string lp_cut_symbol,string) term list) list" where
 "return_machine_saved=[(LPCGoals [LPCTrue],[Var ''X''])]"
definition return_machine_is_state where
 "return_machine_is_state=(LPCGoals [LPCAtom (Fun (LPCUser ''2:is'')
   [Var ''X'',lpp_machine_term (LPPMachineInteger 1)]),LPCTrue],[Var ''X''])#return_machine_saved"

lemma return_machine_is_updates_only_active:
 "lpp_no_return_is (LPPMachineLiteral (LPPMachineInteger 1)) return_machine_is_state
   ((LPCGoals [LPCTrue],[lpp_machine_term (LPPMachineInteger 1)])#return_machine_saved)"
 by (simp add: return_machine_is_state_def)

lemma return_machine_is_rejects_stale_payload:
 "\<not> lpp_no_return_is (LPPMachineLiteral (LPPMachineInteger 1)) return_machine_is_state
   ((LPCGoals [LPCTrue],[Var ''X''])#return_machine_saved)"
 by (simp add: return_machine_is_state_def lpp_integer_term_def)

lemma return_machine_is_rejects_changed_saved_row:
 "\<not> lpp_no_return_is (LPPMachineLiteral (LPPMachineInteger 1)) return_machine_is_state
   [(LPCGoals [LPCTrue],[lpp_machine_term (LPPMachineInteger 1)]),
    (LPCGoals [LPCTrue],[lpp_machine_term (LPPMachineInteger 1)])]"
 by (simp add: return_machine_is_state_def return_machine_saved_def lpp_integer_term_def)

lemma return_machine_guard_rejects_wrong_outcome:
 "\<not> lpp_no_return_compare (LPPMachineLiteral (LPPMachineInteger 1))
   (LPPMachineLiteral (LPPMachineInteger 0)) False
   [(LPCGoals [LPCAtom (Fun (LPCUser ''2:>'')
     [lpp_machine_term (LPPMachineInteger 1),lpp_machine_term (LPPMachineInteger 0)])],[Var ''X''])] []"
 by (simp add: lpp_no_return_comparison_value_def)

lemma return_ordinary_rejects_builtin:
 "\<not> lpp_no_return_ordinary_step 10 [] []
   [(LPCGoals [LPCAtom (Fun (LPCUser ''2:is'') [Var ''X'',Var ''Y''])],[])]
   (LPCNOCase 0) []"
 by (simp add: lpp_no_return_ordinary_step_def lpp_builtin_signature_def)

lemma return_ordinary_rejects_undefined:
 "\<not> lpp_no_return_ordinary_step 10 [] []
   [(LPCGoals [LPCAtom (Fun (LPCUser ''helper'') [])],[])] (LPCNOCase 0) []"
 by (simp add: lpp_no_return_ordinary_step_def lpp_defined_def)

lemma return_ordinary_rejects_exposed_caller:
 "\<not> lpp_no_return_ordinary_step 10 [] [] [(LPCGoals [],[Var ''X''])] LPCNOAdmin []"
 by (simp add: lpp_no_return_ordinary_step_def)

lemma return_machine_ground_float_is_not_integer:
 "lpp_no_return_integer (LPPMachineFloat 0)
   ((LPCGoals [LPCAtom (Fun (LPCUser ''1:integer'') [lpp_machine_term (LPPMachineFloat 0)])],[])
     #return_machine_saved) return_machine_saved"
 by (simp add: lpp_binary64_finite_def)

lemma return_machine_is_failure_resumes_saved:
 "lpp_no_return_is (LPPMachineLiteral (LPPMachineInteger 1))
   ((LPCGoals [LPCAtom (Fun (LPCUser ''2:is'')
     [Fun (LPCUser ''wrapper'') [Var ''X''],lpp_machine_term (LPPMachineInteger 1)])],[Var ''X''])
     #return_machine_saved) return_machine_saved"
 by (simp add: lpp_integer_term_def)

lemma return_machine_unsupported_expression_rejected:
 "\<not> lpp_no_return_is
   (LPPMachineBinary ''unsupported'' (LPPMachineLiteral (LPPMachineInteger 1))
      (LPPMachineLiteral (LPPMachineInteger 0)))
   ((LPCGoals [LPCAtom (Fun (LPCUser ''2:is'') [Var ''X'',b])],[])#return_machine_saved) tt"
 by (simp add: lpp_machine_binary_name_def)

ML \<open>
val checked = [@{thm return_machine_is_updates_only_active}, @{thm return_machine_is_rejects_stale_payload},
 @{thm return_machine_is_rejects_changed_saved_row}, @{thm return_machine_guard_rejects_wrong_outcome},
 @{thm return_ordinary_rejects_builtin}, @{thm return_ordinary_rejects_undefined},
 @{thm return_ordinary_rejects_exposed_caller}, @{thm return_machine_ground_float_is_not_integer},
 @{thm return_machine_is_failure_resumes_saved}, @{thm return_machine_unsupported_expression_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted Prolog return trace controls" else ();
\<close>
end
