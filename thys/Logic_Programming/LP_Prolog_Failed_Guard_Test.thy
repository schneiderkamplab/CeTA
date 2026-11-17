theory LP_Prolog_Failed_Guard_Test
 imports LP_Prolog_Head_Failure_Check
begin

definition failed_choice_guard where
 "failed_choice_guard n = LPPScalarIsLiteral (LPPMachineInteger n) (LPPScalarParameter ''x'')"
definition failed_choice_tree where
 "failed_choice_tree = LPPFailedChoice (LPPFailedGuard (failed_choice_guard 0))
   (LPPFailedGuard (failed_choice_guard 1))"
definition failed_choice_program where
 "failed_choice_program = [(Fun (LPCUser ''2:q'') [Var ''x'',Var ''y''],
   lpp_failed_tree_goals failed_choice_tree @ [LPCTrue])]"

lemma failed_choice_controls:
 "lpp_check_head_failure failed_choice_program ''2:q'' [Some (LPPMachineInteger 2),None] 0
    (LPPTreeFailure ([''x'',''y''],failed_choice_tree)) \<and>
  \<not>lpp_check_head_failure failed_choice_program ''2:q'' [Some (LPPMachineInteger 0),None] 0
    (LPPTreeFailure ([''x'',''y''],failed_choice_tree)) \<and>
  \<not>lpp_check_head_failure failed_choice_program ''2:q'' [Some (LPPMachineInteger 1),None] 0
    (LPPTreeFailure ([''x'',''y''],failed_choice_tree)) \<and>
  \<not>lpp_check_head_failure failed_choice_program ''2:q'' [None,None] 0
    (LPPTreeFailure ([''x'',''y''],failed_choice_tree)) \<and>
  \<not>lpp_check_head_failure failed_choice_program ''2:q'' [Some (LPPMachineInteger 2),None] 0
    (LPPTreeFailure ([''x'',''y''],LPPFailedGuard (failed_choice_guard 0))) \<and>
  \<not>lpp_check_head_failure failed_choice_program ''2:q'' [Some (LPPMachineInteger 2),None] 0
    (LPPTreeFailure ([''y'',''x''],failed_choice_tree))"
 by eval

ML \<open>
val checked = [@{thm lpp_check_tree_failure_sound}, @{thm lpp_check_head_failure_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted failed choice dependency" else ();
\<close>
end
