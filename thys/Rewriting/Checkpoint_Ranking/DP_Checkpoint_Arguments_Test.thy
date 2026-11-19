theory DP_Checkpoint_Arguments_Test
 imports DP_Checkpoint_Arguments
begin

definition argument_test_rules :: "(nat,nat) rule list" where
 "argument_test_rules = checkpoint_argument_rules 0 1 2 3 4 5"
definition argument_test_receipts :: "(nat,nat) checkpoint_schema_witness list" where
 "argument_test_receipts = [Some (0,[]),Some (1,[Var 0,Var 1]),Some (2,[Var 0,Var 1,Var 2])]"
lemma argument_test_checked:
 "check_checkpoint_argument_summary {0,1,2} 0 1 2 3 4 5 argument_test_rules argument_test_receipts"
 by (simp add: check_checkpoint_argument_summary_def argument_test_rules_def argument_test_receipts_def
   checkpoint_argument_rules_def checkpoint_list_cons_def)
lemma argument_test_missing_receipt:
 "\<not> check_checkpoint_argument_summary {0,1,2} 0 1 2 3 4 5 argument_test_rules (tl argument_test_receipts)"
 by (simp add: check_checkpoint_argument_summary_def argument_test_rules_def argument_test_receipts_def
   checkpoint_argument_rules_def)
lemma argument_test_forged_output_rule:
 "\<not> check_checkpoint_argument_summary {0,1,2} 0 1 2 3 4 5
   (argument_test_rules @ [(Fun 4 [Var 0,Var 1],Fun 4 [Var 0,Var 0])])
   (argument_test_receipts @ [None])"
 by (simp add: check_checkpoint_argument_summary_def argument_test_rules_def argument_test_receipts_def
   checkpoint_argument_rules_def checkpoint_list_cons_def)
lemma argument_test_wrong_coordinate:
 "\<not> check_checkpoint_argument_summary {0,1,2} 0 1 2 3 4 5 argument_test_rules
   [Some (0,[]),Some (1,[Var 0,Var 1]),Some (2,[Var 1,Var 0,Var 2])]"
 by (simp add: check_checkpoint_argument_summary_def argument_test_rules_def
   checkpoint_argument_rules_def checkpoint_list_cons_def)
lemma argument_test_no_forged_children:
 "(Fun 3 [Fun 1 []],Fun 4 [copied,result])\<in>(rstep (set argument_test_rules))\<^sup>* \<Longrightarrow>
 checkpoint_skeleton {0,1,2} result=Fun 0 [Fun 1 []]"
proof -
 assume success: "(Fun 3 [Fun 1 []],Fun 4 [copied,result])\<in>(rstep (set argument_test_rules))\<^sup>*"
 show "checkpoint_skeleton {0,1,2} result=Fun 0 [Fun 1 []]"
  using checked_checkpoint_argument_success[OF argument_test_checked success] by simp
qed
ML \<open>
val thms = @{thms argument_test_checked argument_test_missing_receipt argument_test_forged_output_rule
 argument_test_wrong_coordinate argument_test_no_forged_children};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted extraction tests" else ();
\<close>
end
