theory DP_Checkpoint_Composed_Test
 imports DP_Checkpoint_Composed_Summary DP_Checkpoint_Leaf_Test
begin

definition composed_test_rules :: "(nat,nat) rule list" where
 "composed_test_rules = checkpoint_composed_rules 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 [Var 0]"
definition composed_test_receipts :: "(nat,nat) checkpoint_schema_witness list" where
 "composed_test_receipts = leaf_test_receipts @ [Some (8,[Var 0]),
 Some (9,[Var 0,Var 1,Var 2]),Some (10,[Var 0,Var 1,Var 2,Var 3]),
 Some (11,[Var 0,Var 1,Var 2,Var 3,Var 4])]"
lemma composed_test_checked:
 "check_checkpoint_composed_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 [Var 0] composed_test_rules composed_test_receipts"
 by (simp add: check_checkpoint_composed_summary_def composed_test_rules_def composed_test_receipts_def
 leaf_test_receipts_def checkpoint_composed_rules_def checkpoint_leaf_summary_rules_def checkpoint_effect_rules_def checkpoint_list_rules_def checkpoint_list_cons_def)
lemma composed_test_missing_receipt:
 "\<not>check_checkpoint_composed_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 [Var 0] composed_test_rules []"
 by (simp add: check_checkpoint_composed_summary_def composed_test_rules_def checkpoint_composed_rules_def checkpoint_leaf_summary_rules_def checkpoint_effect_rules_def checkpoint_list_rules_def)
lemma composed_test_leaf_replacement:
 "\<not>check_checkpoint_composed_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 [Fun 0 []] composed_test_rules composed_test_receipts"
 by (simp add: check_checkpoint_composed_summary_def)
lemma composed_test_forged_output:
 "\<not>check_checkpoint_composed_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 [Var 0]
 [(Fun 12 [Var 0,Var 1,Var 2],Fun 12 [Var 0,Var 0,Var 2])] [None]"
 by (simp add: check_checkpoint_composed_summary_def)
ML \<open>
val thms = @{thms composed_test_checked composed_test_missing_receipt composed_test_leaf_replacement composed_test_forged_output};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted composition tests" else ();
\<close>
end
