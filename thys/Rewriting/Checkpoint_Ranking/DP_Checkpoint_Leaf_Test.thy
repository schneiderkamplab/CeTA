theory DP_Checkpoint_Leaf_Test
 imports DP_Checkpoint_Leaf_Summary
begin

definition leaf_test_rules :: "(nat,nat) rule list" where
 "leaf_test_rules = checkpoint_leaf_summary_rules 0 1 2 3 4 5 6 7 8 9 10 [Var 0]"
definition leaf_test_receipts :: "(nat,nat) checkpoint_schema_witness list" where
 "leaf_test_receipts = [Some (0,[Var 0]),Some (1,[Var 0,Var 1]),Some (2,[Var 0,Var 1,Var 2]),
 Some (3,[Var 0]),Some (4,[Var 0,Var 1,Var 2]),Some (5,[Var 0,Var 1,Var 2,Var 3]),
 Some (6,[Var 0,Var 1,Var 2,Var 3,Var 4]),Some (7,[Var 0])]"
lemma leaf_test_checked:
 "check_checkpoint_leaf_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 [Var 0] leaf_test_rules leaf_test_receipts"
 by (simp add: check_checkpoint_leaf_summary_def leaf_test_rules_def leaf_test_receipts_def
 checkpoint_leaf_summary_rules_def checkpoint_effect_rules_def)
lemma leaf_test_leaf_template_rejected:
 "\<not>check_checkpoint_leaf_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 [Fun 0 []] leaf_test_rules leaf_test_receipts"
 by (simp add: check_checkpoint_leaf_summary_def)
lemma leaf_test_wrong_parameter_rejected:
 "\<not>check_checkpoint_leaf_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 [Var 1] leaf_test_rules leaf_test_receipts"
 by (simp add: check_checkpoint_leaf_summary_def)
lemma leaf_test_missing_receipt_rejected:
 "\<not>check_checkpoint_leaf_summary {0,1,2,3} 0 1 2 3 4 5 6 7 8 9 10 [Var 0] leaf_test_rules []"
 by (simp add: check_checkpoint_leaf_summary_def leaf_test_rules_def checkpoint_leaf_summary_rules_def checkpoint_effect_rules_def)
lemma leaf_test_growing_replacement_not_related:
 "\<not>checkpoint_leaf_relation (0::nat) (Fun 0 []) (Fun 1 [Fun 0 [],Fun 0 []])"
 using checkpoint_leaf_relation_rigidity[of "(0::nat)" "Fun 0 []" "Fun 1 [Fun 0 [],Fun 0 []]"] by auto

ML \<open>
val thms = @{thms leaf_test_checked leaf_test_leaf_template_rejected leaf_test_wrong_parameter_rejected
 leaf_test_missing_receipt_rejected leaf_test_growing_replacement_not_related};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted leaf controls" else ();
\<close>
end
