theory DP_Checkpoint_Ground_Test
 imports DP_Checkpoint_Ground
begin

definition ground_test_rules :: "(nat,nat) rule list" where
 "ground_test_rules = checkpoint_ground_rules 0 1 2 3 4 5 6 7 8 9"
definition ground_test_receipts :: "(nat,nat) checkpoint_schema_witness list" where
 "ground_test_receipts = [Some(0,[Var 0]),Some(1,[Var 0]),Some(2,[]),
   Some(3,[Var 0,Var 1]),Some(4,[Var 0,Var 1]),Some(5,[Var 0,Var 1])]"

lemma ground_test_checked:
 "check_checkpoint_ground_summary {0,1,2,10} 0 1 2 3 4 5 6 7 8 9 ground_test_rules ground_test_receipts"
 by (simp add: check_checkpoint_ground_summary_def ground_test_rules_def ground_test_receipts_def
   checkpoint_ground_rules_def)

lemma missing_ground_receipt_rejected:
 "\<not> check_checkpoint_ground_summary {0,1,2,10} 0 1 2 3 4 5 6 7 8 9 ground_test_rules (tl ground_test_receipts)"
 by (simp add: check_checkpoint_ground_summary_def ground_test_rules_def ground_test_receipts_def
   checkpoint_ground_rules_def)

lemma forged_ground_return_rejected:
 "\<not> check_checkpoint_ground_summary {0,1,2,10} 0 1 2 3 4 5 6 7 8 9
   (ground_test_rules @ [(Fun 3 [Var 0],Fun 4 [Var 0])]) (ground_test_receipts @ [None])"
 by (simp add: check_checkpoint_ground_summary_def ground_test_rules_def ground_test_receipts_def
   checkpoint_ground_rules_def)

lemma missing_ground_constructor_rejected:
 "\<not> check_checkpoint_ground_summary {1,2,10} 0 1 2 3 4 5 6 7 8 9 ground_test_rules ground_test_receipts"
 by (simp add: check_checkpoint_ground_summary_def)

lemma arbitrary_forged_output_not_recognized:
 "(Fun 3 [Fun 4 []],Fun 4 outputs)\<notin>(rstep (set ground_test_rules))\<^sup>*"
proof
 assume success: "(Fun 3 [Fun 4 []],Fun 4 outputs)\<in>(rstep (set ground_test_rules))\<^sup>*"
 show False using checked_checkpoint_ground_success[OF ground_test_checked success] by simp
qed

lemma variable_leaf_not_recognized:
 "(Fun 3 [Fun 10 []],Fun 4 outputs)\<notin>(rstep (set ground_test_rules))\<^sup>*"
proof
 assume success: "(Fun 3 [Fun 10 []],Fun 4 outputs)\<in>(rstep (set ground_test_rules))\<^sup>*"
 show False using checked_checkpoint_ground_success[OF ground_test_checked success] by simp
qed

ML \<open>
val checked = @{thms ground_test_checked missing_ground_receipt_rejected forged_ground_return_rejected
 missing_ground_constructor_rejected arbitrary_forged_output_not_recognized variable_leaf_not_recognized};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground summary controls" else ();
\<close>
end
