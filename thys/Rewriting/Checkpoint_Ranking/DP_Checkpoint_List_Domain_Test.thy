theory DP_Checkpoint_List_Domain_Test
 imports DP_Checkpoint_List_Domain
begin

definition list_domain_test_rules :: "(nat,nat) rule list" where
 "list_domain_test_rules = checkpoint_list_rules 0 1 2 3 4 5 6 7 8"
definition list_domain_test_receipts :: "(nat,nat) checkpoint_schema_witness list" where
 "list_domain_test_receipts = [Some (0,[Var 0]),Some (1,[Var 0,Var 1,Var 2]),
 Some (2,[Var 0,Var 1,Var 2,Var 3]),Some (3,[Var 0,Var 1,Var 2,Var 3,Var 4])]"
lemma list_domain_test_checked:
 "check_checkpoint_list_domain {0,1,2} 0 1 2 3 4 5 6 7 8 list_domain_test_rules list_domain_test_receipts"
 by (simp add: check_checkpoint_list_domain_def list_domain_test_rules_def list_domain_test_receipts_def
 checkpoint_list_rules_def checkpoint_list_cons_def)
lemma list_domain_test_missing_receipt:
 "\<not>check_checkpoint_list_domain {0,1,2} 0 1 2 3 4 5 6 7 8 list_domain_test_rules []"
 by (simp add: check_checkpoint_list_domain_def list_domain_test_rules_def checkpoint_list_rules_def)
lemma list_domain_test_forged_input:
 "\<not>check_checkpoint_list_domain {0,1,2} 0 1 2 3 4 5 6 7 8
 (list_domain_test_rules @ [(Fun 3 [Var 0,Var 1],Fun 4 [Var 0,Var 0,Var 1])])
 (list_domain_test_receipts @ [None])"
 by (simp add: check_checkpoint_list_domain_def list_domain_test_rules_def list_domain_test_receipts_def
 checkpoint_list_rules_def checkpoint_list_cons_def)
lemma list_domain_test_opaque_elements:
 "checkpoint_list_domain (0::nat) 1 2 (checkpoint_list_cons 0 1 2 (Var ()) (Fun 0 [Fun 1 []]))"
 by (simp add: checkpoint_list_cons_def)
lemma list_domain_test_opaque_tail:
 "\<not>checkpoint_list_domain (0::nat) 1 2 (checkpoint_list_cons 0 1 2 (Var ()) (Var ()))"
 by (simp add: checkpoint_list_cons_def)

ML \<open>
val thms = @{thms list_domain_test_checked list_domain_test_missing_receipt list_domain_test_forged_input
 list_domain_test_opaque_elements list_domain_test_opaque_tail};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted list-domain controls" else ();
\<close>
end
