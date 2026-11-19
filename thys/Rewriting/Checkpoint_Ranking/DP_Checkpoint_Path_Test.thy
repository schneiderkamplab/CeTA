theory DP_Checkpoint_Path_Test
 imports DP_Checkpoint_Path DP_Checkpoint_Test
begin

text \<open>Structural coverage and a populated annotation are not descent.
Conversely, a vacuous annotation cannot discharge an actual entry transition.\<close>
lemma checkpoint_true_annotation_not_descent:
 "checkpoint_rule_contract {} (\<lambda>_. True) (\<lambda>_. True) (Fun (0::nat) [],Fun 0 [])"
 "\<not> ((0::nat),0)\<in>less_than"
 by (simp_all add: checkpoint_rule_contract_def)

lemma checkpoint_false_annotation_entry_rejected:
 "\<not>checkpoint_rule_contract ({}::(nat,nat) trs)
 (\<lambda>s. s=Fun 0 []) (\<lambda>_. False) (Fun 0 [],Fun 0 [])"
 by (simp add: checkpoint_rule_contract_def)

lemma checkpoint_omitted_rule_changes_contract:
 "list_all (checkpoint_rule_contract ({}::(nat,nat) trs) (\<lambda>_. True) (\<lambda>_. False)) []"
 "\<not>list_all (checkpoint_rule_contract ({}::(nat,nat) trs) (\<lambda>_. True) (\<lambda>_. False)) [(Fun 0 [],Fun 0 [])]"
 by (simp_all add: checkpoint_rule_contract_def)

ML \<open>
val thms = @{thms checkpoint_true_annotation_not_descent checkpoint_false_annotation_entry_rejected checkpoint_omitted_rule_changes_contract checkpoint_self_loop_not_finite};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted path controls" else ();
\<close>
end
