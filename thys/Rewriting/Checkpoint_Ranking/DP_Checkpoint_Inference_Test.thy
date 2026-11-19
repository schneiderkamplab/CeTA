theory DP_Checkpoint_Inference_Test
 imports DP_Checkpoint_Inference DP_Checkpoint_Fact_Test
begin

abbreviation fact_test_checker where
 "fact_test_checker \<equiv> check_checkpoint_inference (1::nat) 2 3 [] [] []"

lemma checkpoint_inference_unknown_code:
 "\<not>fact_test_checker [] (9,[],[],[]) claim"
 by (simp add: check_checkpoint_inference_def)

lemma checkpoint_inference_future_reference:
 "\<not>fact_test_checker [] (2,[],[Var (0::nat),Var 1],[0]) (CP_Prefix 0,[Var 0])"
 by (simp add: check_checkpoint_inference_def)

lemma checkpoint_inference_missing_summary:
 "\<not>fact_test_checker [(CP_Arguments 8 0,[Fun 9 [Var (0::nat),Var 1]])]
 (6,[8,9],[Var 0,Var 1],[0]) (CP_Strict 0,[Var 1])"
 by (simp add: check_checkpoint_inference_def)

lemma checkpoint_inference_wrong_guard:
 "\<not>fact_test_checker [(CP_Split 0 1,[Var (0::nat),Var 1]),(CP_Guard 0,[Var 3])]
 (5,[9],[Var 0,Var 1,Var 2],[0,1]) (CP_List 9 0 1,[Fun 9 [Var 1,Var 2],Var 0])"
 by (simp add: check_checkpoint_inference_def check_checkpoint_fact_list_start_def)

lemma checkpoint_derivation_positive:
 "check_checkpoint_clause_derivation fact_test_checker [CP_Split 0 1,CP_Guard 2]
 [Var (0::nat),Var 1,Var 2]
 [((2,[],[Var 0,Var 1],[0]),(CP_Prefix 0,[Var 0])),
  ((5,[9],[Var 0,Var 1,Var 2],[1,2]),(CP_List 9 0 1,[Fun 9 [Var 1,Var 2],Var 0]))]
 [CP_List 9 0 1,CP_Prefix 1] [Fun 9 [Var 1,Var 2],Var 0]"
 by (simp add: check_checkpoint_clause_derivation_def checkpoint_atom_bounded_def
 check_checkpoint_inference_def check_checkpoint_fact_prefix_def check_checkpoint_fact_list_start_def
 checkpoint_derived_def check_checkpoint_fact_copy_def)

lemma checkpoint_derivation_circular_reference:
 "\<not>check_checkpoint_derivation fact_test_checker []
 [((2,[],[Var (0::nat),Var 1],[0]),(CP_Prefix 0,[Var 0]))]"
 by (simp add: check_checkpoint_inference_def)


definition checkpoint_inference_smoke :: "bool list" where
 "checkpoint_inference_smoke = [
 fact_test_checker [(CP_Split 0 1,[Var (0::nat),Var 1])]
 (2,[],[Var 0,Var 1],[0]) (CP_Prefix 0,[Var 0]),
 fact_test_checker [] (2,[],[Var (0::nat),Var 1],[0]) (CP_Prefix 0,[Var 0]),
 fact_test_checker [(CP_Arguments 8 0,[Fun 9 [Var (0::nat),Var 1]])]
 (6,[8,9],[Var 0,Var 1],[0]) (CP_Strict 0,[Var 1]),
 check_checkpoint_derivation fact_test_checker []
 [((2,[],[Var (0::nat),Var 1],[0]),(CP_Prefix 0,[Var 0]))]]"

lemma checkpoint_inference_smoke_expected:
 "checkpoint_inference_smoke=[True,False,False,False]"
 by (simp add: checkpoint_inference_smoke_def check_checkpoint_inference_def check_checkpoint_fact_prefix_def)

ML \<open>
val thms = @{thms checkpoint_inference_unknown_code checkpoint_inference_future_reference checkpoint_inference_missing_summary checkpoint_inference_wrong_guard checkpoint_derivation_positive checkpoint_derivation_circular_reference checkpoint_inference_smoke_expected};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted inference controls" else ();
\<close>
end
