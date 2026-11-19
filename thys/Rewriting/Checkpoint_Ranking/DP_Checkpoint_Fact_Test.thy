theory DP_Checkpoint_Fact_Test
 imports DP_Checkpoint_Fact_Return
begin

lemma checkpoint_fact_copy_positive:
 "check_checkpoint_clause_copy [CP_Split 0 2,CP_Guard 1]
 [Var (0::nat),Var 1,Var 2] [CP_Guard 0,CP_Split 2 1] [Var 1,Var 2,Var 0]"
 by (simp add: check_checkpoint_clause_copy_def checkpoint_atom_bounded_def check_checkpoint_fact_copy_def)

lemma checkpoint_fact_copy_negative:
 "\<not>check_checkpoint_clause_copy [CP_Guard 0] [Var (0::nat),Var 1]
 [CP_Guard 1] [Var 0,Var 1]"
 "\<not>check_checkpoint_clause_copy [CP_Guard 2] [Var (0::nat),Var 1] [] []"
 "\<not>check_checkpoint_clause_copy [] [] [CP_Guard 0] [Var (0::nat)]"
 by (simp_all add: check_checkpoint_clause_copy_def checkpoint_atom_bounded_def check_checkpoint_fact_copy_def)

lemma checkpoint_fact_list_guard_binding:
 "check_checkpoint_fact_list_start (9::nat) (Var (0::nat)) (Var 1) (Var 2)
 (CP_Split 0 1,[Var 0,Var 1]) (CP_Guard 0,[Var 2])
 (CP_List 9 0 1,[Fun 9 [Var 1,Var 2],Var 0])"
 "\<not>check_checkpoint_fact_list_start (9::nat) (Var (0::nat)) (Var 1) (Var 2)
 (CP_Split 0 1,[Var 0,Var 1]) (CP_Guard 0,[Var 3])
 (CP_List 9 0 1,[Fun 9 [Var 1,Var 2],Var 0])"
 "\<not>check_checkpoint_fact_list_start (9::nat) (Var (0::nat)) (Var 1) (Var 2)
 (CP_Split 0 1,[Var 0,Var 1]) (CP_Guard 0,[Var 2])
 (CP_List 9 0 1,[Fun 9 [Var 3,Var 2],Var 0])"
 by (simp_all add: check_checkpoint_fact_list_start_def)

lemma checkpoint_fact_forged_return:
 "\<not>check_checkpoint_fact_arguments_return (8::nat) (9::nat) (Var (0::nat)) (Var 1)
 (CP_Arguments 8 0,[Fun 9 [Var 0,Var 1]]) (CP_Strict 0,[Var 2])"
 "\<not>check_checkpoint_fact_ground_return (8::nat) (9::nat) (Var (0::nat)) (Var 1)
 (CP_Ground 8 0 1,[Fun 10 [Var 0],Var 1]) (CP_Guard 0,[Var 1])"
 "\<not>check_checkpoint_fact_list_return (8::nat) (9::nat) (Var (0::nat)) (Var 1) (Var 2) (Var 3)
 (CP_List 8 0 1,[Fun 9 [Var 0,Var 1,Var 2],Var 3]) (CP_Strict 0,[Var 0])"
 by (simp_all add: check_checkpoint_fact_arguments_return_def check_checkpoint_fact_ground_return_def check_checkpoint_fact_list_return_def)

ML \<open>
val thms = @{thms checkpoint_fact_copy_positive checkpoint_fact_copy_negative checkpoint_fact_list_guard_binding checkpoint_fact_forged_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted fact checker controls" else ();
\<close>
end
