theory DP_Checkpoint_Route_Test
 imports DP_Checkpoint_Route
begin
definition route_test_pairs :: "(nat,nat) rule list" where
 "route_test_pairs=[(Fun 0 [Var 0],Fun 1 [Var 0,Var 0]),
 (Fun 1 [Var 1,Var 2],Fun 2 [Var 2]),(Fun 2 [Var 0],Fun 3 [Var 0])]"
lemma route_test_copied_alternative:
 "check_checkpoint_route {0,1,2,3} route_test_pairs [0,1,2] [1,0] (Var 0) (Var 0)"
 by (simp add: route_test_pairs_def)
lemma route_test_wrong_copy:
 "\<not>check_checkpoint_route {0,1,2,3} route_test_pairs [0,1,2] [0,0] (Var 0) (Var 0)"
 by (simp add: route_test_pairs_def)
lemma route_test_missing_connection:
 "\<not>check_checkpoint_route {0,1,2,3} route_test_pairs [0,2] [0] (Var 0) (Var 0)"
 by (simp add: route_test_pairs_def)
lemma route_test_bad_bounds:
 "\<not>check_checkpoint_route {0,1,2,3} route_test_pairs [0,1,2] [2,0] (Var 0) (Var 0)"
 "\<not>check_checkpoint_route {0,1,2,3} route_test_pairs [3] [] (Var 0) (Var 0)"
 by (simp_all add: route_test_pairs_def)
lemma route_test_wrong_property_target:
 "\<not>check_checkpoint_route {0,1,2,3} route_test_pairs [0,1,2] [1,0] (Var 0) (Var 1)"
 by (simp add: route_test_pairs_def)
lemma route_test_missing_coordinate:
 "\<not>check_checkpoint_route {0,1,2,3} route_test_pairs [0,1,2] [1] (Var 0) (Var 0)"
 by (simp add: route_test_pairs_def)
ML \<open>
val thms = @{thms route_test_copied_alternative route_test_wrong_copy route_test_missing_connection route_test_bad_bounds route_test_wrong_property_target route_test_missing_coordinate};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted route controls" else ();
\<close>
end
