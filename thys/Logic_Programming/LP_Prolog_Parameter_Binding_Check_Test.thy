theory LP_Prolog_Parameter_Binding_Check_Test
 imports LP_Prolog_Parameter_Binding_Check
begin

lemma parameter_binding_patterns_checked:
 "lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Var 1) \<and>
  lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Fun 2 [Fun 3 [],Var 1]) \<and>
  lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Fun 4 []) \<and>
  lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Fun 2 [Fun 3 [],Fun 4 []])"
 by simp

lemma parameter_binding_missing_free_rejected:
 "\<not>lpp_check_parameter_binding [] (1::nat) (2::nat) 3 (Var (0::nat)) (Var 1)"
 by simp

lemma parameter_binding_wrong_coordinate_rejected:
 "\<not>lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Var 5)"
 by simp

lemma parameter_binding_compound_selected_rejected:
 "\<not>lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Fun (4::nat) [Var (0::nat)]) (Var 1)"
 by simp

lemma parameter_binding_untracked_leaf_rejected:
 "\<not>lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Fun 2 [Fun 3 [],Fun 4 [Var 5]])"
 by simp

lemma parameter_binding_wrong_marker_rejected:
 "\<not>lpp_check_parameter_binding [0::nat] (1::nat) (2::nat) 3 (Var (0::nat)) (Fun 6 [Fun 3 [],Var 1])"
 by simp

ML \<open>
val checked = @{thms parameter_binding_patterns_checked parameter_binding_missing_free_rejected
 parameter_binding_wrong_coordinate_rejected parameter_binding_compound_selected_rejected
 parameter_binding_untracked_leaf_rejected parameter_binding_wrong_marker_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter binding controls" else ();
\<close>
end
