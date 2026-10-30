theory LP_Return_Shape_Contracts_Test
  imports LP_Return_Shape_Contracts LP_Return_Shapes_Test
begin

definition lprc_copy :: "(nat,nat) lp_clause list" where
  "lprc_copy = [((10,[Fun 0 [],Fun 0 []]),[]),
    ((10,[Fun 1 [Var 0,Var 1],Fun 1 [Var 0,Var 2]]),[(10,[Var 1,Var 2])])]"

definition lprc_modes where
  "lprc_modes = [(10::nat,[LPReturnShape 0,LPReturnAny],[LPReturnShape 0,LPReturnShape 0])]"

lemma lprc_copy_checked:
  "lp_return_shape_program_check 8 lprs_spine lprc_modes lprc_copy"
  by (simp add: lp_return_shape_program_check_def lp_return_shape_clause_check_def
    lp_return_args_facts_def lp_return_mode_facts_def lprc_copy_def lprc_modes_def
    lprs_spine_def eval_nat_numeral)

lemma lprc_copy_sound:
  "lp_return_shape_model lprc_copy lprs_spine lprc_modes"
  by (rule lp_return_shape_program_check_sound[OF lprc_copy_checked])

lemma lprc_missing_helper_mode_rejected:
  "\<not>lp_return_shape_clause_check 8 lprs_spine [] (lprc_copy!1) (hd lprc_modes)"
  by (simp add: lp_return_shape_clause_check_def lp_return_args_facts_def
    lprc_copy_def lprc_modes_def lprs_spine_def eval_nat_numeral)

lemma lprc_exhausted_fuel_retains_obligation:
  "lp_return_shape_facts 0 lprs_spine (LPReturnShape 0) (Fun 7 []) = Some []"
  by simp

lemma lprc_wrong_constructor_impossible:
  "lp_return_shape_facts 2 lprs_spine (LPReturnShape 0) (Fun 7 []) = None"
  by (simp add: lprs_spine_def eval_nat_numeral)


definition lprc_key_producer :: "(nat,nat) lp_clause list" where
  "lprc_key_producer = [((11,[Fun 0 [],Fun 0 []]),[]),
    ((11,[Fun 1 [Var 0,Var 1],Fun 1 [Fun 2 [Var 0,Var 3],Var 2]]),[(11,[Var 1,Var 2])])]"

definition lprc_key_modes where
  "lprc_key_modes = [(11::nat,[LPReturnGround,LPReturnAny],[LPReturnGround,LPReturnShape 0])]"

lemma lprc_partial_ground_keys_checked:
  "lp_return_shape_program_check 8 lprs_keyed lprc_key_modes lprc_key_producer"
  by (simp add: lp_return_shape_program_check_def lp_return_shape_clause_check_def
    lp_return_args_facts_def lp_return_mode_facts_def lprc_key_producer_def lprc_key_modes_def
    lprs_keyed_def eval_nat_numeral)

end
