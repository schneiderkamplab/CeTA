theory LP_Prolog_Stable_Computed_Sequence_Test
  imports LP_Prolog_Stable_Computed_Sequence_Return
begin

definition sequence_test_rows :: "string lpp_observed_triple list" where
  "sequence_test_rows = [(((''probe'',[Var ''a'',Var ''b'']),[],
      (''probe'',[Var ''a'',Var ''b'']),[]),[])]"

lemma checked_second_stage_uses_first_stage:
  "lpp_check_expansion_sequence
    [(\<lambda>_. [(LPCUser ''quotient'',[0,1])]),
     (\<lambda>_. [(LPCUser ''difference'',[2,1])])] sequence_test_rows"
  by (simp add: sequence_test_rows_def lpp_check_argument_expansion_def
    lpp_expand_call_def lpp_select_arguments_def)

lemma missing_first_stage_is_rejected:
  "\<not> lpp_check_expansion_sequence
    [(\<lambda>_. [(LPCUser ''difference'',[2,1])])] sequence_test_rows"
  by (simp add: sequence_test_rows_def lpp_check_argument_expansion_def)

lemma invalid_later_stage_is_rejected:
  "\<not> lpp_check_expansion_sequence
    [(\<lambda>_. [(LPCUser ''quotient'',[0,1])]),
     (\<lambda>_. [(LPCUser ''difference'',[3,1])])] sequence_test_rows"
  by (simp add: sequence_test_rows_def lpp_check_argument_expansion_def
    lpp_expand_call_def lpp_select_arguments_def)

ML \<open>
val checked = [@{thm checked_second_stage_uses_first_stage},
 @{thm missing_first_stage_is_rejected}, @{thm invalid_later_stage_is_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted computed sequence test dependency" else ();
\<close>
end
