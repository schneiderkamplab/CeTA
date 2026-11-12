theory LP_Prolog_List_Observation_Test
 imports LP_Prolog_NO_List
begin

primcorec lpp_test_cyclic_spine :: "(string lp_cut_symbol,string) lp_iterm" where
 "lpp_test_cyclic_spine = LPIFun (LPCUser ''2:prolog_data_2e'')
   [LPIVar ''head'',lpp_test_cyclic_spine]"

lemma cyclic_spine_is_not_finite:
 "\<not> lpp_list_length lpp_test_cyclic_spine n"
 by (rule lpp_list_length_no_cyclic_spine)
    (rule lpp_test_cyclic_spine.code)

lemma rational_element_is_a_proper_list:
 "lpp_list_observation
   (LPIFun (LPCUser ''2:prolog_data_2e'')
     [lpp_test_cyclic_spine,LPIFun (LPCUser ''0:prolog_data_5b5d'') []]) True"
 by (intro lpp_list_observation.cons lpp_list_observation.nil)

lemma observed_variable_head:
 "lpp_check_list_observation 2
   (Fun (LPCUser ''2:prolog_data_2e'') [Var ''head'',Fun (LPCUser ''0:prolog_data_5b5d'') []]) = Some True"
 by (simp add: numeral_2_eq_2)

lemma checked_rational_element:
 "lpp_stable_source_builtin operation ''1:is_list''
   [lp_ieval (Fun (LPCUser ''2:prolog_data_2e'')
     [Var ''head'',Fun (LPCUser ''0:prolog_data_5b5d'') []])
       (\<lambda>_. lpp_test_cyclic_spine)] (LPPBuiltinSuccess LPIVar)"
 using lpp_no_list_outcome[OF observed_variable_head,
   where operation=operation and eta="\<lambda>_. lpp_test_cyclic_spine"] by (simp add: numeral_2_eq_2)

lemma open_spine_is_not_classified:
 "lpp_check_list_observation fuel (Var ''tail'') = None"
 by (cases fuel) simp_all

lemma improper_spine_fails:
 "lpp_check_list_observation 2
   (Fun (LPCUser ''2:prolog_data_2e'') [Var ''head'',Fun (LPCUser ''0:atom'') []]) = Some False"
 by (simp add: numeral_2_eq_2)

lemma exhausted_spine_is_not_classified:
 "lpp_check_list_observation 1
   (Fun (LPCUser ''2:prolog_data_2e'') [Var ''head'',Fun (LPCUser ''0:prolog_data_5b5d'') []]) = None"
 by (simp add: numeral_2_eq_2)

ML \<open>
val checked = [@{thm cyclic_spine_is_not_finite}, @{thm rational_element_is_a_proper_list},
 @{thm observed_variable_head}, @{thm checked_rational_element}, @{thm open_spine_is_not_classified},
 @{thm improper_spine_fails}, @{thm exhausted_spine_is_not_classified}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted list observation regression" else ();
\<close>
end
