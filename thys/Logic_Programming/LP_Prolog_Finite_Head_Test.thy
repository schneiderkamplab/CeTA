theory LP_Prolog_Finite_Head_Test
 imports LP_Prolog_Finite_Head_Check
begin

lemma partial_constructor_head:
 "lpp_check_finite_head [''input''] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''head'',Var ''tail''],Var ''count'']"
 by (simp add: lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma missing_constructor_groundness_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''head'',Var ''tail''],Var ''count'']"
 by (simp add: lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma shared_head_variable_rejected:
 "\<not>lpp_check_finite_head [''input''] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''shared''],Var ''shared'']"
 by (simp add: lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma ground_repeated_head:
 "lpp_check_finite_head [''input'',''output''] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''shared''],Var ''shared'']"
 by (simp add: lpp_check_finite_head_def)

lemma variable_head_unconstrained:
 "lpp_check_finite_head [] [Var ''input'',Var ''output''] [Var ''left'',Var ''right'']"
 by (simp add: lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma repeated_unconstrained_head_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input'',Var ''output''] [Var ''same'',Var ''same'']"
 by (simp add: lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

ML \<open>
val checked = [@{thm partial_constructor_head}, @{thm missing_constructor_groundness_rejected},
 @{thm shared_head_variable_rejected}, @{thm ground_repeated_head},
 @{thm variable_head_unconstrained}, @{thm repeated_unconstrained_head_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite head regressions" else ();
\<close>
end
