theory LP_Prolog_Finite_Head_Test
 imports LP_Prolog_Finite_Head_Check
begin

lemma partial_constructor_head:
 "lpp_check_finite_head [''input''] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''head'',Var ''tail''],Var ''count'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma missing_constructor_groundness_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''head'',Var ''tail''],Var ''count'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma shared_head_variable_anchored:
 "lpp_check_finite_head [''input''] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''shared''],Var ''shared'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma ground_repeated_head:
 "lpp_check_finite_head [''input'',''output''] [Var ''input'',Var ''output'']
   [Fun ''cell'' [Var ''shared''],Var ''shared'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def)

lemma variable_head_unconstrained:
 "lpp_check_finite_head [] [Var ''input'',Var ''output''] [Var ''left'',Var ''right'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma repeated_unconstrained_head_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input'',Var ''output''] [Var ''same'',Var ''same'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma finite_ground_template_unconstrained:
 "lpp_check_finite_head [] [Var ''input'',Var ''output'']
   [Fun ''nil'' [],Fun ''zero'' []]"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def)

lemma nested_ground_template_unconstrained:
 "lpp_check_finite_head [] [Var ''input''] [Fun ''box'' [Fun ''zero'' []]]"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def)

lemma cyclic_binding_template_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input'',Var ''input'']
   [Fun ''cell'' [Var ''tail''],Var ''tail'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_2_eq_2)

lemma ground_template_wrong_arity_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input''] [Fun ''nil'' [],Fun ''zero'' []]"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def)

lemma repeated_head_ground_anchor:
 "lpp_check_finite_head [''answer''] [Var ''input'',Var ''other'',Var ''answer'']
   [Var ''same'',Fun ''zero'' [],Var ''same'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def numeral_3_eq_3 numeral_2_eq_2)

lemma missing_head_anchor_rejected:
 "\<not>lpp_check_finite_head [] [Var ''input'',Var ''other'',Var ''answer'']
   [Var ''same'',Fun ''zero'' [],Var ''same'']"
 by (simp add: lpp_check_anchored_head_def lpp_check_finite_head_def lpp_check_separated_head_def numeral_3_eq_3 numeral_2_eq_2)

ML \<open>
val checked = [@{thm repeated_head_ground_anchor}, @{thm missing_head_anchor_rejected}, @{thm finite_ground_template_unconstrained}, @{thm nested_ground_template_unconstrained},
 @{thm cyclic_binding_template_rejected}, @{thm ground_template_wrong_arity_rejected},
 @{thm partial_constructor_head}, @{thm missing_constructor_groundness_rejected},
 @{thm shared_head_variable_anchored}, @{thm ground_repeated_head},
 @{thm variable_head_unconstrained}, @{thm repeated_unconstrained_head_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite head regressions" else ();
\<close>
end
