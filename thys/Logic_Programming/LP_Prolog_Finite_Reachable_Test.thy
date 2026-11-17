theory LP_Prolog_Finite_Reachable_Test
 imports LP_Prolog_Finite_Direct_XML
begin

lemma unreachable_nonlinear_library_retained:
 "lpp_check_finite_reachable_clause {(''q'',1)}
   (Fun (LPCUser ''library'') [Var ''x'',Var ''x''],[LPCMeta (Var ''x'')])"
 by simp

lemma reachable_nonlinear_head_rejected:
 "\<not>lpp_check_finite_reachable_clause {(''library'',2)}
   (Fun (LPCUser ''library'') [Var ''x'',Var ''x''],[])"
 by simp

lemma omitted_reachable_callee_rejected:
 "\<not>lpp_check_finite_reachable_clause {(''q'',1)}
   (Fun (LPCUser ''q'') [Var ''x''],[LPCAtom (Fun (LPCUser ''helper'') [Var ''x''])])"
 by simp

lemma unknown_head_never_ignored:
 "\<not>lpp_check_finite_reachable_clause A (Var x,bs)"
 by simp

lemma root_rejects_initial_free_claim:
 assumes "Fs!0\<noteq>[]"
 shows "\<not>lpp_check_finite_direct_root fuel P Q nds states contexts Fs T returned arity actions ranks signatures q modes"
 using assms by (simp add: lpp_check_finite_direct_root_def)

lemma root_rejects_missing_action:
 assumes "None\<in>set actions"
 shows "\<not>lpp_check_finite_direct_root fuel P Q nds states contexts Fs T returned arity actions ranks signatures q modes"
 using assms by (auto simp: lpp_check_finite_direct_root_def list_all_iff)

end
