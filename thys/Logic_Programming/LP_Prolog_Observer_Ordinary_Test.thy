theory LP_Prolog_Observer_Ordinary_Test
 imports LP_Prolog_Observer_Ordinary_Check
begin

lemma observer_nonempty_separation_transport:
 "lpp_check_observer_target [[LPPSeparate (Var x) (Var y)]] 0
  (e\<lparr>lpcl_target:=0,lpcl_bindings:=[]\<rparr>)"
 by (simp add: lpp_check_observer_target_def lpp_check_separation_transport_def lp_cut_instance_subst_def)

lemma observer_missing_separation_initialization:
 "\<not>lpp_check_observer_target [[],[observation]] 0 (e\<lparr>lpcl_target:=1\<rparr>)"
 by (simp add: lpp_check_observer_target_def lpp_check_separation_transport_def)

lemma observer_missing_parallel_child:
 "\<not>lpp_check_observer_ordinary contexts i [first_row,second_row] (LPPFParallel [e] factss)"
 by simp

lemma observer_exhausted_helper_not_silent_admin:
 "\<not>lpp_check_observer_ordinary contexts i [(LPCGoals [],payload)]
   (LPPFCut (LPCRAdmin event successor e) fs ns)"
 by simp

lemma observer_arithmetic_requires_separate_contract:
 "\<not>lpp_check_observer_ordinary contexts i ss (LPPFIs result_var middle fs)"
 by simp

ML \<open>
val checked = @{thms observer_nonempty_separation_transport observer_missing_separation_initialization
 observer_missing_parallel_child observer_exhausted_helper_not_silent_admin
 observer_arithmetic_requires_separate_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer ordinary controls" else ();
\<close>
end
