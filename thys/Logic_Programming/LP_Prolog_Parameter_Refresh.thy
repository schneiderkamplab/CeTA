theory LP_Prolog_Parameter_Refresh
 imports LP_Prolog_Runtime_Parameter LP_Cut_Resolve
begin

text \<open>Raw ground tables determine refreshing. Contextual groundness can
prove a parameter closed, but cannot change the syntactic refresh map.\<close>

definition lpp_check_parameter_refresh where
 "lpp_check_parameter_refresh k l G before_parameter after_parameter bindings =
  (2 * k \<le> l \<and> (\<forall>x\<in>vars_term before_parameter. length x<k) \<and>
   after_parameter \<cdot> lp_cut_instance_subst bindings =
    before_parameter \<cdot> lp_cut_refresh k (set G))"

lemma lpp_checked_parameter_refresh:
 assumes checked: "lpp_check_parameter_refresh k l G before_parameter after_parameter bindings"
 and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
 and tracked: "lpp_runtime_parameter c (lp_ieval before_parameter eta)"
 shows "lpp_runtime_parameter c (lp_ieval after_parameter
  (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)))"
proof -
 have short: "\<forall>x\<in>vars_term before_parameter. length x<k" and bounds: "2 * k \<le> l"
 and coordinates: "after_parameter \<cdot> lp_cut_instance_subst bindings =
   before_parameter \<cdot> lp_cut_refresh k (set G)"
  using checked by (auto simp: lpp_check_parameter_refresh_def)
 have actual: "lp_ieval after_parameter
   (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)) =
   lp_isubst (lp_ieval before_parameter eta) sigma"
  by (simp only: lp_ieval_finite_subst[symmetric] coordinates
    lp_cut_resolution_active[OF short bounds ground])
 show ?thesis using lpp_runtime_parameter_subst[OF tracked, of sigma] by (simp add: actual)
qed

lemma lpp_parameter_refresh_context_only:
 "lpp_check_parameter_refresh 3 6 [] (Var ''V1'' :: (nat,string) term)
  (Var ''V1'') [(''V1'',Var ''$$$V1'')]"
 by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def lp_prefix_def numeral_3_eq_3)

lemma lpp_parameter_refresh_raw_ground:
 "lpp_check_parameter_refresh 3 6 [''V1''] (Var ''V1'' :: (nat,string) term)
  (Var ''V1'') [(''V1'',Var ''V1'')]"
 by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def)

lemma lpp_parameter_refresh_context_is_not_raw:
 "\<not>lpp_check_parameter_refresh 3 6 [] (Var ''V1'' :: (nat,string) term)
  (Var ''V1'') [(''V1'',Var ''V1'')]"
 by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def lp_prefix_def numeral_3_eq_3)

lemma lpp_parameter_refresh_bad_bounds:
 "\<not>lpp_check_parameter_refresh 3 5 G before_parameter after_parameter bindings"
 by (simp add: lpp_check_parameter_refresh_def)

lemma lpp_parameter_refresh_wrong_coordinate:
 "\<not>lpp_check_parameter_refresh 3 6 [] (Var ''V1'' :: (nat,string) term)
  (Var ''V1'') [(''V1'',Var ''$$$V2'')]"
 by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def lp_prefix_def numeral_3_eq_3)

ML \<open>
val checked = @{thms lpp_checked_parameter_refresh lpp_parameter_refresh_context_only
 lpp_parameter_refresh_raw_ground lpp_parameter_refresh_context_is_not_raw
 lpp_parameter_refresh_bad_bounds lpp_parameter_refresh_wrong_coordinate};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter refresh" else ();
\<close>
end
