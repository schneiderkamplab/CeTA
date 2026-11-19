theory LP_Prolog_Partial_Equality_Successor
 imports LP_Prolog_Partial_Parameter_Equality_Node LP_Prolog_Parameter_Refresh
begin

lemma lpp_partial_equality_successor_values:
 assumes coordinate: "lpp_check_parameter_refresh k l G b target_value bindings"
 and ground_table: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
 and tracked: "lpp_runtime_parameter initial_parameter (lp_ieval b eta)"
 and actual: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) gs sigma"
 defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma eta)"
 shows "lp_ieval target_value nu = lp_ieval b eta \<and>
   lp_isubst (lp_ieval a eta) sigma = lp_ieval target_value nu \<and>
   lpp_runtime_parameter initial_parameter (lp_ieval target_value nu)"
proof -
 have short: "\<forall>x\<in>vars_term b. length x<k"
 and bounds: "2 * k \<le> l"
 and mapped: "target_value \<cdot> lp_cut_instance_subst bindings = b \<cdot> lp_cut_refresh k (set G)"
  using coordinate by (auto simp: lpp_check_parameter_refresh_def)
 have refreshed: "lp_ieval target_value nu = lp_isubst (lp_ieval b eta) sigma"
  unfolding nu_def
  by (simp only: lp_ieval_finite_subst[symmetric] mapped lp_cut_resolution_active[OF short bounds ground_table])
 have fixed: "lp_isubst (lp_ieval b eta) sigma = lp_ieval b eta"
  by (rule lp_seg_ground_subst[OF lpp_runtime_parameter_ground[OF tracked]])
 have equality: "lp_isubst (lp_ieval a eta) sigma = lp_isubst (lp_ieval b eta) sigma"
  using actual by (simp add: lpc_mgu_unify_def)
 show ?thesis using refreshed fixed equality tracked by simp
qed

ML \<open>
val checked = @{thms lpp_partial_equality_successor_values};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted partial equality successor" else ();
\<close>
end
