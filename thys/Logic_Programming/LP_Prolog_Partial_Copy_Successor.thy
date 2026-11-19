theory LP_Prolog_Partial_Copy_Successor
 imports LP_Prolog_Observer_Partial_Copy_Node
begin

lemma lpp_partial_copy_successor_values:
 fixes k :: nat and eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes parameter_coordinate: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and output_coordinate: "lpp_check_clause_coordinate l (Var n) target_output bindings"
 and actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"
 shows "lp_ieval target_parameter nu= parameter \<and> lp_ieval target_output nu= parameter \<and>
   lpp_runtime_parameter initial_parameter (lp_ieval target_parameter nu) \<and>
   lpp_runtime_parameter initial_parameter (lp_ieval target_output nu)"
proof -
 have ground: "lp_seg_ground parameter" by (rule lpp_runtime_parameter_ground[OF tracked])
 have eq: "lp_isubst (LPIFun p [input_value,parameter,output_value]) sigma=
   lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho"
  using actual by (simp only: lpc_mgu_resolve_def)
 have copied: "rho n= parameter" using eq lp_seg_ground_subst[OF ground, of sigma] by auto
 have param: "lp_ieval target_parameter nu=rho n"
  using lpp_checked_clause_coordinate_value[OF parameter_coordinate, of k eta sigma rho]
  by (simp add: nu_def)
 have out: "lp_ieval target_output nu=rho n"
  using lpp_checked_clause_coordinate_value[OF output_coordinate, of k eta sigma rho]
  by (simp add: nu_def)
 show ?thesis using copied param out tracked by simp
qed

ML \<open>
val checked = @{thms lpp_partial_copy_successor_values};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted partial copy successor" else ();
\<close>
end
