theory LP_Prolog_Repeated_Parameter_Head
 imports LP_Prolog_Runtime_Leaf_Invariant
begin

text \<open>Resolution against a repeated parameter in a head reduces to a
free-output ground equality. The body and active continuation remain part of
the original most-general resolution; no knowledge from a successful return
is assumed. The free output premise excludes compound output subterm binding.\<close>

lemma lpp_repeated_parameter_head_unify:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve
   (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) gs
   (Fun p [t,Var n,Var n]) bs sigma rho"
 and closed: "vars_term t={}" "vars_term u={}"
 shows "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar) gs sigma"
proof -
 have tg: "lp_seg_ground (lp_ieval t LPIVar)"
  and ug: "lp_seg_ground (lp_ieval u LPIVar)"
  using closed by (simp_all add: lp_seg_ground_eval)
 have equation: "lp_isubst (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) sigma =
   lp_ieval (Fun p [t,Var n,Var n]) rho"
  using mgu unfolding lpc_mgu_resolve_def by blast
 have bound: "sigma x=lp_ieval u LPIVar"
  using equation by (auto simp only: lp_isubst_Var lp_isubst_Fun list.map lp_ieval.simps lp_seg_ground_subst[OF ug] lp_iterm.inject list.inject)
 show ?thesis unfolding lpc_mgu_unify_def
 proof (intro conjI allI impI)
  show "lp_isubst (LPIVar x) sigma=lp_isubst (lp_ieval u LPIVar) sigma"
   by (simp add: bound lp_seg_ground_subst[OF ug])
 next
  fix tau :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume eq: "lp_isubst (LPIVar x) tau=lp_isubst (lp_ieval u LPIVar) tau"
  have tnu: "lp_ieval t (\<lambda>_::string. lp_ieval u LPIVar) = lp_ieval t LPIVar"
   by (rule lp_ieval_cong) (use closed in auto)
  have comparison: "lp_isubst
    (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) tau =
    lp_ieval (Fun p [t,Var n,Var n]) (\<lambda>_. lp_ieval u LPIVar)"
   using eq by (simp only: lp_isubst_Var lp_isubst_Fun lp_ieval.simps list.map tnu lp_seg_ground_subst[OF tg] lp_seg_ground_subst[OF ug])
  obtain delta where atom:
    "lp_isubst (lp_isubst (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) sigma) delta =
     lp_isubst (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) tau"
   and rest: "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta)) gs =
     map (lp_cut_map (\<lambda>v. lp_isubst v tau)) gs"
   using mgu comparison unfolding lpc_mgu_resolve_def by blast
  show "\<exists>delta. lp_isubst (lp_isubst (LPIVar x) sigma) delta=lp_isubst (LPIVar x) tau \<and>
    map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta)) gs =
     map (lp_cut_map (\<lambda>v. lp_isubst v tau)) gs"
   by (rule exI[of _ delta]) (use atom rest in \<open>simp add: lp_seg_ground_subst[OF ug]\<close>)
 qed
qed

lemma lpp_repeated_parameter_head_leaf_transport:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve
   (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x])
   (map (lp_cut_map (\<lambda>v. lp_ieval v LPIVar)) gs)
   (Fun p [t,Var n,Var n]) bs sigma rho"
 and closed: "vars_term t={}"
 and allowed: "u\<in>A"
 and ground_templates: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and known: "lpp_runtime_leaf_effect A observed_tree runtime_value"
 and covered: "set2_lp_iterm runtime_value \<subseteq> insert x
   (\<Union>g\<in>set gs. \<Union>v\<in>set (lp_cut_terms g). vars_term v)"
 shows "lpp_runtime_leaf_effect A observed_tree (lp_isubst runtime_value sigma)"
 by (rule lpp_runtime_leaf_effect_ground_binding[OF known
   lpp_repeated_parameter_head_unify[OF mgu closed ground_templates[OF allowed]]
   ground_templates allowed covered])

ML \<open>
val checked = @{thms lpp_repeated_parameter_head_unify lpp_repeated_parameter_head_leaf_transport};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted repeated parameter head" else ();
\<close>
end
