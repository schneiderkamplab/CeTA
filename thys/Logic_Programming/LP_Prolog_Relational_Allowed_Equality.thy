theory LP_Prolog_Relational_Allowed_Equality
 imports LP_Prolog_Relational_Ground_Equality LP_Prolog_Repeated_Parameter_Head
begin

text \<open>The relational coverage checker can justify a restricted replacement
set when the selected equality binds a free runtime variable to an explicitly
allowed ground template. Groundness alone is insufficient.\<close>

lemma lpp_runtime_allowed_binding_images:
 assumes mgu: "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar) gs sigma"
 and finite_rest: "lpp_finite_goals gs"
 and ground: "vars_term u={}"
 and allowed: "u\<in>A"
 and covered: "V \<subseteq> insert x
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images A sigma V"
proof -
 obtain qs where rest: "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
  using lpp_finite_goal_templates[OF finite_rest] by blast
 have represented: "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs) sigma"
  using mgu rest by simp
 have support: "V \<subseteq> insert x
   (\<Union>g\<in>set qs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered unfolding rest[symmetric]
  by (simp only: lpp_evaluated_goals_runtime_support)
 show ?thesis by (rule lpp_ground_binding_bounded_images[OF represented ground allowed support])
qed

lemma lpp_relational_allowed_equality_leaf_transport:
 assumes coverage: "lpp_check_relational_leaf_coverage facts (map fst specs) payload a gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and selected_free: "lp_ieval a eta=LPIVar x"
 and allowed: "u\<in>A"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport A specs (lpc_return_env payload eta) sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect A shape (lpc_return_env payload eta slot)"
 have support: "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval a eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  by (rule lpp_relational_leaf_coverage_sound[OF coverage facts]) (use member in auto)
 have images: "lpp_bounded_images A sigma (set2_lp_iterm (lpc_return_env payload eta slot))"
  by (rule lpp_runtime_allowed_binding_images[OF _ finite_rest ground[OF allowed] allowed])
    (use mgu support in \<open>simp_all add: selected_free\<close>)
 show "lpp_runtime_leaf_effect A shape (lp_isubst (lpc_return_env payload eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known images ground])
qed

lemma lpp_runtime_repeated_parameter_images:
 assumes mgu: "lpc_mgu_resolve
   (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) gs
   (Fun p [t,Var n,Var n]) bs sigma rho"
 and finite_rest: "lpp_finite_goals gs"
 and closed: "vars_term t={}" "vars_term u={}"
 and allowed: "u\<in>A"
 and covered: "V \<subseteq>
   set2_lp_iterm (LPIFun p [lp_ieval t LPIVar,lp_ieval u LPIVar,LPIVar x]) \<union>
   (\<Union>g\<in>set gs. \<Union>v\<in>set (lp_cut_terms g). set2_lp_iterm v)"
 shows "lpp_bounded_images A sigma V"
 by (rule lpp_runtime_allowed_binding_images[OF
   lpp_repeated_parameter_head_unify[OF mgu closed] finite_rest closed(2) allowed])
   (use covered in \<open>simp add: lpp_template_runtime_support closed\<close>)

ML \<open>
val checked = @{thms lpp_runtime_allowed_binding_images lpp_relational_allowed_equality_leaf_transport lpp_runtime_repeated_parameter_images};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted allowed relational equality" else ();
\<close>
end
