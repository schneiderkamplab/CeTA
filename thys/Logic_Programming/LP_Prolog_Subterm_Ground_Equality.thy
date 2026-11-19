theory LP_Prolog_Subterm_Ground_Equality
 imports LP_Prolog_Relational_Ground_Equality LP_Prolog_Ground_Output_Images
begin

text \<open>Ground equality with arbitrary finite selected output. Closing allowed
replacements under subterms covers images forced inside partial output patterns.\<close>

lemma lpp_subterm_ground_equality_images:
 fixes sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a (lp_ieval u LPIVar) gs sigma"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals gs"
 and ground: "vars_term u = {}"
 and allowed: "u\<in>A"
 and closed: "\<And>v. lpp_finite_template_subterm v u \<Longrightarrow> v\<in>A"
 and covered: "V\<subseteq> set2_lp_iterm a \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images A sigma V"
proof -
 obtain call where call: "a=lp_ieval call LPIVar"
  using lpp_finite_runtime_template[OF finite_call] by blast
 obtain rest where rest: "gs=map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) rest"
  using lpp_finite_goal_templates[OF finite_rest] by blast
 have resolution: "lpc_mgu_resolve (lp_ieval call LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) rest) u [] sigma LPIVar"
  by (rule lpp_ground_unify_resolution[OF mgu[unfolded call rest] ground])
 have equation: "lp_isubst (lp_ieval call LPIVar) sigma=lp_ieval u LPIVar"
  using resolution by (simp add: lpc_mgu_resolve_def)
 have selected: "lpp_bounded_images A sigma (vars_term call)"
 proof (unfold lpp_bounded_images_def, intro ballI)
  fix x assume member: "x\<in>vars_term call"
  obtain v where sub: "lpp_finite_template_subterm v u" and image: "sigma x=lp_ieval v LPIVar"
   using lpp_ground_instance_variable_subterm[OF equation ground member] by blast
  show "(\<exists>y. sigma x=LPIVar y) \<or> (\<exists>v\<in>A. sigma x=lp_ieval v LPIVar)"
   using closed[OF sub] image by blast
 qed
 have support: "V\<subseteq> vars_term call \<union>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered unfolding call rest
  by (simp only: lpp_template_runtime_support lpp_evaluated_goals_runtime_support)
 show ?thesis by (rule lpp_resolution_extends_bounded_call_images[OF resolution selected support])
qed

lemma lpp_parameter_subterm_equality_leaf:
 assumes mgu: "lpc_mgu_unify a (lp_ieval u LPIVar) gs sigma"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals gs"
 and ground: "vars_term initial_parameter = {}"
 and allowed: "u\<in>lpp_parameter_subterm_templates marker tag initial_parameter"
 and known: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates marker tag initial_parameter) shape caller"
 and covered: "set2_lp_iterm caller \<subseteq> set2_lp_iterm a \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates marker tag initial_parameter) shape (lp_isubst caller sigma)"
proof -
 have images: "lpp_bounded_images (lpp_parameter_subterm_templates marker tag initial_parameter) sigma (set2_lp_iterm caller)"
  by (rule lpp_subterm_ground_equality_images[OF mgu finite_call finite_rest
    lpp_parameter_subterm_templates_ground[OF ground allowed] allowed _ covered])
   (rule lpp_parameter_subterm_templates_closed[OF allowed])
 show ?thesis by (rule lpp_runtime_leaf_effect_substitute[OF known images])
  (rule lpp_parameter_subterm_templates_ground[OF ground])
qed

ML \<open>
val checked = @{thms lpp_parameter_subterm_equality_leaf lpp_subterm_ground_equality_images};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted subterm ground equality" else ();
\<close>
end
