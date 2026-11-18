theory LP_Prolog_Structural_Projection
 imports LP_Prolog_Structural_Observation LP_Prolog_Finite_List_Head
begin

text \<open>The residual expression preserves source constructors and uses a
separate environment of finite structural observations for its variables. It is
not evaluated in the runtime environment, and does not assert runtime equality
between pre-resolution and refreshed variables.\<close>

lemma lpp_runtime_structure_unique:
 assumes "lpp_runtime_structure t s" "lpp_runtime_structure t u"
 shows "s=u"
 using assms lp_seg_ieval_injective unfolding lpp_runtime_structure_def by blast

lemma lpp_structure_template_substitution:
 "lpp_structure_template (t \<cdot> template_subst) =
   map_term Inl id t \<cdot> (lpp_structure_template \<circ> template_subst)"
 by (induct t) (auto simp: map_map o_def intro!: map_cong)

lemma lpp_structural_projection_eval:
 fixes rho :: "'v \<Rightarrow> ('f,'w) lp_iterm"
 assumes observed: "\<And>x. x\<in>vars_term t \<Longrightarrow> lpp_runtime_structure (rho x) (eta x)"
 shows "lpp_runtime_structure (lp_ieval t rho) (map_term Inl id t \<cdot> eta)"
proof -
 define templates :: "'v \<Rightarrow> ('f,'w) term" where
  "templates x = (SOME s. rho x=lp_ieval s LPIVar \<and> eta x=lpp_structure_template s)" for x
 have chosen: "rho x=lp_ieval (templates x) LPIVar \<and> eta x=lpp_structure_template (templates x)"
  if "x\<in>vars_term t" for x
  unfolding templates_def by (rule someI_ex) (use observed[OF that] in \<open>simp add: lpp_runtime_structure_def\<close>)
 have runtime: "lp_ieval t rho=lp_ieval (t \<cdot> templates) LPIVar"
  unfolding lp_ieval_finite_subst
  using chosen by (induct t) (auto intro!: map_cong)
 have shape: "map_term Inl id t \<cdot> eta = lpp_structure_template (t \<cdot> templates)"
  unfolding lpp_structure_template_substitution
  using chosen by (induct t) (auto simp: o_def intro!: map_cong)
 show ?thesis unfolding lpp_runtime_structure_def
  by (rule exI[of _ "t \<cdot> templates"]) (simp add: runtime shape)
qed

theorem lpp_checked_matching_structural_equation:
 assumes checked: "lp_cut_check_match call head bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval call rho) gs head bs sigma rho_next"
 and source_observed: "\<And>x. x\<in>vars_term call \<Longrightarrow> lpp_runtime_structure (rho x) (eta x)"
 and target_observed: "\<And>x. x\<in>vars_term head \<Longrightarrow> lpp_runtime_structure (rho_next x) (eta_next x)"
 shows "map_term Inl id call \<cdot> eta = map_term Inl id head \<cdot> eta_next"
proof -
 have source: "lpp_runtime_structure (lp_ieval call rho) (map_term Inl id call \<cdot> eta)"
  by (rule lpp_structural_projection_eval[OF source_observed])
 have target: "lpp_runtime_structure (lp_ieval head rho_next) (map_term Inl id head \<cdot> eta_next)"
  by (rule lpp_structural_projection_eval[OF target_observed])
 have finite: "lpp_finite_term (lp_ieval call rho)"
  by (rule lpp_runtime_structure_finite[OF source])
 have matching: "lp_ieval head (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) rho)=lp_ieval call rho"
  using checked unfolding lp_cut_check_match_def
  by (simp add: lp_ieval_finite_subst[symmetric])
 obtain shared where old: "lpp_runtime_structure (lp_ieval call rho) shared"
 and new: "lpp_runtime_structure (lp_ieval head rho_next) shared"
  using lpp_matching_head_structural_observation[OF mgu matching finite] by blast
 show ?thesis using lpp_runtime_structure_unique[OF source old]
  lpp_runtime_structure_unique[OF target new] by simp
qed

theorem lpp_list_head_structural_equation:
 assumes spine: "lpp_list_length arg n"
 and mgu: "lpc_mgu_resolve (LPIFun f (arg#actuals)) gs
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) bs sigma rho"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and source_observed: "lpp_runtime_structure (LPIFun f (arg#actuals)) initial_structure"
 and target_observed: "\<And>v. v\<in>set (x#y#H) \<Longrightarrow> lpp_runtime_structure (rho v) (eta v)"
 shows "initial_structure = map_term Inl id
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) \<cdot> eta"
proof -
 let ?head = "Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)"
 obtain a b where shape: "arg=LPIFun (LPCUser ''2:prolog_data_2e'') [a,b]"
  using lpp_list_head_success_shape[OF spine mgu] by blast
 let ?nu = "lpp_partial_arguments (x#y#H) (a#b#actuals)"
 have exact: "map ?nu (x#y#H)=a#b#actuals"
  by (rule lpp_partial_arguments_exact[OF _ distinct]) (simp add: lengths)
 have matching: "lp_ieval ?head ?nu=LPIFun f (arg#actuals)"
  using exact by (simp add: shape map_map o_def)
 have finite: "lpp_finite_term (LPIFun f (arg#actuals))"
  by (rule lpp_runtime_structure_finite[OF source_observed])
 obtain shared where old: "lpp_runtime_structure (LPIFun f (arg#actuals)) shared"
 and new: "lpp_runtime_structure (lp_ieval ?head rho) shared"
  using lpp_matching_head_structural_observation[OF mgu matching finite] by blast
 have projected: "lpp_runtime_structure (lp_ieval ?head rho) (map_term Inl id ?head \<cdot> eta)"
  by (rule lpp_structural_projection_eval) (auto intro: target_observed)
 show ?thesis using lpp_runtime_structure_unique[OF source_observed old]
  lpp_runtime_structure_unique[OF projected new] by simp
qed

text \<open>Arbitrary successful substitution is not shape preservation: even a
finite variable can become a constructor. The matching premise cannot be
silently dropped, nor can helper returns reuse their input observations.\<close>
lemma lpp_structural_instantiation_changes_leaf:
 "lpp_structure_template (Var x) \<noteq> lpp_structure_template (Fun f ts)"
 by simp

ML \<open>
val checked = @{thms lpp_runtime_structure_unique lpp_structure_template_substitution
 lpp_structural_projection_eval lpp_checked_matching_structural_equation
 lpp_list_head_structural_equation lpp_structural_instantiation_changes_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural projection" else ();
\<close>
end
