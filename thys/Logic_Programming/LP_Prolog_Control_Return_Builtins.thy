theory LP_Prolog_Control_Return_Builtins
 imports LP_Prolog_Control_Actual_Return LP_Prolog_Open_Return_Builtins
begin

lemma lpp_control_finite_call_shape:
  assumes "lpp_finite_source_builtin f ts (LPPBuiltinCall a)"
  shows "f=''3:subtract'' \<and> length ts=3 \<and>
    a=LPIFun (LPCUser lpp_subtract_library) ts"
  using assms by (auto simp: lpp_finite_source_builtin_def
    lpp_probe_outcome_def lpp_finite_is_outcome_def lpp_integer_is_outcome_def lpp_rational_disequality_outcome_def
    lpp_finite_length_outcome_def lpp_branch_outcome_def lpp_is_list_outcome_def lpp_integer_source_no_call
    simp del: lpp_integer_source_builtin.simps split: if_splits option.splits)

lemma lpp_control_finite_branch_shape:
  assumes "lpp_finite_source_builtin f ts (LPPBuiltinBranch cs ys ns)"
  shows "f=''2:;'' \<and> (\<exists>c y n.
    ts=[LPIFun (LPCUser ''2:->'') [c,y],n] \<and>
    lpp_branch_lower c cs \<and> lpp_branch_lower y ys \<and> lpp_branch_lower n ns)"
  using assms by (auto simp: lpp_finite_source_builtin_def
    lpp_probe_outcome_def lpp_finite_is_outcome_def lpp_integer_is_outcome_def lpp_rational_disequality_outcome_def
    lpp_finite_length_outcome_def lpp_branch_outcome_def lpp_is_list_outcome_def lpp_integer_source_no_branch
    simp del: lpp_integer_source_builtin.simps split: if_splits option.splits)

lemma lpp_control_finite_choice_shape:
  assumes "lpp_finite_source_builtin f ts (LPPBuiltinChoice left right)"
  shows "f=''2:;'' \<and> (\<exists>a b. ts=[a,b] \<and> lpp_choice_left a \<and>
    lpp_branch_lower a left \<and> lpp_branch_lower b right)"
  using assms by (auto simp: lpp_finite_source_builtin_def
    lpp_probe_outcome_def lpp_finite_is_outcome_def lpp_integer_is_outcome_def lpp_rational_disequality_outcome_def
    lpp_finite_length_outcome_def lpp_branch_outcome_def lpp_is_list_outcome_def lpp_integer_source_no_choice
    simp del: lpp_integer_source_builtin.simps split: if_splits option.splits)

lemma lpp_control_stable_choice_model:
  assumes outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinChoice left right)"
    and model: "list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) left) \<or>
      list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) right)"
  shows "lpp_control_return_model M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  obtain a b where shape: "f=''2:;''" "ts=[a,b]" and choice: "lpp_choice_left a"
    and lower: "lpp_branch_lower a left" "lpp_branch_lower b right"
    using lpp_control_finite_choice_shape[OF lpp_stable_source_refines_finite[OF outcome]] by blast
  show ?thesis unfolding shape lp_isubst_Fun list.map
    by (rule lpp_control_return_model.choice[OF lpp_choice_left_subst[OF choice]
      lpp_branch_lower_subst[OF lower(1)] lpp_branch_lower_subst[OF lower(2)] model])
qed

lemma lpp_control_stable_call_model:
  assumes outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinCall a)"
    and model: "lpp_control_return_model M (lp_isubst a sigma)"
  shows "lpp_control_return_model M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  have shape: "f=''3:subtract''" "length ts=3"
    "a=LPIFun (LPCUser lpp_subtract_library) ts"
    using lpp_control_finite_call_shape[OF lpp_stable_source_refines_finite[OF outcome]] by auto
  show ?thesis unfolding shape(1) lp_isubst_Fun
    by (rule lpp_control_return_model.subtract_call)
      (use shape model in simp_all)
qed

lemma lpp_control_stable_branch_model:
  assumes outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinBranch cs ys ns)"
    and model: "list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
      list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)"
  shows "lpp_control_return_model M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  obtain c y n where shape: "f=''2:;''" "ts=[LPIFun (LPCUser ''2:->'') [c,y],n]"
    and lower: "lpp_branch_lower c cs" "lpp_branch_lower y ys" "lpp_branch_lower n ns"
    using lpp_control_finite_branch_shape[OF lpp_stable_source_refines_finite[OF outcome]] by blast
  have lowers:
    "lpp_branch_lower (lp_isubst c sigma) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) cs)"
    "lpp_branch_lower (lp_isubst y sigma) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ys)"
    "lpp_branch_lower (lp_isubst n sigma) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)"
    using lower by (auto intro: lpp_branch_lower_subst)
  show ?thesis using model
    unfolding shape lp_isubst_Fun list.map map_append
    by (auto intro: lpp_control_return_model.conditional_yes[OF lowers]
      lpp_control_return_model.conditional_no[OF lowers])
qed


lemma lpp_control_stable_success_model:
  assumes checked: "lpp_open_builtin_check F SP"
    and outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinSuccess sigma)"
  shows "lpp_control_return_model
    (lpp_open_return_model F (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))
      (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  have ordinary: "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    using lpp_stable_source_refines_finite[OF outcome]
    by (auto simp: lpp_finite_source_builtin_def lpp_branch_outcome_def lpp_disequality_predicate_def)
  have base: "lpp_open_return_model F (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))
      (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    using lpp_open_stable_builtin_model[where sigma=sigma, OF checked _ outcome]
    by (cases "f\<in>F") (simp_all only: lp_isubst_Fun lpp_open_return_model.simps if_True if_False)
  show ?thesis unfolding lp_isubst_Fun
    by (rule lpp_control_return_model.ordinary[OF ordinary]) (use base in simp)
qed

lemma lpp_control_stable_probe_model:
  assumes checked: "lpp_open_builtin_check F SP"
    and outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinProbe a keep)"
  shows "lpp_control_return_model
    (lpp_open_return_model F (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))
      (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  have ordinary: "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    using lpp_stable_source_refines_finite[OF outcome]
    by (auto simp: lpp_finite_source_builtin_def lpp_branch_outcome_def lpp_disequality_predicate_def)
  have base: "lpp_open_return_model F (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))
      (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    using lpp_open_stable_probe_model[where sigma=sigma, OF checked _ outcome]
    by (cases "f\<in>F") (simp_all only: lp_isubst_Fun lpp_open_return_model.simps if_True if_False)
  show ?thesis unfolding lp_isubst_Fun
    by (rule lpp_control_return_model.ordinary[OF ordinary]) (use base in simp)
qed

ML \<open>
val checked = [@{thm lpp_control_stable_call_model},@{thm lpp_control_stable_branch_model},
  @{thm lpp_control_stable_success_model},@{thm lpp_control_stable_probe_model}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted control builtin model" else ();
\<close>
end
