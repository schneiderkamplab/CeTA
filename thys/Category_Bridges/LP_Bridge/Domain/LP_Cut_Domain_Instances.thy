theory LP_Cut_Domain_Instances
  imports LP_Cut_Domain_Source Category_Properties.LP_Domain_Properties
begin

lemma cut_finite_substitute:
  assumes "cut_finite_runtime t" "\<And>x. cut_finite_runtime (sigma x)"
  shows "cut_finite_runtime (lp_isubst t sigma)"
proof -
  obtain u where t: "t = lp_ieval u LPIVar"
    using assms(1) by (auto simp: cut_finite_runtime_def)
  have "cut_finite_runtime (lp_ieval u sigma)"
    by (rule cut_domain_eval[OF assms(2) cut_finite_function])
  then show ?thesis by (simp add: t lp_ieval_subst)
qed

lemma cut_finite_arguments:
  assumes "cut_finite_runtime (LPIFun f ts)"
  shows "list_all cut_finite_runtime ts"
proof -
  obtain u where "LPIFun f ts = lp_ieval u LPIVar"
    using assms by (auto simp: cut_finite_runtime_def)
  then show ?thesis by (cases u) (auto simp: list_all_iff cut_finite_runtime_def)
qed

lemma cut_native_subst_back:
  "cut_tree_back (lp_isubst t sigma) =
    logic_subst (cut_tree_back \<circ> sigma) (cut_tree_back t)"
  by (rule cut_tree_injective[THEN iffD1]) (simp add: cut_tree_subst o_def)

lemma cut_rational_substitute:
  "cut_rational_runtime t \<Longrightarrow> (\<And>x. cut_rational_runtime (sigma x)) \<Longrightarrow>
    cut_rational_runtime (lp_isubst t sigma)"
  unfolding cut_rational_runtime_def cut_native_subst_back
  by (rule logic_rational_substitution) (auto simp: o_def)

lemma cut_rational_arguments:
  "cut_rational_runtime (LPIFun f ts) \<Longrightarrow> list_all cut_rational_runtime ts"
  unfolding cut_rational_runtime_def
  using logic_rational_arguments[of "cut_symbol_back f" "map cut_tree_back ts"]
  by (simp add: list_all_iff)

interpretation finite_cut: cut_runtime_domain cut_finite_runtime
  by unfold_locales (auto intro: cut_finite_variable cut_finite_function cut_finite_substitute cut_finite_arguments)
interpretation rational_cut: cut_runtime_domain cut_rational_runtime
  by unfold_locales (auto intro: cut_rational_variable cut_rational_function cut_rational_substitute cut_rational_arguments)

end
