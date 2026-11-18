theory LP_Prolog_Parameter_Leaf_Budget
 imports LP_Prolog_Bounded_Unify
begin

text \<open>A helper may initially copy an arbitrary finite ground parameter,
then use atomic evaluated results. A uniform replacement bound can depend on
that initial parameter. It must not assume the parameter itself is atomic.\<close>

lemma lpp_ground_leaf_budget_independent:
 assumes ground_template: "vars_term t={}"
 shows "lpp_leaf_budget k (lpp_structure_template t)=lpp_leaf_budget j (lpp_structure_template t)"
 using ground_template
 by (induct t) (auto intro!: arg_cong[where f=sum_list] map_cong)

definition lpp_parameter_leaf_templates where
 "lpp_parameter_leaf_templates f g c =
   {Fun f [Fun g [],c]} \<union> {Fun f [Fun g [],Fun h []] |h. True}"

definition lpp_parameter_leaf_budget where
 "lpp_parameter_leaf_budget c = max (2+lpp_leaf_budget 0 (lpp_structure_template c)) 3"

lemma lpp_parameter_leaf_templates_ground:
 assumes ground_parameter: "vars_term c={}"
 and member: "u\<in>lpp_parameter_leaf_templates f g c"
 shows "vars_term u={}"
 using assms by (auto simp: lpp_parameter_leaf_templates_def)

lemma lpp_parameter_leaf_templates_budget:
 assumes ground_parameter: "vars_term c={}"
 and member: "u\<in>lpp_parameter_leaf_templates f g c"
 shows "lpp_leaf_budget (lpp_parameter_leaf_budget c) (lpp_structure_template u)
   \<le> lpp_parameter_leaf_budget c"
proof -
 have fixed: "lpp_leaf_budget (lpp_parameter_leaf_budget c) (lpp_structure_template c)=
   lpp_leaf_budget 0 (lpp_structure_template c)"
  by (rule lpp_ground_leaf_budget_independent[OF ground_parameter])
 have copied: "lpp_leaf_budget (lpp_parameter_leaf_budget c)
   (lpp_structure_template (Fun f [Fun g [],c]))=2+lpp_leaf_budget 0 (lpp_structure_template c)"
  by (simp add: fixed)
 have limit: "2+lpp_leaf_budget 0 (lpp_structure_template c) \<le> lpp_parameter_leaf_budget c"
  by (simp add: lpp_parameter_leaf_budget_def)
 have atomic: "3 \<le> lpp_parameter_leaf_budget c"
  by (simp add: lpp_parameter_leaf_budget_def)
 show ?thesis using member copied limit atomic
  by (auto simp only: lpp_parameter_leaf_templates_def Un_iff singleton_iff mem_Collect_eq
    lpp_binary_atomic_template_budget)
qed

ML \<open>
val checked = @{thms lpp_ground_leaf_budget_independent
 lpp_parameter_leaf_templates_ground lpp_parameter_leaf_templates_budget};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter leaf budget" else ();
\<close>
end
