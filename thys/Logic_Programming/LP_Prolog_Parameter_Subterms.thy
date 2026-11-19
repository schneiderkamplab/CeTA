theory LP_Prolog_Parameter_Subterms
 imports LP_Prolog_Parameter_Return_Composition
begin

text \<open>Close the restricted parameter replacements under finite subterms.
The existing budget is unchanged; actual unifier-image coverage remains a
separate obligation, especially for shared nonground caller outputs.\<close>

inductive lpp_finite_template_subterm where
 root: "lpp_finite_template_subterm t t"
| child: "v\<in>set ts \<Longrightarrow> lpp_finite_template_subterm u v \<Longrightarrow>
    lpp_finite_template_subterm u (Fun f ts)"

definition lpp_parameter_subterm_templates where
 "lpp_parameter_subterm_templates f g c =
   {u. \<exists>t\<in>lpp_parameter_leaf_templates f g c. lpp_finite_template_subterm u t}"

lemma lpp_finite_template_subterm_trans:
 assumes outer: "lpp_finite_template_subterm v t"
 and inner: "lpp_finite_template_subterm u v"
 shows "lpp_finite_template_subterm u t"
 using outer inner
 by (induct arbitrary: u rule: lpp_finite_template_subterm.induct)
    (auto intro: lpp_finite_template_subterm.intros)

lemma lpp_finite_template_subterm_ground:
 assumes sub: "lpp_finite_template_subterm u t" and ground: "vars_term t={}"
 shows "vars_term u={}"
 using sub ground
 by (induct rule: lpp_finite_template_subterm.induct) auto

lemma lpp_list_member_budget:
 fixes weight :: "'a\<Rightarrow>nat"
 assumes "x\<in>set xs"
 shows "weight x \<le> sum_list (map weight xs)"
 using assms by (induct xs) auto

lemma lpp_finite_template_subterm_budget:
 assumes sub: "lpp_finite_template_subterm u t"
 shows "lpp_leaf_budget k (lpp_structure_template u) \<le> lpp_leaf_budget k (lpp_structure_template t)"
 using sub
proof (induct rule: lpp_finite_template_subterm.induct)
 case (root t) then show ?case by simp
next
 case (child v ts u f)
 have member: "lpp_leaf_budget k (lpp_structure_template v) \<le>
   sum_list (map (\<lambda>t. lpp_leaf_budget k (lpp_structure_template t)) ts)"
  by (rule lpp_list_member_budget[OF child.hyps(1)])
 show ?case using child member by (simp add: o_def; arith)
qed

lemma lpp_parameter_subterm_templates_include:
 "lpp_parameter_leaf_templates f g c \<subseteq> lpp_parameter_subterm_templates f g c"
 by (auto simp: lpp_parameter_subterm_templates_def intro: lpp_finite_template_subterm.root)

lemma lpp_parameter_subterm_templates_closed:
 "t\<in>lpp_parameter_subterm_templates f g c \<Longrightarrow>
   lpp_finite_template_subterm u t \<Longrightarrow> u\<in>lpp_parameter_subterm_templates f g c"
 unfolding lpp_parameter_subterm_templates_def
 using lpp_finite_template_subterm_trans by blast

lemma lpp_parameter_subterm_templates_ground:
 assumes ground: "vars_term c={}" and member: "u\<in>lpp_parameter_subterm_templates f g c"
 shows "vars_term u={}"
proof -
 obtain t where original: "t\<in>lpp_parameter_leaf_templates f g c"
 and sub: "lpp_finite_template_subterm u t"
  using member by (auto simp: lpp_parameter_subterm_templates_def)
 show ?thesis by (rule lpp_finite_template_subterm_ground[OF sub lpp_parameter_leaf_templates_ground[OF ground original]])
qed

lemma lpp_parameter_subterm_templates_budget:
 assumes ground: "vars_term c={}" and member: "u\<in>lpp_parameter_subterm_templates f g c"
 shows "lpp_leaf_budget (lpp_parameter_leaf_budget c) (lpp_structure_template u) \<le> lpp_parameter_leaf_budget c"
proof -
 obtain t where original: "t\<in>lpp_parameter_leaf_templates f g c"
 and sub: "lpp_finite_template_subterm u t"
  using member by (auto simp: lpp_parameter_subterm_templates_def)
 show ?thesis by (rule order_trans[OF lpp_finite_template_subterm_budget[OF sub]
   lpp_parameter_leaf_templates_budget[OF ground original]])
qed

lemma lpp_parameter_return_subterm_templates:
 "lpp_parameter_return c d \<Longrightarrow>
   lpp_parameter_subterm_templates f g d \<subseteq> lpp_parameter_subterm_templates f g c"
 unfolding lpp_parameter_subterm_templates_def
 using lpp_parameter_return_templates[of c d f g] by blast

lemma lpp_parameter_subterm_leaf_composition:
 assumes first: "lpp_leaf_effect (lpp_parameter_subterm_templates f g c) s t"
 and returned: "lpp_parameter_return c d"
 and second: "lpp_leaf_effect (lpp_parameter_subterm_templates f g d) t u"
 and ground: "vars_term c={}"
 shows "lpp_leaf_effect (lpp_parameter_subterm_templates f g c) s u"
proof -
 have widened: "lpp_leaf_effect (lpp_parameter_subterm_templates f g c) t u"
  by (rule lpp_leaf_effect_replacements_mono[OF second lpp_parameter_return_subterm_templates[OF returned]])
 show ?thesis by (rule lpp_leaf_effect_transitive[OF first widened])
   (rule lpp_parameter_subterm_templates_ground[OF ground])
qed

ML \<open>
val checked = @{thms lpp_parameter_subterm_templates_closed lpp_parameter_subterm_templates_ground
 lpp_parameter_subterm_templates_budget lpp_parameter_return_subterm_templates lpp_parameter_subterm_leaf_composition};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted subterm replacement bounds" else ();
val _ = writeln "PARAMETER_SUBTERM_BOUNDS_KERNEL_CHECKED";
\<close>
end
