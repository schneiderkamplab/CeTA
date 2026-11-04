theory LP_Equation_Congruence
 imports LP_Ground_Equations
begin

fun lp_equation_replace where
  "lp_equation_replace s t (Var x) = (if Var x=s then t else Var x)"
| "lp_equation_replace s t (Fun f xs) =
    (if Fun f xs=s then t else Fun f (map (lp_equation_replace s t) xs))"

lemma lp_equation_replace_eval:
  assumes "lp_ieval s eta=lp_ieval t eta"
  shows "lp_ieval (lp_equation_replace s t a) eta=lp_ieval a eta"
  using assms by (induction a) (auto simp: map_map intro!: map_cong)

definition lp_check_equation_congruence where
  "lp_check_equation_congruence equations a b =
    (a=b \<or> (\<exists>(s,t)\<in>set equations.
      lp_equation_replace s t a=b \<or> lp_equation_replace t s a=b))"

lemma lp_check_equation_congruence_sound:
  assumes checked: "lp_check_equation_congruence equations a b"
    and equations: "\<forall>(s,t)\<in>set equations. lp_ieval s eta=lp_ieval t eta"
  shows "lp_ieval a eta=lp_ieval b eta"
proof (cases "a=b")
  case True then show ?thesis by simp
next
  case False
  obtain s t where member: "(s,t)\<in>set equations"
    and replacement: "lp_equation_replace s t a=b \<or> lp_equation_replace t s a=b"
    using checked False by (auto simp: lp_check_equation_congruence_def)
  have eq: "lp_ieval s eta=lp_ieval t eta" using equations member by auto
  have forward: "lp_ieval (lp_equation_replace s t a) eta=lp_ieval a eta"
    by (rule lp_equation_replace_eval[OF eq])
  have backward: "lp_ieval (lp_equation_replace t s a) eta=lp_ieval a eta"
    by (rule lp_equation_replace_eval[OF eq[symmetric]])
  show ?thesis using replacement forward backward by auto
qed

lemma lp_equation_congruence_requires_initialization:
  "a\<noteq>b \<Longrightarrow> \<not>lp_check_equation_congruence [] a b"
  by (simp add: lp_check_equation_congruence_def)

end
