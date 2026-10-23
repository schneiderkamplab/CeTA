theory LP_Residual_Roles
  imports LP_Residual_Signature
begin

text \<open>Predicates and constructors use distinct encodings in Ferrum's LP
frontend. Both maps remain explicit in the child-program equality check.\<close>

definition lp_roles_atom where
  "lp_roles_atom p d a = (p (fst a),map (map_term d id) (snd a))"
definition lp_roles_iatom where
  "lp_roles_iatom p d a = (p (fst a),map (map_lp_iterm d id) (snd a))"
definition lp_roles_program where
  "lp_roles_program p d P = map (\<lambda>(h,bs). (lp_roles_atom p d h,map (lp_roles_atom p d) bs)) P"

lemma lp_roles_eval:
  "lp_roles_iatom p d (lp_atom_eval a \<rho>) =
    lp_atom_eval (lp_roles_atom p d a) (\<lambda>x. map_lp_iterm d id (\<rho> x))"
  by (simp add: lp_roles_iatom_def lp_roles_atom_def lp_atom_eval_def map_map o_def lp_signature_eval)
lemma lp_roles_subst:
  "lp_roles_iatom p d (lp_iatom_subst a \<sigma>) =
    lp_iatom_subst (lp_roles_iatom p d a) (\<lambda>x. map_lp_iterm d id (\<sigma> x))"
  by (simp add: lp_roles_iatom_def lp_iatom_subst_def map_map o_def lp_data_map_subst)

lemma lp_roles_step:
  assumes "(s,t)\<in>lp_ild P"
  shows "(map (lp_roles_iatom p d) s,map (lp_roles_iatom p d) t)\<in>lp_ild (lp_roles_program p d P)"
  using assms
proof (induct rule: lp_ild.induct)
  case (resolve c a \<sigma> \<rho> gs)
  have c: "c<length (lp_roles_program p d P)"
    using resolve.hyps(1) by (simp add: lp_roles_program_def)
  have head: "lp_iatom_subst (lp_roles_iatom p d a) (\<lambda>x. map_lp_iterm d id (\<sigma> x)) =
    lp_atom_eval (fst (lp_roles_program p d P ! c)) (\<lambda>x. map_lp_iterm d id (\<rho> x))"
    using arg_cong[OF resolve.hyps(2), of "lp_roles_iatom p d"] resolve.hyps(1)
    by (simp add: lp_roles_program_def case_prod_beta lp_roles_subst lp_roles_eval)
  show ?case using lp_ild.resolve[OF c head, of "map (lp_roles_iatom p d) gs"] resolve.hyps(1)
    by (simp add: lp_roles_program_def case_prod_beta map_map o_def lp_roles_eval lp_roles_subst)
qed

theorem lp_roles_termination_reflect:
  assumes "SN_on (lp_ild (lp_roles_program p d P)) {map (lp_roles_iatom p d) s}"
  shows "SN_on (lp_ild P) {s}"
proof -
  have all: "\<forall>u. map (lp_roles_iatom p d) u=map (lp_roles_iatom p d) s \<longrightarrow> SN_on (lp_ild P) {u}"
  proof (rule SN_on_induct[OF assms singletonI])
    fix xs
    assume ih: "\<And>ys. (xs,ys)\<in>lp_ild (lp_roles_program p d P) \<Longrightarrow>
      \<forall>u. map (lp_roles_iatom p d) u=ys \<longrightarrow> SN_on (lp_ild P) {u}"
    show "\<forall>u. map (lp_roles_iatom p d) u=xs \<longrightarrow> SN_on (lp_ild P) {u}"
    proof (intro allI impI)
      fix u assume eq: "map (lp_roles_iatom p d) u=xs"
      show "SN_on (lp_ild P) {u}"
      proof (rule step_reflects_SN_on)
        fix v assume step: "(u,v)\<in>lp_ild P"
        have "(xs,map (lp_roles_iatom p d) v)\<in>lp_ild (lp_roles_program p d P)"
          using lp_roles_step[OF step, of p d] eq by simp
        then show "SN_on (lp_ild P) {v}" using ih by blast
      qed
    qed
  qed
  show ?thesis using all by blast
qed

end
