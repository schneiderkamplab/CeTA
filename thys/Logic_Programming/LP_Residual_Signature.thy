theory LP_Residual_Signature
  imports LP_Constructor_Source
begin

text \<open>Transport a residual LP obligation to the checker's concrete symbol
signature. Predicate and data symbols are mapped explicitly; no clauses or
argument positions are erased. Forward simulation suffices for termination
reflection, even if the mapping identifies symbols.\<close>

definition lp_signature_atom where
  "lp_signature_atom f a = (f (fst a), map (map_term f id) (snd a))"

definition lp_signature_iatom where
  "lp_signature_iatom f a = (f (fst a), map (map_lp_iterm f id) (snd a))"

definition lp_signature_program where
  "lp_signature_program f P = map (\<lambda>(h,bs).
    (lp_signature_atom f h,map (lp_signature_atom f) bs)) P"

lemma lp_signature_eval:
  "map_lp_iterm f id (lp_ieval t \<rho>) =
    lp_ieval (map_term f id t) (\<lambda>x. map_lp_iterm f id (\<rho> x))"
  by (induct t) auto

lemma lp_signature_atom_eval:
  "lp_signature_iatom f (lp_atom_eval a \<rho>) =
    lp_atom_eval (lp_signature_atom f a) (\<lambda>x. map_lp_iterm f id (\<rho> x))"
  by (simp add: lp_signature_iatom_def lp_signature_atom_def lp_atom_eval_def
    map_map o_def lp_signature_eval)

lemma lp_signature_atom_subst:
  "lp_signature_iatom f (lp_iatom_subst a \<sigma>) =
    lp_iatom_subst (lp_signature_iatom f a) (\<lambda>x. map_lp_iterm f id (\<sigma> x))"
  by (simp add: lp_signature_iatom_def lp_iatom_subst_def map_map o_def lp_data_map_subst)

lemma lp_signature_step:
  assumes "(s,t) \<in> lp_ild P"
  shows "(map (lp_signature_iatom f) s,map (lp_signature_iatom f) t)
    \<in> lp_ild (lp_signature_program f P)"
  using assms
proof (induct rule: lp_ild.induct)
  case (resolve c a \<sigma> \<rho> gs)
  have c: "c < length (lp_signature_program f P)"
    using resolve.hyps(1) by (simp add: lp_signature_program_def)
  have head: "lp_iatom_subst (lp_signature_iatom f a)
      (\<lambda>x. map_lp_iterm f id (\<sigma> x)) =
    lp_atom_eval (fst (lp_signature_program f P ! c))
      (\<lambda>x. map_lp_iterm f id (\<rho> x))"
    using arg_cong[OF resolve.hyps(2), of "lp_signature_iatom f"] resolve.hyps(1)
    by (simp add: lp_signature_program_def case_prod_beta lp_signature_atom_subst lp_signature_atom_eval)
  show ?case
    using lp_ild.resolve[OF c head, of "map (lp_signature_iatom f) gs"] resolve.hyps(1)
    by (simp add: lp_signature_program_def case_prod_beta map_map o_def
      lp_signature_atom_eval lp_signature_atom_subst)
qed

theorem lp_signature_termination_reflect:
  assumes "SN_on (lp_ild (lp_signature_program f P)) {map (lp_signature_iatom f) s}"
  shows "SN_on (lp_ild P) {s}"
proof -
  have all: "\<forall>u. map (lp_signature_iatom f) u=map (lp_signature_iatom f) s
      \<longrightarrow> SN_on (lp_ild P) {u}"
  proof (rule SN_on_induct[OF assms singletonI])
    fix xs
    assume ih: "\<And>ys. (xs,ys) \<in> lp_ild (lp_signature_program f P) \<Longrightarrow>
      \<forall>u. map (lp_signature_iatom f) u=ys \<longrightarrow> SN_on (lp_ild P) {u}"
    show "\<forall>u. map (lp_signature_iatom f) u=xs \<longrightarrow> SN_on (lp_ild P) {u}"
    proof (intro allI impI)
      fix u assume eq: "map (lp_signature_iatom f) u=xs"
      show "SN_on (lp_ild P) {u}"
      proof (rule step_reflects_SN_on)
        fix v assume step: "(u,v) \<in> lp_ild P"
        have "(xs,map (lp_signature_iatom f) v) \<in> lp_ild (lp_signature_program f P)"
          using lp_signature_step[OF step, of f] eq by simp
        then show "SN_on (lp_ild P) {v}" using ih by blast
      qed
    qed
  qed
  show ?thesis using all by blast
qed

end
