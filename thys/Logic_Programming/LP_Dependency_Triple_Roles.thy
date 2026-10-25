theory LP_Dependency_Triple_Roles
  imports LP_Dependency_Triple_Models LP_Residual_Roles
begin

definition lp_roles_triples where
  "lp_roles_triples p d D = map (\<lambda>(h,ps,b).
    (lp_roles_atom p d h,map (lp_roles_atom p d) ps,lp_roles_atom p d b)) D"

lemma lp_roles_answer_model:
  assumes "lp_answer_model P a"
  shows "lp_answer_model (lp_roles_program p d P) (lp_roles_iatom p d a)"
  using assms
proof (induct rule: lp_answer_model.induct)
  case (clause c nu)
  have index: "c<length (lp_roles_program p d P)"
    using clause.hyps(1) by (simp add: lp_roles_program_def)
  have body: "lp_answer_model (lp_roles_program p d P)
    (lp_atom_eval b (\<lambda>x. map_lp_iterm d id (nu x)))"
    if "b\<in>set (snd (lp_roles_program p d P!c))" for b
    using that clause.hyps
    by (auto simp: lp_roles_program_def case_prod_beta lp_roles_eval)
  have result_model: "lp_answer_model (lp_roles_program p d P)
    (lp_atom_eval (fst (lp_roles_program p d P!c)) (\<lambda>x. map_lp_iterm d id (nu x)))"
    by (rule lp_answer_model.clause[OF index body])
  show ?case using result_model clause.hyps(1)
    by (simp add: lp_roles_program_def case_prod_beta lp_roles_eval)
qed

lemma lp_roles_triple_call:
  assumes edge: "(a,b)\<in>lp_triple_calls (set D) P"
  shows "(lp_roles_iatom p d a,lp_roles_iatom p d b)
    \<in>lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P)"
proof -
  obtain h ps call sigma rho eta where triple: "(h,ps,call)\<in>set D"
    and matching: "lp_iatom_subst a sigma=lp_atom_eval h rho"
    and prefix: "((map (\<lambda>g. lp_atom_eval g rho) ps,rho),([],eta))\<in>(lp_seg_answer_step P)\<^sup>*"
    and b: "b=lp_atom_eval call eta"
    using edge by (auto simp: lp_triple_calls_def)
  obtain delta where eta: "eta=(\<lambda>x. lp_isubst (rho x) delta)"
    and models: "\<forall>g\<in>set (map (\<lambda>g. lp_atom_eval g rho) ps).
      lp_answer_model P (lp_iatom_subst g delta)"
    using lp_answer_steps_model[OF prefix] by blast
  have source_models: "lp_answer_model P (lp_atom_eval g eta)" if "g\<in>set ps" for g
    using models that by (auto simp: eta lp_atom_eval_def lp_iatom_subst_def lp_ieval_subst map_map o_def)
  have head: "lp_iatom_subst a (\<lambda>x. lp_isubst (sigma x) delta)=lp_atom_eval h eta"
    using arg_cong[OF matching, of "\<lambda>g. lp_iatom_subst g delta"]
    by (simp add: eta lp_atom_eval_def lp_iatom_subst_def lp_ieval_subst lp_seg_isubst_comp map_map o_def)
  have target_triple: "(lp_roles_atom p d h,map (lp_roles_atom p d) ps,lp_roles_atom p d call)
    \<in>set (lp_roles_triples p d D)"
    unfolding lp_roles_triples_def set_map
    by (rule image_eqI[where x="(h,ps,call)"]) (use triple in auto)
  have target_match: "lp_iatom_subst (lp_roles_iatom p d a)
      (\<lambda>x. map_lp_iterm d id (lp_isubst (sigma x) delta)) =
      lp_atom_eval (lp_roles_atom p d h) (\<lambda>x. map_lp_iterm d id (eta x))"
    using arg_cong[OF head, of "lp_roles_iatom p d"]
    by (simp only: lp_roles_subst lp_roles_eval)
  have target_edge: "(lp_roles_iatom p d a,
      lp_atom_eval (lp_roles_atom p d call) (\<lambda>x. map_lp_iterm d id (eta x)))
    \<in>lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P)"
  proof (rule lp_triple_calls_modelI[OF target_triple target_match])
    fix g assume "g\<in>set (map (lp_roles_atom p d) ps)"
    then obtain source where member: "source\<in>set ps" and g: "g=lp_roles_atom p d source" by auto
    show "lp_answer_model (lp_roles_program p d P)
      (lp_atom_eval g (\<lambda>x. map_lp_iterm d id (eta x)))"
      using lp_roles_answer_model[OF source_models[OF member], of p d]
      by (simp only: g lp_roles_eval)
  qed
  show ?thesis using target_edge by (simp only: b lp_roles_eval)
qed

theorem lp_roles_triple_termination_reflect:
  assumes sn: "SN_on (lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P))
    {lp_roles_iatom p d a}"
  shows "SN_on (lp_triple_calls (set D) P) {a}"
proof -
  have all: "\<forall>u. lp_roles_iatom p d u=lp_roles_iatom p d a \<longrightarrow>
    SN_on (lp_triple_calls (set D) P) {u}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix x
    assume ih: "\<And>y. (x,y)\<in>lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P)
      \<Longrightarrow> \<forall>u. lp_roles_iatom p d u=y \<longrightarrow> SN_on (lp_triple_calls (set D) P) {u}"
    show "\<forall>u. lp_roles_iatom p d u=x \<longrightarrow> SN_on (lp_triple_calls (set D) P) {u}"
    proof (intro allI impI)
      fix u assume equal: "lp_roles_iatom p d u=x"
      show "SN_on (lp_triple_calls (set D) P) {u}"
      proof (rule step_reflects_SN_on)
        fix v assume edge: "(u,v)\<in>lp_triple_calls (set D) P"
        have target: "(x,lp_roles_iatom p d v)\<in>lp_triple_calls (set (lp_roles_triples p d D)) (lp_roles_program p d P)"
          using lp_roles_triple_call[OF edge, of p d] by (simp only: equal)
        show "SN_on (lp_triple_calls (set D) P) {v}" using ih[OF target] by blast
      qed
    qed
  qed
  show ?thesis using all by blast
qed

end
