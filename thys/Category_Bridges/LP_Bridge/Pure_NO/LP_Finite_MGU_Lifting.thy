theory LP_Finite_MGU_Lifting
  imports LP_Universal_MGU_Finite
begin

text \<open>This auxiliary finite relation chooses a unifier that is most general
in every tree domain. A finite all-unifier execution lifts one step at a time to
this relation, retaining a finite inst substitution after each step.\<close>
inductive_set lp_exact_finite_ld :: "('f,string) lp_clause list \<Rightarrow> ('f,string) lp_atom list rel"
  for P where
  resolve: "c<length P \<Longrightarrow> lp_universal_mgu a (fst (P!c)) sigma rho \<Longrightarrow>
    (a#gs,map (\<lambda>b. lp_atom_subst b rho) (snd (P!c)) @
      map (\<lambda>b. lp_atom_subst b sigma) gs)\<in>lp_exact_finite_ld P"

lemma lp_finite_step_lifting:
  fixes sigma :: "string \<Rightarrow> ('f,string) term"
  assumes step: "(map (\<lambda>a. lp_atom_subst a sigma) gs,hs)\<in>lp_ld P"
  obtains us delta where "(gs,us)\<in>lp_exact_finite_ld P"
    "hs=map (\<lambda>a. lp_atom_subst a delta) us"
proof -
  obtain a rest where gs: "gs=a#rest"
    using step by (cases rule: lp_ld.cases) (cases gs; auto)
  obtain c selected tau nu tail where c: "c<length P"
    and selected: "map (\<lambda>a. lp_atom_subst a sigma) gs=selected#tail"
    and native: "lp_atom_subst selected tau=lp_atom_subst (fst (P!c)) nu"
    and target: "hs=map (\<lambda>b. lp_atom_subst b nu) (snd (P!c)) @
      map (\<lambda>b. lp_atom_subst b tau) tail"
    using step
  proof (cases rule: lp_ld.cases)
    case (resolve ci aa ss rr tail0)
    show thesis
      by (rule that[where c=ci and selected=aa and tau=ss and nu=rr and tail=tail0])
        (use resolve in auto)
  qed
  have head: "selected=lp_atom_subst a sigma"
    and tail: "tail=map (\<lambda>b. lp_atom_subst b sigma) rest"
    using selected by (simp_all add: gs)
  have match: "lp_atom_subst a (sigma \<circ>\<^sub>s tau)=lp_atom_subst (fst (P!c)) nu"
    using native by (simp add: head eval_subst_def)
  have hs: "hs=map (\<lambda>b. lp_atom_subst b nu) (snd (P!c)) @
      map (\<lambda>b. lp_atom_subst b (sigma \<circ>\<^sub>s tau)) rest"
    using target by (simp add: tail map_map o_def eval_subst_def)
  obtain mu rho where mgu: "lp_universal_mgu a (fst (P!c)) mu rho"
    by (rule lp_universal_mgu_exists[OF match]) blast
  obtain delta where sf: "\<And>x. mu x\<cdot>delta=(sigma \<circ>\<^sub>s tau) x"
    and rf: "\<And>x. rho x\<cdot>delta=nu x"
    by (rule lp_universal_mgu_finite_factor[OF mgu match]) blast
  let ?us = "map (\<lambda>b. lp_atom_subst b rho) (snd (P!c)) @ map (\<lambda>b. lp_atom_subst b mu) rest"
  have exact: "(gs,?us)\<in>lp_exact_finite_ld P"
    unfolding gs by (rule lp_exact_finite_ld.resolve[OF c mgu])
  have compositions: "mu \<circ>\<^sub>s delta=sigma \<circ>\<^sub>s tau" "rho \<circ>\<^sub>s delta=nu"
    by (auto simp: fun_eq_iff subst_compose sf rf)
  have inst: "hs=map (\<lambda>b. lp_atom_subst b delta) ?us"
    by (simp add: hs map_map o_def eval_subst_def compositions[unfolded eval_subst_def])
  show thesis by (rule that[OF exact inst])
qed

lemma lp_exact_finite_termination_covers_instances:
  fixes sigma :: "string \<Rightarrow> ('f,string) term"
  assumes sn: "SN_on (lp_exact_finite_ld P) {gs}"
  shows "SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) gs}"
proof -
  have all: "\<forall>sigma. SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) us}"
    if sn: "SN_on (lp_exact_finite_ld P) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro allI)
    fix vs sigma
    assume lower: "\<And>ws. (vs,ws)\<in>lp_exact_finite_ld P \<Longrightarrow>
      \<forall>sigma. SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) ws}"
    show "SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) vs}"
    proof (rule step_reflects_SN_on)
      fix hs assume step: "(map (\<lambda>a. lp_atom_subst a sigma) vs,hs)\<in>lp_ld P"
      obtain ws delta where exact: "(vs,ws)\<in>lp_exact_finite_ld P"
        and inst: "hs=map (\<lambda>a. lp_atom_subst a delta) ws"
        by (rule lp_finite_step_lifting[OF step]) blast
      show "SN_on (lp_ld P) {hs}" using lower[OF exact] by (simp add: inst)
    qed
  qed
  show ?thesis using all[OF sn] by blast
qed

corollary lp_finite_nontermination_has_mgu_execution:
  "\<not>SN_on (lp_ld P) {gs} \<Longrightarrow> \<not>SN_on (lp_exact_finite_ld P) {gs}"
  using lp_exact_finite_termination_covers_instances[where sigma=Var, of P gs] by auto

end
