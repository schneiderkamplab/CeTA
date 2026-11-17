theory LP_Fresh_Finite_Lifting
  imports LP_Global_MGU Category_LP_Bridge.LP_Checked_Global_MGU
begin

text \<open>A finite caller has a bound on the lengths of its variable names.
Prefixing clause variables beyond that bound standardizes the clause apart.
The bound is an implementation of freshening at the string boundary only.\<close>
definition lp_short_atoms :: "nat \<Rightarrow> ('f,string) lp_atom list \<Rightarrow> bool" where
  "lp_short_atoms k gs \<longleftrightarrow>
    (\<forall>a\<in>set gs. \<forall>t\<in>set (snd a). \<forall>x\<in>vars_term t. length x < k)"

lemma lp_short_atoms_exists:
  "\<exists>k. lp_short_atoms k gs"
proof -
  let ?X = "\<Union>a\<in>set gs. \<Union>t\<in>set (snd a). vars_term t"
  have fin: "finite ?X" by auto
  have bound: "length x < Suc (Lattices_Big.linorder_class.Max (length ` ?X))" if "x\<in>?X" for x
  proof -
    have "length x \<le> Lattices_Big.linorder_class.Max (length ` ?X)"
      by (rule Lattices_Big.linorder_class.Max_ge) (use fin that in auto)
    then show ?thesis by simp
  qed
  show ?thesis by (intro exI[of _ "Suc (Lattices_Big.linorder_class.Max (length ` ?X))"])
    (auto simp: lp_short_atoms_def intro: bound)
qed

lemma lp_finite_subst_on_vars:
  "(\<And>x. x\<in>vars_term t \<Longrightarrow> s x = r x) \<Longrightarrow> t\<cdot>s = t\<cdot>r"
  by (induct t) auto

lemma lp_short_atoms_merge:
  assumes "lp_short_atoms k gs" "a\<in>set gs"
  shows "lp_atom_subst a (\<lambda>x. if length x<k then s x else r (drop k x)) = lp_atom_subst a s"
  unfolding lp_atom_subst_def
  apply (intro arg_cong2[where f=Pair] refl map_cong)
  apply (rule lp_finite_subst_on_vars)
  using assms unfolding lp_short_atoms_def by auto

lemma lp_prefix_atom_merge:
  "lp_atom_subst (lp_atom_subst a (\<lambda>x. Var (lp_prefix k x)))
      (\<lambda>x. if length x<k then s x else r (drop k x)) = lp_atom_subst a r"
  by (simp add: lp_atom_subst_def map_map o_def eval_subst_def subst_subst lp_prefix_def)

text \<open>Each step uses one normalized MGU after explicitly renaming the
clause. The same substitution acts on its body and on the caller continuation.\<close>
inductive_set lp_fresh_finite_ld :: "('f,string) lp_clause list \<Rightarrow> ('f,string) lp_atom list rel"
  for P where
  resolve: "c<length P \<Longrightarrow> lp_short_atoms k (a#gs) \<Longrightarrow>
    lp_normalized_mgu a (lp_atom_subst (fst (P!c)) (\<lambda>x. Var (lp_prefix k x))) mu \<Longrightarrow>
    (a#gs, map (\<lambda>b. lp_atom_subst (lp_atom_subst b (\<lambda>x. Var (lp_prefix k x))) mu) (snd (P!c)) @
      map (\<lambda>b. lp_atom_subst b mu) gs) \<in> lp_fresh_finite_ld P"

lemma lp_fresh_finite_step_lifting:
  fixes sigma :: "string \<Rightarrow> ('f,string) term"
  assumes step: "(map (\<lambda>a. lp_atom_subst a sigma) gs,hs)\<in>lp_ld P"
  obtains us delta where "(gs,us)\<in>lp_fresh_finite_ld P"
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
    and tail: "tail=map (\<lambda>a. lp_atom_subst a sigma) rest"
    using selected by (simp_all add: gs)
  obtain k where short: "lp_short_atoms k (a#rest)"
    using lp_short_atoms_exists by blast
  let ?r = "\<lambda>x. Var (lp_prefix k x)"
  let ?d = "\<lambda>x. if length x<k then (sigma \<circ>\<^sub>s tau) x else nu (drop k x)"
  have old: "lp_atom_subst b ?d = lp_atom_subst b (sigma \<circ>\<^sub>s tau)"
    if "b\<in>set (a#rest)" for b
    by (rule lp_short_atoms_merge[OF short that])
  have solution: "lp_atom_subst a ?d = lp_atom_subst (lp_atom_subst (fst (P!c)) ?r) ?d"
    using native by (simp add: head old lp_prefix_atom_merge eval_subst_def lp_prefix_def)
  obtain mu where mgu: "lp_normalized_mgu a (lp_atom_subst (fst (P!c)) ?r) mu"
    by (rule lp_normalized_mgu_exists[OF solution]) blast
  have factor: "mu \<circ>\<^sub>s ?d = ?d"
    by (rule ext) (simp add: subst_compose lp_normalized_mgu_finite_factor[OF mgu solution])
  let ?us = "map (\<lambda>b. lp_atom_subst (lp_atom_subst b ?r) mu) (snd (P!c)) @
      map (\<lambda>b. lp_atom_subst b mu) rest"
  have exact: "(gs,?us)\<in>lp_fresh_finite_ld P"
    unfolding gs by (rule lp_fresh_finite_ld.resolve[OF c short mgu])
  have inst: "hs=map (\<lambda>b. lp_atom_subst b ?d) ?us"
    using target
    by (simp add: tail map_map o_def eval_subst_def factor[unfolded eval_subst_def]
      lp_normalized_mgu_finite_factor[OF mgu solution] lp_prefix_def old cong: map_cong)
  show thesis by (rule that[OF exact inst])
qed

lemma lp_fresh_finite_termination_covers_instances:
  fixes sigma :: "string \<Rightarrow> ('f,string) term"
  assumes sn: "SN_on (lp_fresh_finite_ld P) {gs}"
  shows "SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) gs}"
proof -
  have all: "\<forall>sigma. SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) us}"
    if sn: "SN_on (lp_fresh_finite_ld P) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro allI)
    fix vs sigma
    assume lower: "\<And>ws. (vs,ws)\<in>lp_fresh_finite_ld P \<Longrightarrow>
      \<forall>sigma. SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) ws}"
    show "SN_on (lp_ld P) {map (\<lambda>a. lp_atom_subst a sigma) vs}"
    proof (rule step_reflects_SN_on)
      fix hs assume step: "(map (\<lambda>a. lp_atom_subst a sigma) vs,hs)\<in>lp_ld P"
      obtain ws delta where exact: "(vs,ws)\<in>lp_fresh_finite_ld P"
        and inst: "hs=map (\<lambda>a. lp_atom_subst a delta) ws"
        by (rule lp_fresh_finite_step_lifting[OF step]) blast
      show "SN_on (lp_ld P) {hs}" using lower[OF exact] by (simp add: inst)
    qed
  qed
  show ?thesis using all[OF sn] by blast
qed

corollary lp_finite_nontermination_has_fresh_mgu_execution:
  "\<not>SN_on (lp_ld P) {gs} \<Longrightarrow> \<not>SN_on (lp_fresh_finite_ld P) {gs}"
  using lp_fresh_finite_termination_covers_instances[where sigma=Var, of P gs] by auto

end
