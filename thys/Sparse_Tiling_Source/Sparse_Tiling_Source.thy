theory Sparse_Tiling_Source
  imports "First_Order_Rewriting.Trs"
    "Sparse_Tiling_Construction.Sparse_Tiling_Termination"
begin

text \<open>Source correspondence uses genuine first-order terms. No checker
verdict is transferred before the term-rewriting implication is proved.\<close>

fun sparse_term :: "'a list \<Rightarrow> ('a,'v) term \<Rightarrow> ('a,'v) term" where
  "sparse_term [] t = t"
| "sparse_term (a # w) t = Fun a [sparse_term w t]"

lemma sparse_term_append:
  "sparse_term (u @ v) t = sparse_term u (sparse_term v t)"
  by (induction u) auto

lemma sparse_term_subst:
  "sparse_term w t \<cdot> \<sigma> = sparse_term w (t \<cdot> \<sigma>)"
  by (induction w) auto

lemma sparse_term_vars:
  "vars_term (sparse_term w t) = vars_term t"
  by (induction w) auto

fun sparse_branches :: "('a,'v) term \<Rightarrow> 'a list multiset" where
  "sparse_branches (Var x) = {#[]#}"
| "sparse_branches (Fun f ts) = (if ts = [] then {#[f]#}
    else image_mset (Cons f) (\<Sum>\<^sub># (image_mset sparse_branches (mset ts))))"

lemma sparse_branches_nonempty [simp]: "sparse_branches t \<noteq> {#}"
  by (induction t) (auto simp: image_mset_is_empty_iff)

lemma sparse_branches_term:
  "sparse_branches (sparse_term w t) = image_mset ((@) w) (sparse_branches t)"
  by (induction w) (auto simp: image_mset.compositionality comp_def)

lemma sparse_branches_context:
  "\<exists>p I. \<forall>t. sparse_branches (C\<langle>t\<rangle>) = I + image_mset ((@) p) (sparse_branches t)"
proof (induction C)
  case Hole
  show ?case by (intro exI[of _ "[]"] exI[of _ "{#}"]) simp
next
  case (More f ls C rs)
  then obtain p I where IH: "\<And>t. sparse_branches (C\<langle>t\<rangle>) = I + image_mset ((@) p) (sparse_branches t)" by blast
  let ?I = "image_mset (Cons f) (\<Sum>\<^sub># (image_mset sparse_branches (mset ls)) + I +
    \<Sum>\<^sub># (image_mset sparse_branches (mset rs)))"
  show ?case
    by (intro exI[of _ "f # p"] exI[of _ ?I])
      (simp add: IH image_mset.compositionality comp_def ac_simps)
qed

lemma sparse_term_rules_simulation:
  assumes represent: "\<And>l r. (l,r) \<in> T \<Longrightarrow> \<exists>u v x.
    (u,v) \<in> R \<and> l = sparse_term u (Var x) \<and> r = sparse_term v (Var x)"
    and step: "(s,t) \<in> rstep T"
  shows "(sparse_branches t,sparse_branches s) \<in> mult ((sparse_word_step R)\<inverse>)"
proof -
  obtain C \<sigma> l r where rule: "(l,r) \<in> T" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" using step by (cases rule: rstep.cases) blast
  obtain u v x where words: "(u,v) \<in> R" and l: "l = sparse_term u (Var x)"
    and r: "r = sparse_term v (Var x)" using represent[OF rule] by blast
  obtain p I where context_paths: "\<And>a. sparse_branches (C\<langle>a\<rangle>) = I + image_mset ((@) p) (sparse_branches a)"
    using sparse_branches_context[of C] by blast
  have before: "sparse_branches s = I + image_mset ((@) (p @ u)) (sparse_branches (\<sigma> x))"
    by (simp add: s l sparse_term_subst context_paths sparse_branches_term image_mset.compositionality comp_def append_assoc;
      rule image_mset_cong; simp add: append_assoc)
  have after: "sparse_branches t = I + image_mset ((@) (p @ v)) (sparse_branches (\<sigma> x))"
    by (simp add: t r sparse_term_subst context_paths sparse_branches_term image_mset.compositionality comp_def append_assoc;
      rule image_mset_cong; simp add: append_assoc)
  show ?thesis unfolding before after
  proof (rule one_step_implies_mult)
    show "image_mset ((@) (p @ u)) (sparse_branches (\<sigma> x)) \<noteq> {#}" by simp
  next
    show "\<forall>k\<in>set_mset (image_mset ((@) (p @ v)) (sparse_branches (\<sigma> x))).
      \<exists>j\<in>set_mset (image_mset ((@) (p @ u)) (sparse_branches (\<sigma> x))).
      (k,j) \<in> (sparse_word_step R)\<inverse>"
      using sparse_word_stepI[OF words, of p] by (auto simp: append_assoc)
  qed
qed

lemma sparse_word_SN_imp_term_SN:
  assumes represent: "\<And>l r. (l,r) \<in> T \<Longrightarrow> \<exists>u v x.
    (u,v) \<in> R \<and> l = sparse_term u (Var x) \<and> r = sparse_term v (Var x)"
    and sn: "SN (sparse_word_step R)"
  shows "SN (rstep T)"
proof -
  let ?M = "(mult ((sparse_word_step R)\<inverse>))\<inverse>"
  have mult_sn: "SN ?M" using wf_mult[of "(sparse_word_step R)\<inverse>"] sn
    by (simp add: SN_iff_wf)
  show ?thesis
  proof (rule sparse_local_simulation_SN[where L=UNIV and label=sparse_branches and S="?M"])
    fix x y
    assume "x \<in> UNIV" "(x,y) \<in> rstep T"
    show "y \<in> UNIV" by simp
  next
    fix x y
    assume "x \<in> UNIV" and step: "(x,y) \<in> rstep T"
    have "(sparse_branches y,sparse_branches x) \<in> mult ((sparse_word_step R)\<inverse>)"
      by (rule sparse_term_rules_simulation[OF _ step]) (meson represent)
    then show "(sparse_branches x,sparse_branches y) \<in> ?M" by simp
  next
    show "SN_on ?M (sparse_branches ` UNIV)" using mult_sn unfolding SN_on_def by blast
  qed
qed

lemma sparse_term_context:
  assumes step: "(s,t) \<in> rstep T"
  shows "(sparse_term w s,sparse_term w t) \<in> rstep T"
proof (induction w)
  case Nil
  then show ?case using step by simp
next
  case (Cons a w)
  have "((More a [] \<box> [])\<langle>sparse_term w s\<rangle>,
    (More a [] \<box> [])\<langle>sparse_term w t\<rangle>) \<in> rstep T"
    by (rule rstep_ctxt[OF Cons.IH])
  then show ?case by simp
qed

lemma sparse_word_to_term_step:
  assumes represent: "\<And>u v. (u,v) \<in> R \<Longrightarrow> \<exists>x.
    (sparse_term u (Var x),sparse_term v (Var x)) \<in> T"
    and step: "(s,t) \<in> sparse_word_step R"
  shows "(sparse_term s d,sparse_term t d) \<in> rstep T"
proof -
  obtain p q u v where rule: "(u,v) \<in> R" and s: "s = p @ u @ q" and t: "t = p @ v @ q"
    using step unfolding sparse_word_step_def by blast
  obtain x where term_rule: "(sparse_term u (Var x),sparse_term v (Var x)) \<in> T"
    using represent[OF rule] by blast
  have instantiated: "(sparse_term u (sparse_term q d),sparse_term v (sparse_term q d)) \<in> rstep T"
    using rstep_subst[OF rstep_rule[OF term_rule], of "\<lambda>_. sparse_term q d"]
    by (simp add: sparse_term_subst)
  from sparse_term_context[OF instantiated, of p] show ?thesis
    by (simp add: s t sparse_term_append)
qed

lemma sparse_term_SN_imp_word_SN:
  assumes represent: "\<And>u v. (u,v) \<in> R \<Longrightarrow> \<exists>x.
    (sparse_term u (Var x),sparse_term v (Var x)) \<in> T"
    and sn: "SN (rstep T)"
  shows "SN (sparse_word_step R)"
proof (rule sparse_local_simulation_SN[where L=UNIV and label="\<lambda>w. sparse_term w (Var undefined)" and S="rstep T"])
  fix x y
  assume "x \<in> UNIV" "(x,y) \<in> sparse_word_step R"
  show "y \<in> UNIV" by simp
next
  fix x y
  assume "x \<in> UNIV" and step: "(x,y) \<in> sparse_word_step R"
  show "(sparse_term x (Var undefined),sparse_term y (Var undefined)) \<in> rstep T"
    by (rule sparse_word_to_term_step[OF _ step]) (meson represent)
next
  show "SN_on (rstep T) ((\<lambda>w. sparse_term w (Var undefined)) ` UNIV)"
    using sn unfolding SN_on_def by blast
qed

end
