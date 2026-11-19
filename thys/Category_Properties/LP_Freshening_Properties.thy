theory LP_Freshening_Properties
  imports LP_Variables_Properties LP_Domain_Properties LP_Arity_Projection
begin

lemma logic_merge_substitutions:
  fixes r :: "'v \<Rightarrow> 'v" and s t :: "'v \<Rightarrow> 'a"
  assumes injective: "inj_on r Y" and disjoint: "r ` Y \<inter> X = {}"
    and sd: "\<And>x. D (s x)" and td: "\<And>x. D (t x)"
  obtains u where "\<And>x. D (u x)" "\<And>x. x \<in> X \<Longrightarrow> u x = s x"
    "\<And>x. x \<in> Y \<Longrightarrow> u (r x) = t x"
proof -
  let ?u = "\<lambda>x. if x \<in> r ` Y then t (inv_into Y r x) else s x"
  have domain: "D (?u x)" for x using sd td by simp
  have caller: "?u x = s x" if "x \<in> X" for x using disjoint that by auto
  have clause: "?u (r x) = t x" if "x \<in> Y" for x
    using injective that by (simp add: inv_into_f_f)
  show thesis by (rule that[OF domain caller clause])
qed

lemma logic_freshening_substitution:
  assumes fresh: "logic_freshening r active clause"
    and sd: "logic_substitution_in D s" and td: "logic_substitution_in D t"
  obtains u where "logic_substitution_in D u"
    "\<And>a. a\<in>set active \<Longrightarrow> logic_subst u a = logic_subst s a"
    "\<And>h. h\<in>set clause \<Longrightarrow>
      logic_subst u (logic_eval (LVar \<circ> r) h) = logic_eval t h"
proof -
  let ?X = "\<Union>(logic_variables ` set active)"
  let ?Y = "\<Union>((logic_variables \<circ> logic_embed) ` set clause)"
  have r: "inj_on r ?Y" "r ` ?Y \<inter> ?X = {}"
    using fresh by (auto simp: logic_freshening_def Let_def)
  obtain u where du: "\<And>x. D (u x)" and caller: "\<And>x. x\<in>?X \<Longrightarrow> u x=s x"
    and clause: "\<And>x. x\<in>?Y \<Longrightarrow> u (r x)=t x"
    by (rule logic_merge_substitutions[where D=D and s=s and t=t, OF r])
      (use sd td in \<open>auto simp: logic_substitution_in_def\<close>)
  have active: "logic_subst u a = logic_subst s a" if "a\<in>set active" for a
    by (rule logic_subst_on_variables) (use caller that in \<open>auto simp: logic_variables_def\<close>)
  have body: "logic_subst u (logic_eval (LVar \<circ> r) h) = logic_eval t h"
    if "h\<in>set clause" for h
    unfolding logic_subst_composition
    by (rule logic_subst_on_variables)
      (use clause that in \<open>auto simp: logic_variables_def o_def\<close>)
  show thesis by (rule that[OF _ active body]) (simp add: logic_substitution_in_def du)
qed

lemma logic_atom_map_equal_on:
  "(\<And>t. t\<in>set (logic_arguments a) \<Longrightarrow> f t = g t) \<Longrightarrow>
    logic_atom_map f a = logic_atom_map g a"
  by (cases a) (auto intro!: map_cong)

lemma logic_fresh_unifier:
  assumes fresh: "logic_freshening r (logic_arguments a @ active) (logic_arguments h @ body)"
    and sd: "logic_substitution_in D s" and td: "logic_substitution_in D t"
    and eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval t) h"
  shows "\<exists>u. logic_substitution_in D u \<and>
    logic_atom_map (logic_subst u) a =
      logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) h"
proof -
  obtain u where domain: "logic_substitution_in D u"
    and caller: "\<And>x. x\<in>set (logic_arguments a @ active) \<Longrightarrow> logic_subst u x=logic_subst s x"
    and clause: "\<And>x. x\<in>set (logic_arguments h @ body) \<Longrightarrow>
      logic_subst u (logic_eval (LVar \<circ> r) x) = logic_eval t x"
    by (rule logic_freshening_substitution[OF fresh sd td]) blast
  have left: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst s) a"
    by (rule logic_atom_map_equal_on) (simp add: caller)
  have right: "logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) h =
      logic_atom_map (logic_eval t) h"
    by (rule logic_atom_map_equal_on) (simp add: clause)
  show ?thesis by (intro exI[of _ u]) (simp add: domain left right eq)
qed

lemma logic_atom_arity_project_subst:
  assumes "list_all (logic_tree_arity_correct A) (logic_arguments a)"
  shows "logic_atom_map (logic_arity_project A z) (logic_atom_map (logic_subst s) a) =
    logic_atom_map (logic_subst (logic_arity_project A z \<circ> s)) a"
  unfolding logic_atom_map_comp
  by (rule logic_atom_map_equal_on)
    (use assms in \<open>auto simp: list_all_iff o_def intro: logic_arity_project_subst[unfolded o_def]\<close>)
lemma logic_atom_arity_project_eval:
  assumes "list_all (arity_correct A) (logic_arguments h)"
  shows "logic_atom_map (logic_arity_project A z) (logic_atom_map (logic_eval t) h) =
    logic_atom_map (logic_eval (logic_arity_project A z \<circ> t)) h"
  unfolding logic_atom_map_comp
  by (rule logic_atom_map_equal_on)
    (use assms in \<open>auto simp: list_all_iff o_def intro: logic_arity_project_subst[unfolded o_def]\<close>)

lemma logic_typed_fresh_unifier:
  assumes fresh: "logic_freshening r (logic_arguments a @ active) (logic_arguments h @ body)"
    and caller: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and clause: "list_all (arity_correct A) (logic_arguments h)"
    and sd: "logic_substitution_in D s" and td: "logic_substitution_in D t"
    and closed: "\<And>u. D u \<Longrightarrow> D (logic_arity_project A z u)"
    and eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval t) h"
  shows "\<exists>u. logic_substitution_in (\<lambda>x. D x \<and> logic_tree_arity_correct A x) u \<and>
    logic_atom_map (logic_subst u) a =
      logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) h"
proof -
  have sd': "logic_substitution_in (\<lambda>x. D x \<and> logic_tree_arity_correct A x)
    (logic_arity_project A z \<circ> s)"
    using sd closed logic_arity_project_correct by (auto simp: logic_substitution_in_def)
  have td': "logic_substitution_in (\<lambda>x. D x \<and> logic_tree_arity_correct A x)
    (logic_arity_project A z \<circ> t)"
    using td closed logic_arity_project_correct by (auto simp: logic_substitution_in_def)
  have projected: "logic_atom_map (logic_subst (logic_arity_project A z \<circ> s)) a =
      logic_atom_map (logic_eval (logic_arity_project A z \<circ> t)) h"
    using arg_cong[OF eq, where f="logic_atom_map (logic_arity_project A z)"]
    by (simp only: logic_atom_arity_project_subst[OF caller] logic_atom_arity_project_eval[OF clause])
  show ?thesis by (rule logic_fresh_unifier[OF fresh sd' td' projected])
qed

end
