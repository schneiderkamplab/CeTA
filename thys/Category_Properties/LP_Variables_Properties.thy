theory LP_Variables_Properties
  imports LP_Properties
begin

lemma logic_subst_on_variables:
  assumes "\<And>x. logic_subtree (LVar x) t \<Longrightarrow> s x = r x"
  shows "logic_subst s t = logic_subst r t"
  using assms
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 list_all2_same
      intro: logic_subtree.intros)

text \<open>Finite and rational trees mention finitely many distinct variables.
This supplies the finite caller set needed for standardization apart.\<close>
lemma logic_rational_variables_finite:
  assumes "logic_rational t"
  shows "finite {x. logic_subtree (LVar x) t}"
proof -
  have "finite (LVar -` {u. logic_subtree u t})"
    by (rule finite_vimageI) (use assms in \<open>auto simp: logic_rational_def intro: injI\<close>)
  then show ?thesis by simp
qed

lemma logic_finite_variables_finite:
  "logic_finite t \<Longrightarrow> finite {x. logic_subtree (LVar x) t}"
  by (intro logic_rational_variables_finite logic_finite_rational)

text \<open>Infinitely many variables suffice to rename a finite clause away
from the finite set of caller variables while preserving distinct variables.
This is a variable-supply theorem, not a premise of the definitions.\<close>
lemma logic_fresh_renaming:
  fixes X Y :: "'v set"
  assumes infinite: "infinite (UNIV :: 'v set)"
    and X: "finite X" and Y: "finite Y"
  shows "\<exists>r :: 'v \<Rightarrow> 'v. inj_on r Y \<and> r ` Y \<inter> X = {}"
  using Y
proof (induct rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert y Y)
  obtain r where r: "inj_on r Y" "r ` Y \<inter> X = {}"
    using insert.hyps(3) by blast
  have "finite (X \<union> r ` Y)" using X insert.hyps(1) by simp
  from ex_new_if_finite[OF infinite this] obtain z where z: "z \<notin> X \<union> r ` Y" by blast
  show ?case
    by (rule exI[of _ "r(y := z)"])
      (use r z insert.hyps(2) in \<open>auto simp: inj_on_def\<close>)
qed

lemma logic_finite_namespaces:
  fixes X Y :: "'v set"
  assumes "infinite (UNIV :: 'v set)" "finite X" "finite Y"
  shows "\<exists>e :: 'v + 'v \<Rightarrow> 'v.
    (\<forall>x\<in>X. e (Inl x) = x) \<and> inj_on e (Inl ` X \<union> Inr ` Y)"
proof -
  obtain r where r: "inj_on r Y" "r ` Y \<inter> X = {}"
    using logic_fresh_renaming[OF assms] by blast
  have injective: "inj_on (case_sum id r) (Inl ` X \<union> Inr ` Y)"
  proof (rule inj_onI)
    fix a b
    assume a: "a \<in> Inl ` X \<union> Inr ` Y"
      and b: "b \<in> Inl ` X \<union> Inr ` Y"
      and eq: "case_sum id r a = case_sum id r b"
    show "a = b" using a b eq r
      by (cases a; cases b) (auto simp: inj_on_def)
  qed
  show ?thesis by (rule exI[of _ "case_sum id r"]) (simp add: injective)
qed

corollary logic_string_namespaces:
  assumes "finite (X :: string set)" "finite Y"
  shows "\<exists>e :: string + string \<Rightarrow> string.
    (\<forall>x\<in>X. e (Inl x) = x) \<and> inj_on e (Inl ` X \<union> Inr ` Y)"
  by (rule logic_finite_namespaces[OF infinite_UNIV_listI assms])

lemma logic_fresh_for_rational_goals:
  fixes gs :: "('f,'v) logic_tree list" and Y :: "'v set"
  assumes "infinite (UNIV :: 'v set)" "list_all logic_rational gs" "finite Y"
  shows "\<exists>r :: 'v \<Rightarrow> 'v. inj_on r Y \<and>
    r ` Y \<inter> (\<Union>t\<in>set gs. {x. logic_subtree (LVar x) t}) = {}"
  by (rule logic_fresh_renaming[OF assms(1) _ assms(3)])
    (use assms(2) in \<open>auto simp: list_all_iff intro!: finite_UN_I
      intro: logic_rational_variables_finite\<close>)

text \<open>An infinite variable type alone does not make every arbitrary tree
freshenable: one tree can already contain every variable. Correspondence for
executions from finite queries therefore needs a reachable-state invariant.\<close>
primcorec logic_variable_chain :: "nat \<Rightarrow> (unit,nat) logic_tree" where
  "logic_variable_chain n = LFun () [LVar n, logic_variable_chain (Suc n)]"

lemma logic_variable_chain_contains:
  "logic_subtree (LVar (n+k)) (logic_variable_chain n)"
proof (induct k arbitrary: n)
  case 0
  show ?case by (subst logic_variable_chain.code)
    (auto intro: logic_subtree.intros)
next
  case (Suc k)
  have "logic_subtree (LVar (n + Suc k)) (logic_variable_chain (Suc n))"
    using Suc.hyps[of "Suc n"] by simp
  then show ?case by (subst logic_variable_chain.code)
    (auto intro: logic_subtree.child)
qed

lemma logic_variable_chain_exhausts:
  "{x. logic_subtree (LVar x) (logic_variable_chain 0)} = UNIV"
  using logic_variable_chain_contains[of 0] by auto

lemma logic_variable_chain_not_freshenable:
  "r ` {x} \<inter> {y. logic_subtree (LVar y) (logic_variable_chain 0)} \<noteq> {}"
  by (simp add: logic_variable_chain_exhausts)

text \<open>A singleton variable type cannot freshen a variable-containing
clause against a caller already using that variable. Infinitude belongs in
variable-supply theorems, not in the program-validity definition.\<close>
lemma logic_unit_not_freshenable:
  "\<not>logic_freshening r [LVar ()] [SVar ()]"
  by (auto simp: logic_freshening_def logic_variables_def Let_def
      intro: logic_subtree.root)

end
