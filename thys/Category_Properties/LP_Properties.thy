theory LP_Properties
  imports Category_Specifications.LP_Finite_Spec Category_Specifications.LP_Rational_Spec
    Category_Specifications.LP_Cut_Finite_Spec Category_Specifications.LP_Cut_Rational_Spec
    Category_Specifications.LP_Infinite_Spec Category_Specifications.LP_Cut_Infinite_Spec
begin

lemma logic_atom_map_comp:
  "logic_atom_map f (logic_atom_map g a) = logic_atom_map (f \<circ> g) a"
  by (cases a) (simp add: map_map)


lemma logic_substitute_variable[simp]: "logic_subst s (LVar x) = s x"
  by (subst logic_subst.code) simp
lemma logic_substitute_function[simp]:
  "logic_subst s (LFun f ts) = LFun f (map (logic_subst s) ts)"
  by (subst logic_subst.code) simp
lemma logic_substitution_identity[simp]: "logic_subst LVar t = t"
  by (coinduction arbitrary: t)
    (auto simp: list_all2_map1 list.rel_refl split: logic_tree.splits)
lemma logic_tree_arity_variable[simp]:
  "logic_tree_arity_correct A (LVar x)"
  by (rule logic_tree_arity_correct.variable)
lemma logic_tree_arity_function[simp]:
  "logic_tree_arity_correct A (LFun f ts) \<longleftrightarrow>
    length ts = A f \<and> list_all (logic_tree_arity_correct A) ts"
  by (auto intro: logic_tree_arity_correct.application
      elim: logic_tree_arity_correct.cases)
lemma logic_embed_arity_correct[simp]:
  "logic_tree_arity_correct A (logic_embed t) \<longleftrightarrow> arity_correct A t"
  by (induct t) (auto simp: list_all_iff)

lemma logic_embed_injective[simp]: "logic_embed s = logic_embed t \<longleftrightarrow> s=t"
proof (induct s arbitrary: t)
  case (SVar x) then show ?case by (cases t) auto
next
  case (SFun f ts)
  show ?case
  proof (cases t)
    case (SVar x) then show ?thesis by simp
  next
    case (SFun g us)
    have "ts=us" if "map logic_embed ts=map logic_embed us"
    proof (rule nth_equalityI)
      show "length ts=length us" using that by (metis length_map)
      fix i assume "i<length ts"
      then have "logic_embed (ts!i)=logic_embed (us!i)"
        using that \<open>length ts=length us\<close> by (metis nth_map)
      then show "ts!i=us!i" using SFun.hyps \<open>i<length ts\<close> by simp
    qed
    then show ?thesis by (auto simp: SFun)
  qed
qed
lemma logic_finite_variable[simp]: "logic_finite (LVar x)"
  unfolding logic_finite_def by (rule exI[of _ "SVar x"]) simp
lemma logic_subtree_variable:
  "logic_subtree t (LVar x) \<Longrightarrow> t=LVar x"
  by (auto elim: logic_subtree.cases)
lemma logic_rational_variable[simp]: "logic_rational (LVar x)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "{LVar x}"]) (auto dest: logic_subtree_variable)

lemma logic_subtree_function:
  "logic_subtree u (LFun f ts) \<longleftrightarrow>
    u = LFun f ts \<or> (\<exists>t\<in>set ts. logic_subtree u t)"
  by (auto elim: logic_subtree.cases intro: logic_subtree.intros)
lemma logic_rational_function:
  assumes "\<And>t. t\<in>set ts \<Longrightarrow> logic_rational t"
  shows "logic_rational (LFun f ts)"
proof -
  have "{u. logic_subtree u (LFun f ts)} =
    insert (LFun f ts) (\<Union>t\<in>set ts. {u. logic_subtree u t})"
    by (auto simp: logic_subtree_function)
  then show ?thesis using assms unfolding logic_rational_def by simp
qed
lemma logic_embed_rational: "logic_rational (logic_embed t)"
proof (induct t)
  case (SVar x) then show ?case by simp
next
  case (SFun f ts)
  show ?case unfolding logic_embed.simps
    by (rule logic_rational_function) (use SFun in auto)
qed
lemma logic_finite_rational: "logic_finite t \<Longrightarrow> logic_rational t"
  by (auto simp: logic_finite_def intro: logic_embed_rational)

text \<open>A genuine rational cycle is admitted, but it is not a finite term.\<close>
primcorec logic_cycle :: "'f \<Rightarrow> ('f,'v) logic_tree" where
  "logic_cycle f = LFun f [logic_cycle f]"
lemma logic_cycle_subtree:
  "logic_subtree u t \<Longrightarrow> t=logic_cycle f \<Longrightarrow> u=logic_cycle f"
proof (induct rule: logic_subtree.induct)
  case (root t) then show ?case by simp
next
  case (child u ts v g)
  have eq: "LFun g ts = LFun f [logic_cycle f]"
    using child.prems by (subst (asm) logic_cycle.code) assumption
  then have "ts=[logic_cycle f]" by simp
  then show ?case using child.hyps by simp
qed
lemma logic_cycle_rational: "logic_rational (logic_cycle f)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "{logic_cycle f}"]) (auto dest: logic_cycle_subtree)
lemma logic_finite_not_cycle:
  "logic_finite t \<Longrightarrow> t \<noteq> LFun f [t]"
proof -
  assume "logic_finite t"
  then obtain u where t: "t=logic_embed u" by (auto simp: logic_finite_def)
  have unequal: "u \<noteq> SFun f [u]" by (rule notI; drule arg_cong[where f=size]; simp)
  show ?thesis
  proof
    assume eq: "t = LFun f [t]"
    have "logic_embed u = logic_embed (SFun f [u])" using eq
      by (simp only: t logic_embed.simps list.map)
    then have "u = SFun f [u]" by (simp only: logic_embed_injective)
    with unequal show False by contradiction
  qed
qed

lemma logic_occurs_check:
  "logic_substitution_in logic_finite s \<Longrightarrow>
    logic_subst s (LVar x) \<noteq> logic_subst s (LFun f [LVar x])"
  unfolding logic_substitution_in_def by (simp; metis logic_finite_not_cycle)
lemma logic_rational_cyclic_solution:
  "\<exists>s. logic_substitution_in logic_rational s \<and>
    logic_subst s (LVar x) = logic_subst s (LFun f [LVar x])"
  by (intro exI[of _ "\<lambda>x. logic_cycle f"])
    (simp add: logic_substitution_in_def logic_cycle_rational logic_cycle.code[symmetric])

lemma logic_mgu_identity:
  "(\<And>x. D (LVar x)) \<Longrightarrow> logic_mgu D a a LVar"
  by (auto simp: logic_mgu_def logic_substitution_in_def)

lemma logic_empty_terminates: "logic_terminates_in A D [] p modes"
proof -
  have "\<not>logic_step A D [] s t" for s t by (auto elim: logic_step.cases)
  then show ?thesis unfolding logic_terminates_in_def by blast
qed

lemma logic_nullary_step:
  assumes "\<And>x. D (LVar x)"
  shows "logic_step A D [(LAtom p [],[LAtom p []])] [LAtom p []] [LAtom p []]"
proof -
  have fresh: "logic_freshening id (concat (map logic_arguments [LAtom p []]))
      (concat (map logic_arguments [LAtom p [],LAtom p []]))"
    by (simp add: logic_freshening_def Let_def)
  have mgu: "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t)
      (LAtom p []) (logic_atom_map (logic_eval (LVar \<circ> id)) (LAtom p [])) LVar"
    by (simp; rule logic_mgu_identity) (simp add: assms)
  have step: "logic_step A D [(LAtom p [],[LAtom p []])] [LAtom p []]
    (map (logic_atom_map (logic_subst LVar))
      (map (logic_atom_map (logic_eval (LVar \<circ> id))) [LAtom p []] @ []))"
    by (rule logic_step.resolve[OF _ fresh mgu]) simp
  show ?thesis using step by simp
qed

lemma logic_nullary_nontermination:
  assumes "A p = 0" "\<And>x. D (LVar x)"
  shows "\<not>logic_terminates_in A D [(LAtom p [],[LAtom p []])] p []"
  unfolding logic_terminates_in_def
  apply (intro notI; erule notE)
  apply (rule exI[of _ "LAtom p []"])
  apply (rule exI[of _ "\<lambda>n. [LAtom p []]"])
  using assms logic_nullary_step[where A=A and D=D and p=p, OF assms(2)]
  by (simp add: logic_query_def)

lemma logic_overloaded_predicates:
  "logic_problem snd
    [(LAtom (p,1) [SVar x],[]), (LAtom (p,2) [SVar x,SVar y],[])] (p,1) [False]"
  by (simp add: logic_problem_def)
lemma logic_wrong_atom_arity:
  "\<not>logic_problem snd [(LAtom (p,1) [],[])] (p,1) [False]"
  by (simp add: logic_problem_def)
lemma logic_wrong_query_arity:
  "\<not>logic_query snd (p,1) [] (LAtom (p,1) [SVar x])"
  by (simp add: logic_query_def)
lemma logic_nonground_query:
  "logic_query snd (p,1) [False] (LAtom (p,1) [SFun (f,1) [SVar x]])"
  by (simp add: logic_query_def)
lemma logic_nonground_input_rejected:
  "\<not>logic_query snd (p,1) [True] (LAtom (p,1) [SFun (f,1) [SVar x]])"
  by (simp add: logic_query_def)

lemma logic_global_occurs_check:
  "\<not>logic_mgu logic_finite (LAtom p [LVar x]) (LAtom p [LFun f [LVar x]]) s"
  using logic_occurs_check[where x=x and f=f]
  by (auto simp: logic_mgu_def)
lemma logic_cycle_arity:
  "A f = 1 \<Longrightarrow> logic_tree_arity_correct A (logic_cycle f)"
  by (coinduction) (subst logic_cycle.code; simp)
lemma logic_fixed_cycle:
  assumes eq: "t = LFun f [t]"
  shows "t = logic_cycle f"
proof -
  have disc: "\<not>is_LVar t" using eq by (cases t) auto
  have root: "un_LFun1 t = f" using arg_cong[OF eq, where f=un_LFun1] by simp
  have children: "un_LFun2 t = [t]" using arg_cong[OF eq, where f=un_LFun2] by simp
  show ?thesis by (coinduction) (subst logic_cycle.code; simp add: disc root children)
qed
lemma logic_global_rational_occurs_solution:
  fixes f :: "'f"
  assumes "A f = 1"
  shows "logic_mgu (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct A t)
    (LAtom () [LVar ()]) (LAtom () [LFun f [LVar ()]]) (\<lambda>_. logic_cycle f)"
proof -
  have dom: "logic_rational (logic_cycle f) \<and> logic_tree_arity_correct A (logic_cycle f)"
    by (intro conjI logic_cycle_rational logic_cycle_arity[where A=A and f=f, OF assms])
  have factor: "\<exists>v. logic_substitution_in (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct A t) v \<and>
      (\<forall>x. u x = logic_subst v (logic_cycle f))"
    if eq: "u () = LFun f [u ()]" for u :: "unit \<Rightarrow> ('f,unit) logic_tree"
    using logic_fixed_cycle[OF eq]
    by (intro exI[of _ LVar]) (simp add: logic_substitution_in_def)
  show ?thesis using dom factor
    by (auto simp: logic_mgu_def logic_substitution_in_def logic_cycle.code[symmetric])
qed

lemma logic_cut_scope_example:
  "logic_admin (LogicGoals [LogicCut 2] # LogicGoals gs # LogicBarrier 2 # caller) =
    Some (LogicGoals [] # LogicBarrier 2 # caller)"
  by simp
lemma logic_success_backtracks:
  "logic_cut_step A D P (LogicGoals []#es) es"
  by (rule logic_cut_step.admin) simp
lemma logic_unbound_meta_stuck_example:
  "\<not>logic_cut_step A D P (LogicGoals (LogicMeta (LVar x)#gs)#es) t"
  by (auto elim: logic_cut_step.cases logic_lower_diverges.cases)
lemma logic_meta_preserves_atom_constructor:
  "logic_lower m (LFun (LogicUser f) ts) [LogicAtom (LAtom f ts)]"
  by (rule logic_lower.atom)

end
