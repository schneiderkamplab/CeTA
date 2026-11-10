theory LP_Properties
  imports Category_Specifications.LP_Finite_Spec Category_Specifications.LP_Rational_Spec
    Category_Specifications.LP_Cut_Finite_Spec Category_Specifications.LP_Cut_Rational_Spec
    Category_Specifications.LP_Infinite_Spec Category_Specifications.LP_Cut_Infinite_Spec
begin

lemma logic_substitute_variable[simp]: "logic_subst s (LVar x) = s x"
  by (subst logic_subst.code) simp
lemma logic_substitute_function[simp]:
  "logic_subst s (LFun f ts) = LFun f (map (logic_subst s) ts)"
  by (subst logic_subst.code) simp
lemma logic_substitution_identity[simp]: "logic_subst LVar t = t"
  by (coinduction arbitrary: t)
    (auto simp: list_all2_map1 list.rel_refl split: logic_tree.splits)
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
  "logic_subtree (LVar x) t \<Longrightarrow> t=LVar x"
  by (cases rule: logic_subtree.cases) auto
lemma logic_rational_variable[simp]: "logic_rational (LVar x)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "{LVar x}"]) (auto dest: logic_subtree_variable)

lemma logic_subtree_function:
  "logic_subtree (LFun f ts) u \<longleftrightarrow>
    u = LFun f ts \<or> (\<exists>t\<in>set ts. logic_subtree t u)"
  by (auto elim: logic_subtree.cases intro: logic_subtree.intros)
lemma logic_rational_function:
  assumes "\<And>t. t\<in>set ts \<Longrightarrow> logic_rational t"
  shows "logic_rational (LFun f ts)"
proof -
  have "{u. logic_subtree (LFun f ts) u} =
    insert (LFun f ts) (\<Union>t\<in>set ts. {u. logic_subtree t u})"
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
primcorec logic_cycle :: "'f \<Rightarrow> 'f logic_tree" where
  "logic_cycle f = LFun f [logic_cycle f]"
lemma logic_cycle_subtree:
  "logic_subtree t u \<Longrightarrow> t=logic_cycle f \<Longrightarrow> u=logic_cycle f"
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
  "logic_substitution logic_finite s \<Longrightarrow>
    logic_subst s (LVar x) \<noteq> logic_subst s (LFun f [LVar x])"
  unfolding logic_substitution_def by (simp; metis logic_finite_not_cycle)
lemma logic_rational_cyclic_solution:
  "\<exists>s. logic_substitution logic_rational s \<and>
    logic_subst s (LVar x) = logic_subst s (LFun f [LVar x])"
  by (intro exI[of _ "\<lambda>x. logic_cycle f"])
    (simp add: logic_substitution_def logic_cycle_rational logic_cycle.code[symmetric])

lemma logic_empty_terminates: "logic_terminates_in D [] p modes"
proof -
  have "\<not> logic_step D [] s t" for s t by (auto elim: logic_step.cases)
  then show ?thesis unfolding logic_terminates_in_def by blast
qed
lemma logic_empty_finite: "lp_finite_terminates [] p modes"
  by (simp add: lp_finite_terminates_def logic_empty_terminates)
lemma logic_empty_rational: "lp_rational_terminates [] p modes"
  by (simp add: lp_rational_terminates_def logic_empty_terminates)
lemma logic_empty_infinite: "lp_infinite_terminates [] p modes"
  by (simp add: lp_infinite_terminates_def logic_empty_terminates)
lemma logic_nontermination_iff:
  "\<not> logic_terminates_in D P p modes \<longleftrightarrow>
    (\<exists>a s. logic_query p modes a \<and> s 0=[logic_atom_map logic_embed a] \<and>
      (\<forall>n. logic_step D P (s n) (s (Suc n))))"
  by (simp add: logic_terminates_in_def)
lemma logic_cut_nontermination_iff:
  "\<not> logic_cut_terminates_in D P p modes \<longleftrightarrow>
    (\<exists>ts s. logic_query (LogicUser p) modes (LogicUser p,ts) \<and>
      s 0=[LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]] \<and>
      (\<forall>n. logic_cut_step D P (s n) (s (Suc n))))"
  by (simp add: logic_cut_terminates_in_def)

text \<open>Saved alternatives outside the invocation survive a cut, and success
resumes alternatives. Neither operation reports termination at the first answer.\<close>
lemma logic_cut_scope_example:
  "logic_admin (LogicGoals [LogicCut 2] # LogicGoals gs # LogicBarrier 2 # caller) =
    Some (LogicGoals [] # LogicBarrier 2 # caller)"
  by simp
lemma logic_success_backtracks:
  "logic_cut_step D P (LogicGoals []#es) es"
  by (rule logic_cut_step.admin) simp
lemma logic_finite_cyclic_equation_fails:
  "logic_cut_step logic_finite P
    (LogicGoals (LogicUnify (LVar x) (LFun f [LVar x])#gs)#es) es"
  by (rule logic_cut_step.unify_fail) (auto dest: logic_occurs_check)
lemma logic_rational_cyclic_equation_does_not_fail:
  "\<exists>s. logic_substitution logic_rational s \<and>
    logic_subst s (LVar x) = logic_subst s (LFun f [LVar x])"
  by (rule logic_rational_cyclic_solution)


text \<open>Finite unification failure is an actual backtracking transition that
is absent in the infinite-tree machine. In particular, subset transfer of the
existing cut termination theorem would be invalid.\<close>
lemma logic_infinite_cyclic_equation_cannot_backtrack:
  "\<not> logic_cut_step (\<lambda>_. True) P
    (LogicGoals (LogicUnify (LVar x) (LFun f [LVar x])#gs)#es) es"
proof
  assume step: "logic_cut_step (\<lambda>_. True) P
    (LogicGoals (LogicUnify (LVar x) (LFun f [LVar x])#gs)#es) es"
  have solution: "\<exists>s. logic_substitution (\<lambda>_. True) s \<and>
    logic_subst s (LVar x) = logic_subst s (LFun f [LVar x])"
    using logic_rational_cyclic_solution[of x f] by (auto simp: logic_substitution_def)
  have unequal: "LogicGoals bs#es \<noteq> es" for bs
    by (rule notI; drule arg_cong[where f=length]; simp)
  from step show False
    by (cases rule: logic_cut_step.cases) (use solution unequal in auto)
qed

text \<open>A nullary recursive clause diverges in both domains. Query modes
permit arbitrary nonground outputs, but require finite ground inputs.\<close>
lemma logic_nullary_mgu:
  assumes "\<And>x. D (LVar x)"
  shows "logic_mgu D (p,[]) [] (p,[]) [(p,[])] LVar LVar"
  unfolding logic_mgu_def logic_substitution_def logic_atom_map_def
  using assms by (auto intro!: exI[of _ LVar])
lemma logic_nullary_step:
  assumes domain: "\<And>x. D (LVar x)"
  shows "logic_step D [((p,[]),[(p,[])])] [(p,[])] [(p,[])]"
proof -
  have mgu: "logic_mgu D (p,[]) [] (p,[]) [(p,[])] LVar LVar"
    by (rule logic_nullary_mgu) (rule domain)
  have step: "logic_step D [((p,[]),[(p,[])])] [(p,[])]
    (map (logic_atom_map (logic_eval LVar)) [(p,[])] @
     map (logic_atom_map (logic_subst LVar)) [])"
    by (rule logic_step.resolve[OF _ mgu]) simp
  show ?thesis using step by (simp add: logic_atom_map_def)
qed
lemma logic_nullary_nontermination:
  assumes "\<And>x. D (LVar x)"
  shows "\<not> logic_terminates_in D [((p,[]),[(p,[])])] p []"
  unfolding logic_terminates_in_def
  apply (intro notI)
  apply (erule notE)
  apply (rule exI[of _ "(p,[])"])
  apply (rule exI[of _ "\<lambda>n. [(p,[])]"])
  using logic_nullary_step[where D=D and p=p, OF assms]
  by (simp add: logic_query_def logic_atom_map_def)
lemma logic_finite_nullary_loop:
  "\<not> lp_finite_terminates [((p,[]),[(p,[])])] p []"
  unfolding lp_finite_terminates_def by (rule logic_nullary_nontermination) simp
lemma logic_rational_nullary_loop:
  "\<not> lp_rational_terminates [((p,[]),[(p,[])])] p []"
  unfolding lp_rational_terminates_def by (rule logic_nullary_nontermination) simp
lemma logic_nonground_output:
  "logic_query p [False] (p,[SFun f [SVar x]])"
  by (simp add: logic_query_def)
lemma logic_nonground_input_rejected:
  "\<not> logic_query p [True] (p,[SFun f [SVar x]])"
  by (simp add: logic_query_def)

end
