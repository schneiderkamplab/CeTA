theory LP_MGU_Arity_Abstraction
  imports LP_MGU_Domain_Extension
begin

text \<open>Malformed subtrees are named by variables, separately from renamed
original variables. Unlike projection to one fixed variable, this abstraction
can retain enough information to reconstruct an arbitrary competing unifier.\<close>
primcorec logic_arity_abstract ::
  "'f arity \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> (('f,'v) logic_tree \<Rightarrow> 'w) \<Rightarrow>
    ('f,'v) logic_tree \<Rightarrow> ('f,'w) logic_tree" where
  "logic_arity_abstract A r b t = (case t of LVar x \<Rightarrow> LVar (r x) |
    LFun f ts \<Rightarrow> if length ts = A f then
      LFun f (map (logic_arity_abstract A r b) ts) else LVar (b t))"
lemma logic_arity_abstract_simps[simp]:
  "logic_arity_abstract A r b (LVar x) = LVar (r x)"
  "logic_arity_abstract A r b (LFun f ts) =
    (if length ts = A f then LFun f (map (logic_arity_abstract A r b) ts)
      else LVar (b (LFun f ts)))"
  by (subst logic_arity_abstract.code; simp)+
lemma logic_arity_abstract_correct:
  "logic_tree_arity_correct A (logic_arity_abstract A r b t)"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all_iff)
lemma logic_arity_abstract_subst:
  "logic_tree_arity_correct A t \<Longrightarrow>
    logic_arity_abstract A r b (logic_subst s t) =
      logic_subst (logic_arity_abstract A r b \<circ> s) t"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all_iff list_all2_map1 list_all2_map2 list_all2_same)

lemma logic_arity_abstract_recover:
  assumes vars: "\<And>x. gamma (r x) = LVar x"
    and bad: "\<And>f ts. logic_subtree (LFun f ts) t \<Longrightarrow> length ts \<noteq> A f \<Longrightarrow>
      gamma (b (LFun f ts)) = LFun f ts"
  shows "logic_subst gamma (logic_arity_abstract A r b t) = t"
proof -
  have root: "length ts \<noteq> A f \<Longrightarrow> (\<forall>g us. logic_subtree (LFun g us) (LFun f ts) \<longrightarrow>
      length us \<noteq> A g \<longrightarrow> gamma (b (LFun g us)) = LFun g us) \<Longrightarrow>
      gamma (b (LFun f ts)) = LFun f ts" for f ts
    by (blast intro: logic_subtree.root)
  show ?thesis using bad
    by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
      (case_tac t; auto simp: vars list_all2_map1 list_all2_same
        intro: logic_subtree.root logic_subtree.child;
        drule (1) root; simp add: list_all2_same)
qed

ML \<open>
  val results = @{thms logic_arity_abstract_correct logic_arity_abstract_subst logic_arity_abstract_recover}
  val _ = if Thm_Deps.has_skip_proof results then error "MGU abstraction: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "MGU abstraction: oracle dependency"
\<close>
end
