theory LP_MGU_Concrete_Extension
  imports LP_MGU_Abstraction_Domains
begin

lemma logic_finite_function_intro:
  assumes "list_all logic_finite ts"
  shows "logic_finite (LFun f ts)"
proof -
  let ?rep = "\<lambda>t. SOME u. t = logic_embed u"
  have rep: "logic_embed (?rep t) = t" if "t \<in> set ts" for t
    using assms that someI_ex[of "\<lambda>u. t = logic_embed u"]
    by (auto simp: list_all_iff logic_finite_def)
  have mapped: "map logic_embed (map ?rep ts) = ts"
    by (simp add: map_map o_def; rule map_idI; rule rep)
  show ?thesis unfolding logic_finite_def
    by (rule exI[of _ "SFun f (map ?rep ts)"]) (simp only: logic_embed.simps mapped)
qed
lemma logic_finite_arguments:
  "logic_finite (LFun f ts) \<Longrightarrow> list_all logic_finite ts"
proof -
  assume "logic_finite (LFun f ts)"
  then obtain t where "LFun f ts = logic_embed t" unfolding logic_finite_def by blast
  then show ?thesis by (cases t) (auto simp: list_all_iff logic_finite_def)
qed
lemma logic_finite_subtree:
  "logic_subtree u t \<Longrightarrow> logic_finite t \<Longrightarrow> logic_finite u"
  by (induct rule: logic_subtree.induct)
    (auto dest: logic_finite_arguments simp: list_all_iff)
lemma logic_finite_substitution:
  assumes "logic_finite t" "\<And>x. logic_finite (s x)"
  shows "logic_finite (logic_subst s t)"
proof -
  have "logic_finite (logic_subst s (logic_embed u))" for u
    by (induct u) (auto simp: assms(2) list_all_iff intro: logic_finite_function_intro)
  then show ?thesis using assms(1) unfolding logic_finite_def by blast
qed
lemma logic_rational_subtree:
  "logic_subtree u t \<Longrightarrow> logic_rational t \<Longrightarrow> logic_rational u"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "{u. logic_subtree u t}"]) (auto dest: logic_subtree_trans)

lemma logic_finite_mgu_arity_extension:
  fixes s :: "string \<Rightarrow> ('f,string) logic_tree"
  assumes mgu: "logic_mgu (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct A t) a b s"
    and left: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct A) (logic_arguments b)"
  shows "logic_mgu logic_finite a b s"
  by (rule logic_mgu_arity_extension_by_abstraction[OF mgu left right])
    (auto simp: logic_substitution_in_def intro: logic_finite_subtree
      logic_arity_abstract_finite logic_finite_substitution)
lemma logic_rational_mgu_arity_extension:
  fixes s :: "string \<Rightarrow> ('f,string) logic_tree"
  assumes mgu: "logic_mgu (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct A t) a b s"
    and left: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct A) (logic_arguments b)"
  shows "logic_mgu logic_rational a b s"
  by (rule logic_mgu_arity_extension_by_abstraction[OF mgu left right])
    (auto simp: logic_substitution_in_def intro: logic_rational_subtree
      logic_arity_abstract_rational logic_rational_substitution)
lemma logic_infinite_mgu_arity_extension:
  fixes s :: "string \<Rightarrow> ('f,string) logic_tree"
  assumes mgu: "logic_mgu (logic_tree_arity_correct A) a b s"
    and left: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct A) (logic_arguments b)"
  shows "logic_mgu (\<lambda>_. True) a b s"
  by (rule logic_mgu_arity_extension_by_abstraction[where D="\<lambda>_. True", OF _ left right])
    (use mgu in auto)

ML \<open>
  val results = @{thms logic_finite_mgu_arity_extension logic_rational_mgu_arity_extension logic_infinite_mgu_arity_extension}
  val _ = if Thm_Deps.has_skip_proof results then error "Concrete MGU extension: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Concrete MGU extension: oracle dependency"
\<close>
end
