theory LP_MGU_Abstraction_Names
  imports LP_Tree_Countability
begin

lemma logic_countable_string_names:
  assumes "countable X"
  obtains e :: "'a \<Rightarrow> string" where "inj_on e X"
proof -
  obtain h :: "'a \<Rightarrow> nat" where h: "inj_on h X" using assms by (rule countableE)
  let ?e = "\<lambda>x. replicate (h x) (CHR ''a'')"
  have "inj_on ?e X"
    using h by (auto simp: inj_on_def dest: arg_cong[where f=length])
  then show thesis by (rule that)
qed

lemma logic_substitution_abstraction_names:
  fixes s :: "string \<Rightarrow> ('f,string) logic_tree"
  assumes sd: "logic_substitution_in D s"
    and variables: "\<And>x. D (LVar x)"
    and subtrees: "\<And>u t. D t \<Longrightarrow> logic_subtree u t \<Longrightarrow> D u"
  obtains r b gamma where "logic_substitution_in D gamma"
    "\<And>x. logic_subst gamma (logic_arity_abstract A r b (s x)) = s x"
proof -
  let ?S = "\<Union>x. {u. logic_subtree u (s x)}"
  let ?T = "(Inl ` (UNIV :: string set)) \<union> Inr ` ?S"
  have countable: "countable ?T"
    using countable_logic_substitution_subtrees[of s] by simp
  obtain e :: "(string + ('f,string) logic_tree) \<Rightarrow> string" where inj: "inj_on e ?T"
    by (rule logic_countable_string_names[OF countable]) blast
  let ?decode = "\<lambda>v. case v of Inl x \<Rightarrow> LVar x | Inr t \<Rightarrow> t"
  let ?gamma = "\<lambda>x. if x \<in> e ` ?T then ?decode (inv_into ?T e x) else LVar undefined"
  have recover: "?gamma (e v) = ?decode v" if "v \<in> ?T" for v
    using that inj by (simp add: inv_into_f_f)
  have domain: "D (?decode v)" if "v \<in> ?T" for v
    using that sd variables subtrees
    by (auto simp: logic_substitution_in_def split: sum.splits)
  have gd_point: "D (?gamma x)" for x
  proof (cases "x \<in> e ` ?T")
    case True
    then obtain v where v: "v \<in> ?T" "x = e v" by blast
    show ?thesis using domain[OF v(1)] by (simp only: v(2) recover[OF v(1)])
  next
    case False
    then show ?thesis by (simp add: variables)
  qed
  have gd: "logic_substitution_in D ?gamma"
    using gd_point by (simp add: logic_substitution_in_def)
  have gv: "?gamma (e (Inl x)) = LVar x" for x
    by (subst recover) auto
  have gb: "logic_subtree t (s x) \<Longrightarrow> ?gamma (e (Inr t)) = t" for t x
    by (subst recover) auto
  have restored: "logic_subst ?gamma (logic_arity_abstract A (e \<circ> Inl) (e \<circ> Inr) (s x)) = s x" for x
    apply (rule logic_arity_abstract_recover)
    subgoal for y unfolding o_apply by (rule gv)
    subgoal for f ts unfolding o_apply by (rule gb; assumption)
    done
  show thesis by (rule that[OF gd restored])
qed

ML \<open>
  val results = @{thms logic_countable_string_names logic_substitution_abstraction_names}
  val _ = if Thm_Deps.has_skip_proof results then error "Abstraction names: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Abstraction names: oracle dependency"
\<close>
end
