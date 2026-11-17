theory LP_MGU_Abstraction_Domains
  imports LP_MGU_Arity_Extension
begin

fun logic_arity_abstract_term ::
  "'f arity \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> (('f,'v) logic_tree \<Rightarrow> 'w) \<Rightarrow>
    ('f,'v) fo_term \<Rightarrow> ('f,'w) fo_term" where
  "logic_arity_abstract_term A r b (SVar x) = SVar (r x)"
| "logic_arity_abstract_term A r b (SFun f ts) = (if length ts = A f then
    SFun f (map (logic_arity_abstract_term A r b) ts) else SVar (b (logic_embed (SFun f ts))))"
lemma logic_arity_abstract_embed:
  "logic_arity_abstract A r b (logic_embed t) = logic_embed (logic_arity_abstract_term A r b t)"
  by (induct t) (auto simp: map_map o_def)
lemma logic_arity_abstract_finite:
  "logic_finite t \<Longrightarrow> logic_finite (logic_arity_abstract A r b t)"
  by (auto simp: logic_finite_def logic_arity_abstract_embed)

lemma logic_arity_abstract_subtree:
  assumes "logic_subtree u (logic_arity_abstract A r b t)"
  shows "\<exists>v. u=logic_arity_abstract A r b v \<and> logic_subtree v t"
  using assms
proof (induct u "logic_arity_abstract A r b t" arbitrary: t rule: logic_subtree.induct)
  case root
  then show ?case by (auto intro: logic_subtree.root)
next
  case (child u ts v f)
  show ?case
  proof (cases t)
    case (LVar x)
    then show ?thesis using child by simp
  next
    case (LFun g vs)
    have len: "length vs = A g" using child LFun by (auto split: if_splits)
    obtain w where w: "w\<in>set vs" "u=logic_arity_abstract A r b w"
      using child LFun len by auto
    obtain q where q: "v=logic_arity_abstract A r b q" "logic_subtree q w"
      using child.hyps(3)[OF w(2)] by blast
    show ?thesis using q w(1) by (auto simp: LFun intro: logic_subtree.child)
  qed
qed
lemma logic_arity_abstract_rational:
  "logic_rational t \<Longrightarrow> logic_rational (logic_arity_abstract A r b t)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "logic_arity_abstract A r b ` {u. logic_subtree u t}"])
    (auto dest: logic_arity_abstract_subtree)


ML \<open>
  val results = @{thms logic_arity_abstract_finite logic_arity_abstract_rational}
  val _ = if Thm_Deps.has_skip_proof results then error "Abstraction domains: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Abstraction domains: oracle dependency"
\<close>
end
