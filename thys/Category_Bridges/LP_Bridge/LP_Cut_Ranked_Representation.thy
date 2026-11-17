theory LP_Cut_Ranked_Representation
  imports Category_LP_Bridge.LP_Cut_Representation Category_LP_Bridge.LP_Ranked_Representation
begin

text \<open>User names are paired with their argument count at the boundary.
Control symbols retain their dedicated constructors, so malformed control
applications remain malformed and must be rejected by input validation.\<close>
fun cut_rank_symbol :: "'f logic_symbol \<Rightarrow> nat \<Rightarrow> ('f \<times> nat) logic_symbol" where
  "cut_rank_symbol (LogicUser f) n = LogicUser (f,n)"
| "cut_rank_symbol LogicBang n = LogicBang"
| "cut_rank_symbol LogicComma n = LogicComma"
| "cut_rank_symbol LogicEquals n = LogicEquals"
| "cut_rank_symbol LogicTrue n = LogicTrue"
| "cut_rank_symbol LogicFail n = LogicFail"
| "cut_rank_symbol LogicCall n = LogicCall"
fun cut_unrank_symbol :: "('f \<times> nat) logic_symbol \<Rightarrow> 'f logic_symbol" where
  "cut_unrank_symbol (LogicUser f) = LogicUser (fst f)"
| "cut_unrank_symbol LogicBang = LogicBang"
| "cut_unrank_symbol LogicComma = LogicComma"
| "cut_unrank_symbol LogicEquals = LogicEquals"
| "cut_unrank_symbol LogicTrue = LogicTrue"
| "cut_unrank_symbol LogicFail = LogicFail"
| "cut_unrank_symbol LogicCall = LogicCall"
lemma cut_unrank_rank_symbol[simp]: "cut_unrank_symbol (cut_rank_symbol f n) = f"
  by (cases f) simp_all
fun cut_rank_term :: "('f logic_symbol,'v) fo_term \<Rightarrow> (('f \<times> nat) logic_symbol,'v) fo_term" where
  "cut_rank_term (SVar x) = SVar x"
| "cut_rank_term (SFun f ts) = SFun (cut_rank_symbol f (length ts)) (map cut_rank_term ts)"
fun cut_unrank_term :: "(('f \<times> nat) logic_symbol,'v) fo_term \<Rightarrow> ('f logic_symbol,'v) fo_term" where
  "cut_unrank_term (SVar x) = SVar x"
| "cut_unrank_term (SFun f ts) = SFun (cut_unrank_symbol f) (map cut_unrank_term ts)"
lemma cut_unrank_rank_term[simp]: "cut_unrank_term (cut_rank_term t) = t"
  by (induct t) (auto simp: map_map o_def intro!: map_idI)

primcorec cut_rank_tree :: "('f logic_symbol,'v) logic_tree \<Rightarrow> (('f \<times> nat) logic_symbol,'v) logic_tree" where
  "cut_rank_tree t = (case t of LVar x \<Rightarrow> LVar x |
    LFun f ts \<Rightarrow> LFun (cut_rank_symbol f (length ts)) (map cut_rank_tree ts))"
primcorec cut_unrank_tree :: "(('f \<times> nat) logic_symbol,'v) logic_tree \<Rightarrow> ('f logic_symbol,'v) logic_tree" where
  "cut_unrank_tree t = (case t of LVar x \<Rightarrow> LVar x |
    LFun f ts \<Rightarrow> LFun (cut_unrank_symbol f) (map cut_unrank_tree ts))"
lemma cut_rank_tree_simps[simp]:
  "cut_rank_tree (LVar x) = LVar x"
  "cut_rank_tree (LFun f ts) = LFun (cut_rank_symbol f (length ts)) (map cut_rank_tree ts)"
  by (subst cut_rank_tree.code; simp)+
lemma cut_unrank_tree_simps[simp]:
  "cut_unrank_tree (LVar x) = LVar x"
  "cut_unrank_tree (LFun f ts) = LFun (cut_unrank_symbol f) (map cut_unrank_tree ts)"
  by (subst cut_unrank_tree.code; simp)+
lemma cut_unrank_rank_tree[simp]: "cut_unrank_tree (cut_rank_tree t) = t"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all2_map1 intro!: list.rel_refl)
lemma cut_rank_subst:
  "cut_rank_tree (logic_subst s t) = logic_subst (cut_rank_tree \<circ> s) (cut_rank_tree t)"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl)
lemma cut_unrank_subst:
  "cut_unrank_tree (logic_subst s t) = logic_subst (cut_unrank_tree \<circ> s) (cut_unrank_tree t)"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl)
lemma cut_rank_embed: "cut_rank_tree (logic_embed t) = logic_embed (cut_rank_term t)"
  by (induct t) (auto simp: map_map intro!: map_cong)
lemma cut_unrank_embed: "cut_unrank_tree (logic_embed t) = logic_embed (cut_unrank_term t)"
  by (induct t) (auto simp: map_map intro!: map_cong)

fun cut_rank_atom :: "('f,('f logic_symbol,'v) fo_term) logic_atom \<Rightarrow>
    ('f \<times> nat,(('f \<times> nat) logic_symbol,'v) fo_term) logic_atom" where
  "cut_rank_atom (LAtom f ts) = LAtom (f,length ts) (map cut_rank_term ts)"
fun cut_rank_goal :: "('f,('f logic_symbol,'v) fo_term) logic_goal \<Rightarrow>
    ('f \<times> nat,(('f \<times> nat) logic_symbol,'v) fo_term) logic_goal" where
  "cut_rank_goal (LogicAtom a) = LogicAtom (cut_rank_atom a)"
| "cut_rank_goal (LogicMeta t) = LogicMeta (cut_rank_term t)"
| "cut_rank_goal (LogicUnify s t) = LogicUnify (cut_rank_term s) (cut_rank_term t)"
| "cut_rank_goal (LogicCut m) = LogicCut m"
| "cut_rank_goal LogicSuccess = LogicSuccess"
| "cut_rank_goal LogicFailure = LogicFailure"
definition cut_rank_program :: "('f,'v) logic_cut_program \<Rightarrow> ('f \<times> nat,'v) logic_cut_program" where
  "cut_rank_program P = map (\<lambda>(h,bs). (cut_rank_atom h,map cut_rank_goal bs)) P"

text \<open>The finite-term validator reuses the shared arity predicate after
ranking. User-name overloading is accepted; fixed control arities are checked.\<close>
definition cut_control_term :: "('f logic_symbol,'v) fo_term \<Rightarrow> bool" where
  "cut_control_term t \<longleftrightarrow> arity_correct (logic_symbol_arity snd) (cut_rank_term t)"
definition cut_control_program :: "('f,'v) logic_cut_program \<Rightarrow> bool" where
  "cut_control_program P \<longleftrightarrow> (\<forall>(h,bs)\<in>set P.
    list_all cut_control_term (logic_arguments h) \<and>
    list_all (\<lambda>g. list_all cut_control_term (logic_goal_terms g)) bs)"
lemma cut_rank_atom_correct:
  "logic_atom_correct snd (arity_correct (logic_symbol_arity snd)) (cut_rank_atom a) =
    list_all cut_control_term (logic_arguments a)"
  by (cases a) (simp add: cut_control_term_def list_all_iff)
lemma cut_rank_goal_correct:
  "logic_goal_correct snd (cut_rank_goal g) = list_all cut_control_term (logic_goal_terms g)"
  by (cases g) (simp_all add: cut_rank_atom_correct cut_control_term_def)
lemma cut_rank_problem:
  "logic_cut_problem snd (cut_rank_program P) (q,length modes) modes = cut_control_program P"
  by (auto simp: logic_cut_problem_def cut_rank_program_def cut_control_program_def
    cut_rank_atom_correct cut_rank_goal_correct list_all_iff case_prod_unfold)


lemma cut_rank_unrank_symbol:
  "n = logic_symbol_arity snd f \<Longrightarrow> cut_rank_symbol (cut_unrank_symbol f) n = f"
  by (cases f) (auto split: prod.splits)
lemma cut_rank_unrank_tree:
  "logic_tree_arity_correct (logic_symbol_arity snd) t \<Longrightarrow>
    cut_rank_tree (cut_unrank_tree t) = t"
  by (coinduction arbitrary: t)
    (case_tac t; auto simp: list_all_iff list_all2_map1 list_all2_same cut_rank_unrank_symbol)
lemma cut_rank_finite:
  "logic_finite (cut_rank_tree t) \<longleftrightarrow> logic_finite t"
proof
  assume "logic_finite (cut_rank_tree t)"
  then obtain u where "cut_rank_tree t = logic_embed u" by (auto simp: logic_finite_def)
  then have "t = logic_embed (cut_unrank_term u)"
    by (metis cut_unrank_rank_tree cut_unrank_embed)
  then show "logic_finite t" by (auto simp: logic_finite_def)
next
  assume "logic_finite t"
  then show "logic_finite (cut_rank_tree t)" by (auto simp: logic_finite_def cut_rank_embed)
qed


lemma logic_relabel_subtree:
  fixes F :: "('f,'v) logic_tree \<Rightarrow> ('g,'v) logic_tree"
  assumes variable: "\<And>x. F (LVar x) = LVar x"
    and application: "\<And>f ts. F (LFun f ts) = LFun (k f (length ts)) (map F ts)"
    and subtree: "logic_subtree u (F t)"
  shows "\<exists>v. u = F v \<and> logic_subtree v t"
  using subtree
proof (induct u "F t" arbitrary: t rule: logic_subtree.induct)
  case root then show ?case by (auto intro: logic_subtree.root)
next
  case (child u ts v f)
  show ?case
  proof (cases t)
    case (LVar x) then show ?thesis using child by (simp add: variable)
  next
    case (LFun g vs)
    obtain w where w: "w\<in>set vs" "u=F w"
      using child by (auto simp: LFun application)
    obtain z where z: "v=F z" "logic_subtree z w"
      using child.hyps(3)[OF w(2)] by blast
    show ?thesis using z w(1) by (auto simp: LFun intro: logic_subtree.child)
  qed
qed
lemma logic_relabel_rational:
  fixes F :: "('f,'v) logic_tree \<Rightarrow> ('g,'v) logic_tree"
  assumes variable: "\<And>x. F (LVar x) = LVar x"
    and application: "\<And>f ts. F (LFun f ts) = LFun (k f (length ts)) (map F ts)"
    and rational: "logic_rational t"
  shows "logic_rational (F t)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "F ` {u. logic_subtree u t}"])
    (use rational logic_relabel_subtree[OF variable application] in \<open>auto simp: logic_rational_def\<close>)
lemma cut_rank_rational_forward:
  "logic_rational t \<Longrightarrow> logic_rational (cut_rank_tree t)"
  by (rule logic_relabel_rational[where k=cut_rank_symbol]) simp_all
lemma cut_unrank_rational:
  "logic_rational t \<Longrightarrow> logic_rational (cut_unrank_tree t)"
  by (rule logic_relabel_rational[where k="\<lambda>f _. cut_unrank_symbol f"]) simp_all
lemma cut_rank_rational:
  "logic_rational (cut_rank_tree t) \<longleftrightarrow> logic_rational t"
  by (metis cut_unrank_rational cut_unrank_rank_tree cut_rank_rational_forward)

text \<open>Overloaded user names remain distinct; control-arity mismatches are
rejected rather than reinterpreted as ordinary predicates. Meta-calls retain
their separate, term-valued representation.\<close>
lemma cut_rank_overloaded_atoms:
  "cut_rank_atom (LAtom p [SVar x]) \<noteq> cut_rank_atom (LAtom p [SVar x,SVar y])"
  by simp
lemma cut_rank_overloaded_terms:
  "cut_control_term (SFun (LogicUser f) [SVar x]) \<and>
    cut_control_term (SFun (LogicUser f) [SVar x,SVar y])"
  by (simp add: cut_control_term_def del: correct_term_iff)
lemma cut_rank_wrong_comma:
  "\<not> cut_control_term (SFun LogicComma [])"
  by (simp add: cut_control_term_def del: correct_term_iff)
lemma cut_rank_meta_call:
  "cut_rank_goal (LogicMeta (SFun LogicCall [SVar x])) = LogicMeta (SFun LogicCall [SVar x])"
  "cut_control_term (SFun LogicCall [SVar x])"
  by (simp_all add: cut_control_term_def del: correct_term_iff)


ML \<open>
  val results = @{thms cut_rank_problem cut_rank_subst cut_rank_unrank_tree cut_rank_finite cut_rank_rational}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut ranked representation: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Cut ranked representation: oracle dependencies: " ^ commas names)
\<close>
end
