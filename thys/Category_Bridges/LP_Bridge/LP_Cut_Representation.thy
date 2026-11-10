theory LP_Cut_Representation
  imports LP_Representation Category_Specifications.LP_Cut_Infinite_Spec Category_LP_Library.LP_Cut_Source
begin

text \<open>The representation map keeps user symbols distinct from control
symbols, and preserves clause order, saved alternatives and invocation scopes.\<close>
fun cut_symbol where
  "cut_symbol (LogicUser f) = LPCUser f"
| "cut_symbol LogicBang = LPCBang"
| "cut_symbol LogicComma = LPCComma"
| "cut_symbol LogicEquals = LPCEquals"
| "cut_symbol LogicTrue = LPCTruth"
| "cut_symbol LogicFail = LPCFailure"
| "cut_symbol LogicCall = LPCCallSymbol"
fun cut_symbol_back where
  "cut_symbol_back (LPCUser f) = LogicUser f"
| "cut_symbol_back LPCBang = LogicBang"
| "cut_symbol_back LPCComma = LogicComma"
| "cut_symbol_back LPCEquals = LogicEquals"
| "cut_symbol_back LPCTruth = LogicTrue"
| "cut_symbol_back LPCFailure = LogicFail"
| "cut_symbol_back LPCCallSymbol = LogicCall"
lemma cut_symbol_inverse[simp]:
  "cut_symbol_back (cut_symbol f) = f" "cut_symbol (cut_symbol_back g) = g"
  by (cases f; simp; fail | cases g; simp)+

primcorec cut_tree where
  "cut_tree t = (case t of LVar x \<Rightarrow> LPIVar x
    | LFun f ts \<Rightarrow> LPIFun (cut_symbol f) (map cut_tree ts))"
primcorec cut_tree_back where
  "cut_tree_back t = (case t of LPIVar x \<Rightarrow> LVar x
    | LPIFun f ts \<Rightarrow> LFun (cut_symbol_back f) (map cut_tree_back ts))"
lemma cut_tree_simps[simp]:
  "cut_tree (LVar x) = LPIVar x"
  "cut_tree (LFun f ts) = LPIFun (cut_symbol f) (map cut_tree ts)"
  by (subst cut_tree.code; simp)+
lemma cut_tree_back_simps[simp]:
  "cut_tree_back (LPIVar x) = LVar x"
  "cut_tree_back (LPIFun f ts) = LFun (cut_symbol_back f) (map cut_tree_back ts)"
  by (subst cut_tree_back.code; simp)+
lemma cut_tree_roundtrip[simp]: "cut_tree_back (cut_tree t) = t"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all2_map1 list.rel_refl)
lemma cut_tree_native_roundtrip[simp]: "cut_tree (cut_tree_back t) = t"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all2_map1 list.rel_refl)
lemma cut_tree_injective[simp]: "cut_tree s = cut_tree t \<longleftrightarrow> s=t"
  by (metis cut_tree_roundtrip)
lemma cut_tree_subst:
  "cut_tree (logic_subst s t) = lp_isubst (cut_tree t) (cut_tree \<circ> s)"
  by (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl)
fun cut_term where
  "cut_term (SVar x) = Var x"
| "cut_term (SFun f ts) = Fun (cut_symbol f) (map cut_term ts)"
lemma cut_tree_eval:
  "cut_tree (logic_eval r t) = lp_ieval (cut_term t) (cut_tree \<circ> r)"
  by (induct t) (auto simp: map_map o_def)
lemma cut_tree_embed:
  "cut_tree (logic_embed t) = lp_ieval (cut_term t) LPIVar"
  by (induct t) (auto simp: map_map o_def)
lemma cut_term_ground: "logic_ground t \<longleftrightarrow> ground (cut_term t)"
  by (induct t) (auto simp: list_all_iff)

fun cut_goal where
  "cut_goal f (LogicAtom a) = LPCAtom (f a)"
| "cut_goal f (LogicCut m) = LPCCut m"
| "cut_goal f LogicSuccess = LPCTrue"
| "cut_goal f LogicFailure = LPCFail"
| "cut_goal f (LogicMeta a) = LPCMeta (f a)"
| "cut_goal f (LogicUnify a b) = LPCUnify (f a) (f b)"
fun cut_choice where
  "cut_choice f (LogicGoals gs) = LPCGoals (map (cut_goal f) gs)"
| "cut_choice f (LogicClause gs c m) = LPCClause (map (cut_goal f) gs) c m"
| "cut_choice f (LogicBarrier m) = LPCBarrier m"
abbreviation cut_state where "cut_state s \<equiv> map (cut_choice cut_tree) s"
definition cut_program where
  "cut_program P = map (\<lambda>(h,bs). (cut_term h,map (cut_goal cut_term) bs)) P"
lemma cut_program_length[simp]: "length (cut_program P) = length P"
  by (simp add: cut_program_def)
lemma cut_program_nth:
  "c<length P \<Longrightarrow> cut_program P!c = (cut_term (fst (P!c)),map (cut_goal cut_term) (snd (P!c)))"
  by (simp add: cut_program_def split: prod.splits)
lemma cut_goal_map:
  "cut_goal f (logic_goal_map g a) = lp_cut_map h (cut_goal k a)"
  if "\<And>t. f (g t)=h (k t)"
  using that by (cases a) auto
lemma cut_goal_bind:
  "cut_goal f (logic_bind_cut m g a) = lp_cut_bind m h (cut_goal k a)"
  if "\<And>t. f (g t)=h (k t)"
  using that by (cases a) auto
lemma cut_goal_subst:
  "cut_goal cut_tree (logic_goal_map (logic_subst s) g) =
    lp_cut_map (\<lambda>t. lp_isubst t (cut_tree \<circ> s)) (cut_goal cut_tree g)"
  by (cases g) (simp_all add: cut_tree_subst)
lemma cut_goal_eval_bind:
  "cut_goal cut_tree (logic_bind_cut m (logic_eval r) g) =
    lp_cut_bind m (\<lambda>t. lp_ieval t (cut_tree \<circ> r)) (cut_goal cut_term g)"
  by (cases g) (simp_all add: cut_tree_eval)
lemma cut_goal_scopes[simp]:
  "lp_cut_goal_scopes (cut_goal f g) = logic_goal_marks g"
  by (cases g) auto
lemma cut_choice_scopes[simp]:
  "lp_cut_entry_scopes (cut_choice f e) = logic_choice_marks e"
  by (cases e) (auto simp: image_image)
lemma cut_fresh[simp]:
  "lp_cut_fresh m (map (cut_choice f) es) = logic_fresh_mark m es"
  by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
lemma cut_prune:
  "map (cut_choice f) (logic_prune m es) = lp_cut_prune m (map (cut_choice f) es)"
  by (induct es) (auto split: logic_choice.splits)
lemma cut_admin:
  "lp_cut_admin (map (cut_choice f) s) = map_option (map (cut_choice f)) (logic_admin s)"
  by (induct s rule: logic_admin.induct)
    (auto simp: cut_prune split: logic_goal.splits)
lemma cut_head_shape:
  "(\<exists>ts. cut_term h = Fun (LPCUser f) ts \<and> length ts=n) \<longleftrightarrow>
    (\<exists>ts. h = SFun (LogicUser f) ts \<and> length ts=n)"
  proof (cases h)
  case (SVar x) then show ?thesis by simp
next
  case (SFun g ts) then show ?thesis by (cases g) auto
qed
lemma cut_slice:
  "lp_cut_slice (cut_program P) (LPCUser f) n = logic_slice P f n"
  unfolding lp_cut_slice_def logic_slice_def
  by (rule filter_cong) (auto simp: cut_program_nth cut_head_shape)
lemma cut_lower:
  "logic_lower m a bs \<Longrightarrow>
    lp_cut_lower m (cut_tree a) (map (cut_goal cut_tree) bs)"
  by (induct rule: logic_lower.induct) (auto intro: lp_cut_lower.intros)
lemma cut_lower_reflect:
  "lp_cut_lower m t bs \<Longrightarrow>
    \<exists>gs. logic_lower m (cut_tree_back t) gs"
  by (induct rule: lp_cut_lower.induct) (auto intro: logic_lower.intros)
lemma logic_lower_not_diverges:
  "logic_lower m a bs \<Longrightarrow> \<not> logic_lower_diverges a"
  by (induct rule: logic_lower.induct)
    (auto elim: logic_lower_diverges.cases)
lemma cut_diverges_unlowerable:
  "logic_lower_diverges a \<Longrightarrow> \<not>(\<exists>m bs. lp_cut_lower m (cut_tree a) bs)"
  using cut_lower_reflect logic_lower_not_diverges by fastforce

lemma cut_unifiable_iff:
  fixes a :: "'f logic_symbol logic_tree"
  shows "(\<exists>s :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>r. lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r) \<longleftrightarrow>
    (\<exists>s r. logic_subst s a = logic_eval r h)"
proof
  assume "\<exists>s :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>r. lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r"
  then obtain s r :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm" where eq: "lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r" by blast
  have "cut_tree (logic_subst (cut_tree_back \<circ> s) a) =
    cut_tree (logic_eval (cut_tree_back \<circ> r) h)"
    using eq by (simp add: cut_tree_subst cut_tree_eval o_def)
  then show "\<exists>s r. logic_subst s a = logic_eval r h" by (simp; blast)
next
  assume "\<exists>s r. logic_subst s a = logic_eval r h"
  then obtain s r where "logic_subst s a = logic_eval r h" by blast
  then have "lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_ieval (cut_term h) (cut_tree \<circ> r)"
    by (metis cut_tree_subst cut_tree_eval)
  then show "\<exists>s :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>r. lp_isubst (cut_tree a) s = lp_ieval (cut_term h) r" by blast
qed
lemma cut_equalizable_iff:
  fixes a :: "'f logic_symbol logic_tree"
  shows "(\<exists>s :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s) \<longleftrightarrow>
    (\<exists>s. logic_subst s a = logic_subst s b)"
proof
  assume "\<exists>s :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s"
  then obtain s :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm" where eq: "lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s" by blast
  have "cut_tree (logic_subst (cut_tree_back \<circ> s) a) = cut_tree (logic_subst (cut_tree_back \<circ> s) b)"
    using eq by (simp add: cut_tree_subst o_def)
  then show "\<exists>s. logic_subst s a = logic_subst s b" by (simp; blast)
next
  assume "\<exists>s. logic_subst s a = logic_subst s b"
  then obtain s where "logic_subst s a = logic_subst s b" by blast
  then have "lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_isubst (cut_tree b) (cut_tree \<circ> s)"
    by (metis cut_tree_subst)
  then show "\<exists>s :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s" by blast
qed


text \<open>The unrestricted-tree execution is simulated by the existing
termination overapproximation. No finite-domain transfer is asserted here:
failed finite unification can enable alternatives removed by a later cut in
the infinite-tree execution.\<close>
lemma cut_infinite_step_native:
  fixes P :: "'a logic_cut_program"
  assumes "logic_cut_step (\<lambda>_. True) P s t"
  shows "(cut_state s,cut_state t) \<in> lp_cut_source (cut_program P)"
  using assms
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: lp_cut_source.admin simp: cut_admin)
next
  case (case_call m f ts gs es)
  then show ?thesis
    using lp_cut_source.case_call[of m f "map cut_tree ts" "map (cut_goal cut_tree) gs"
      "cut_state es" "cut_program P"]
    by (simp add: cut_slice map_map o_def lp_cut_fresh_def logic_fresh_mark_def image_image)
next
  case (resolve c a gs sigma rho m es)
  have index: "c<length (cut_program P)" using resolve by simp
  have eq: "logic_subst sigma a = logic_eval rho (fst (P!c))"
    using resolve by (auto simp: logic_cut_mgu_def logic_mgu_def logic_atom_map_def)
  have native_eq: "lp_isubst (cut_tree a) (cut_tree \<circ> sigma) =
    lp_ieval (fst (cut_program P!c)) (cut_tree \<circ> rho)"
    using arg_cong[OF eq, of cut_tree] index
    by (simp add: cut_program_nth cut_tree_subst cut_tree_eval)
  show ?thesis
    using lp_cut_source.resolve[OF index native_eq, where m=m and
      gs="map (cut_goal cut_tree) gs" and es="cut_state es"] resolve
    by (simp add: cut_program_nth map_map o_def
      cut_goal_subst cut_goal_eval_bind)
next
  case (backtrack c a gs m)
  have index: "c<length (cut_program P)" using backtrack by simp
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm. \<exists>rho.
    lp_isubst (cut_tree a) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    using backtrack by (simp add: cut_program_nth cut_unifiable_iff logic_substitution_def)
  show ?thesis using lp_cut_source.backtrack[OF index failure,
    where gs="map (cut_goal cut_tree) gs" and m=m and es="cut_state t"] backtrack by simp
next
  case (unify a b gs sigma es)
  have eq: "logic_subst sigma a = logic_subst sigma b"
    using unify by (auto simp: logic_unify_mgu_def)
  have native_eq: "lp_isubst (cut_tree a) (cut_tree \<circ> sigma) =
    lp_isubst (cut_tree b) (cut_tree \<circ> sigma)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
  show ?thesis using lp_cut_source.unify[OF native_eq,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] unify
    by (simp add: map_map o_def cut_goal_subst)
next
  case (unify_fail a b gs)
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm.
    lp_isubst (cut_tree a) sigma = lp_isubst (cut_tree b) sigma)"
    using unify_fail by (simp add: cut_equalizable_iff logic_substitution_def)
  show ?thesis using lp_cut_source.unify_fail[OF failure,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
  have lower: "lp_cut_lower m (cut_tree (LFun f ts)) (map (cut_goal cut_tree) body)"
    by (rule cut_lower) (use meta in blast)
  show ?thesis using lp_cut_source.meta[OF _ lower,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree a) body)"
    by (rule cut_diverges_unlowerable) (use meta_diverges in blast)
  show ?thesis using lp_cut_source.meta_unlowerable[OF failure,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] meta_diverges
    by simp
qed

theorem cut_native_termination:
  assumes native: "\<And>ts. logic_query (LogicUser p) modes (LogicUser p,ts) \<Longrightarrow>
    SN_on (lp_cut_source (cut_program P))
      {cut_state [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]}"
  shows "lp_cut_infinite_terminates P p modes"
proof (unfold lp_cut_infinite_terminates_def logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (LogicUser p) modes (LogicUser p,ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step (\<lambda>_. True) P (s n) (s (Suc n))"
  have chain: "\<forall>n. ((cut_state \<circ> s) n,(cut_state \<circ> s) (Suc n))
    \<in> lp_cut_source (cut_program P)"
    by (simp only: o_apply; intro allI; rule cut_infinite_step_native; rule spec[OF steps])
  have bad: "\<exists>f. f 0 \<in> {cut_state [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]}
    \<and> (\<forall>n. (f n,f (Suc n)) \<in> lp_cut_source (cut_program P))"
    by (rule exI[of _ "cut_state \<circ> s"], rule conjI)
      (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

end
