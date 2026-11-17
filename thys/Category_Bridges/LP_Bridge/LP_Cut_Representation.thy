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

fun cut_atom where
  "cut_atom (LAtom f ts) = LPIFun (LPCUser f) (map cut_tree ts)"
fun cut_head where
  "cut_head (LAtom f ts) = Fun (LPCUser f) (map cut_term ts)"
fun cut_goal :: "('p \<Rightarrow> 'b list \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    ('p,'a) logic_goal \<Rightarrow> 'b lp_cut_goal" where
  "cut_goal atom_ctor f (LogicAtom a) = LPCAtom (atom_ctor (logic_predicate a) (map f (logic_arguments a)))"
| "cut_goal atom_ctor f (LogicCut m) = LPCCut m"
| "cut_goal atom_ctor f LogicSuccess = LPCTrue"
| "cut_goal atom_ctor f LogicFailure = LPCFail"
| "cut_goal atom_ctor f (LogicMeta a) = LPCMeta (f a)"
| "cut_goal atom_ctor f (LogicUnify a b) = LPCUnify (f a) (f b)"
fun cut_choice :: "('p \<Rightarrow> 'b list \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    ('p,'a) logic_choice \<Rightarrow> 'b lp_cut_entry" where
  "cut_choice atom_ctor f (LogicGoals gs) = LPCGoals (map (cut_goal atom_ctor f) gs)"
| "cut_choice atom_ctor f (LogicClause gs c m) = LPCClause (map (cut_goal atom_ctor f) gs) c m"
| "cut_choice atom_ctor f (LogicBarrier m) = LPCBarrier m"
abbreviation cut_igoal where
  "cut_igoal \<equiv> cut_goal (\<lambda>p ts. LPIFun (LPCUser p) ts) cut_tree"
abbreviation cut_fgoal where
  "cut_fgoal \<equiv> cut_goal (\<lambda>p ts. Fun (LPCUser p) ts) cut_term"
abbreviation cut_ichoice where
  "cut_ichoice \<equiv> cut_choice (\<lambda>p ts. LPIFun (LPCUser p) ts) cut_tree"
abbreviation cut_state where "cut_state s \<equiv> map cut_ichoice s"
definition cut_program where
  "cut_program P = map (\<lambda>(h,bs). (cut_head h,map cut_fgoal bs)) P"
lemma cut_program_length[simp]: "length (cut_program P) = length P"
  by (simp add: cut_program_def)
lemma cut_program_nth:
  "c<length P \<Longrightarrow> cut_program P!c = (cut_head (fst (P!c)),map cut_fgoal (snd (P!c)))"
  by (simp add: cut_program_def split: prod.splits)
lemma cut_goal_map:
  "cut_goal atom_ctor f (logic_goal_map g a) = lp_cut_map h (cut_goal other_ctor k a)"
  if "\<And>t. f (g t)=h (k t)" "\<And>p ts. atom_ctor p (map h ts) = h (other_ctor p ts)"
proof (cases a)
  case (LogicAtom b)
  show ?thesis using that(2)[of "logic_predicate b" "map k (logic_arguments b)"]
    by (simp add: LogicAtom map_map o_def that(1))
qed (simp_all add: that)
lemma cut_goal_bind:
  "cut_goal atom_ctor f (logic_bind_cut m g a) = lp_cut_bind m h (cut_goal other_ctor k a)"
  if "\<And>t. f (g t)=h (k t)" "\<And>p ts. atom_ctor p (map h ts) = h (other_ctor p ts)"
proof (cases a)
  case (LogicAtom b)
  show ?thesis using that(2)[of "logic_predicate b" "map k (logic_arguments b)"]
    by (simp add: LogicAtom map_map o_def that(1))
qed (simp_all add: that)
lemma cut_goal_subst:
  "cut_igoal (logic_goal_map (logic_subst s) g) =
    lp_cut_map (\<lambda>t. lp_isubst t (cut_tree \<circ> s)) (cut_igoal g)"
  by (cases g) (simp_all add: cut_tree_subst map_map o_def)
lemma cut_goal_eval_bind:
  "cut_igoal (logic_bind_cut m (logic_eval r) g) =
    lp_cut_bind m (\<lambda>t. lp_ieval t (cut_tree \<circ> r)) (cut_fgoal g)"
  by (cases g) (simp_all add: cut_tree_eval map_map o_def)
lemma cut_goal_scopes[simp]:
  "lp_cut_goal_scopes (cut_goal atom_ctor f g) = logic_goal_marks g"
  by (cases g) auto
lemma cut_choice_scopes[simp]:
  "lp_cut_entry_scopes (cut_choice atom_ctor f e) = logic_choice_marks e"
  by (cases e) (auto simp: image_image)
lemma cut_fresh[simp]:
  "lp_cut_fresh m (map (cut_choice atom_ctor f) es) = logic_fresh_mark m es"
  by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
lemma cut_prune:
  "map (cut_choice atom_ctor f) (logic_prune m es) = lp_cut_prune m (map (cut_choice atom_ctor f) es)"
  by (induct es) (auto split: logic_choice.splits)
lemma cut_admin:
  "lp_cut_admin (map (cut_choice atom_ctor f) s) = map_option (map (cut_choice atom_ctor f)) (logic_admin s)"
  by (induct s rule: logic_admin.induct)
    (auto simp: cut_prune split: logic_goal.splits)
lemma cut_head_shape:
  "(\<exists>ts. cut_head h = Fun (LPCUser f) ts \<and> length ts=n) \<longleftrightarrow>
    logic_predicate h = f \<and> length (logic_arguments h) = n"
  by (cases h) auto
lemma cut_slice:
  "lp_cut_slice (cut_program P) (LPCUser f) n = logic_slice P f n"
  unfolding lp_cut_slice_def logic_slice_def
  by (rule filter_cong) (auto simp: cut_program_nth cut_head_shape)
lemma cut_lower:
  "logic_lower m a bs \<Longrightarrow>
    lp_cut_lower m (cut_tree a) (map (cut_igoal) bs)"
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

end
