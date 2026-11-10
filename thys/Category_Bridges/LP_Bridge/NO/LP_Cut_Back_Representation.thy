theory LP_Cut_Back_Representation
  imports LP_Cut_Domain_NO_Certificate
begin

text \<open>The reverse map forgets the internal expansion annotation. Such an
annotation has no execution rule in the witness relation; forgetting it can
only add canonical behaviour. On translated source programs the maps are exact.\<close>
fun cut_goal_back where
  "cut_goal_back f (LPCAtom a) = LogicAtom (f a)"
| "cut_goal_back f (LPCCut m) = LogicCut m"
| "cut_goal_back f LPCTrue = LogicSuccess"
| "cut_goal_back f LPCFail = LogicFailure"
| "cut_goal_back f (LPCMeta a) = LogicMeta (f a)"
| "cut_goal_back f (LPCExpand a m) = LogicMeta (f a)"
| "cut_goal_back f (LPCUnify a b) = LogicUnify (f a) (f b)"
fun cut_choice_back where
  "cut_choice_back f (LPCGoals gs) = LogicGoals (map (cut_goal_back f) gs)"
| "cut_choice_back f (LPCClause gs c m) = LogicClause (map (cut_goal_back f) gs) c m"
| "cut_choice_back f (LPCBarrier m) = LogicBarrier m"
abbreviation cut_state_back where
  "cut_state_back s \<equiv> map (cut_choice_back cut_tree_back) s"
definition cut_program_back where
  "cut_program_back P = map (\<lambda>(h,bs). (cut_term_back h,map (cut_goal_back cut_term_back) bs)) P"
lemma cut_term_back_inverse[simp]: "cut_term_back (cut_term t) = t"
  by (induct t) (auto simp: map_map o_def intro!: map_idI)
lemma cut_goal_back_inverse[simp]: "cut_goal_back f (cut_goal g a) = logic_goal_map (f \<circ> g) a"
  by (cases a) auto
lemma cut_back_goal_term_inverse[simp]:
  "cut_goal_back cut_term_back (cut_goal cut_term g) = g"
  by (cases g) auto
lemma logic_goal_map_identity[simp]: "logic_goal_map (\<lambda>x. x) g = g"
  by (cases g) auto
lemma cut_program_back_inverse[simp]: "cut_program_back (cut_program P) = P"
  unfolding cut_program_back_def cut_program_def
  by (induct P) (auto simp: case_prod_unfold map_map o_def intro!: map_idI)
lemma cut_back_subst:
  "cut_tree_back (lp_isubst t s) = logic_subst (cut_tree_back \<circ> s) (cut_tree_back t)"
  using cut_tree_subst[of "cut_tree_back \<circ> s" "cut_tree_back t"]
  by (metis cut_tree_native_roundtrip cut_tree_roundtrip comp_apply ext)
lemma cut_back_eval:
  "cut_tree_back (lp_ieval t r) = logic_eval (cut_tree_back \<circ> r) (cut_term_back t)"
  by (induct t) (auto simp: map_map o_def)
lemma cut_back_goal_map:
  "cut_goal_back f (lp_cut_map g a) = logic_goal_map h (cut_goal_back k a)"
  if "\<And>t. f (g t) = h (k t)"
  using that by (cases a) auto
lemma cut_back_goal_bind:
  "cut_goal_back f (lp_cut_bind m g a) = logic_bind_cut m h (cut_goal_back k a)"
  if "\<And>t. f (g t) = h (k t)"
  using that by (cases a) auto
lemma cut_back_goal_subst:
  "cut_goal_back cut_tree_back (lp_cut_map (\<lambda>t. lp_isubst t s) g) =
    logic_goal_map (logic_subst (cut_tree_back \<circ> s)) (cut_goal_back cut_tree_back g)"
  by (rule cut_back_goal_map; rule cut_back_subst)
lemma cut_back_goal_eval_bind:
  "cut_goal_back cut_tree_back (lp_cut_bind m (\<lambda>t. lp_ieval t r) g) =
    logic_bind_cut m (logic_eval (cut_tree_back \<circ> r)) (cut_goal_back cut_term_back g)"
  by (rule cut_back_goal_bind; rule cut_back_eval)
lemma cut_back_goal_terms:
  "logic_goal_terms (cut_goal_back f g) = map f (lp_cut_terms g)"
  by (cases g) auto
lemma cut_back_goal_marks:
  "logic_goal_marks (cut_goal_back f g) \<subseteq> lp_cut_goal_scopes g"
  by (cases g) auto
lemma cut_back_choice_marks:
  "logic_choice_marks (cut_choice_back f e) \<subseteq> lp_cut_entry_scopes e"
  by (cases e) (auto dest: cut_back_goal_marks[THEN subsetD])
lemma cut_back_fresh:
  "lp_cut_fresh m es \<Longrightarrow> logic_fresh_mark m (map (cut_choice_back f) es)"
  unfolding lp_cut_fresh_def logic_fresh_mark_def
  by (auto dest: cut_back_choice_marks[THEN subsetD])
lemma cut_back_prune:
  "map (cut_choice_back f) (lp_cut_prune m es) = logic_prune m (map (cut_choice_back f) es)"
  by (induct es) (auto split: lp_cut_entry.splits)
lemma cut_back_admin:
  "lp_cut_admin s = Some t \<Longrightarrow>
   logic_admin (map (cut_choice_back f) s) = Some (map (cut_choice_back f) t)"
  by (induct s rule: lp_cut_admin.induct)
    (auto simp: cut_back_prune split: lp_cut_goal.splits)
lemma cut_back_program_length[simp]: "length (cut_program_back P) = length P"
  by (simp add: cut_program_back_def)
lemma cut_back_program_nth:
  "c<length P \<Longrightarrow> cut_program_back P!c =
   (cut_term_back (fst (P!c)),map (cut_goal_back cut_term_back) (snd (P!c)))"
  by (simp add: cut_program_back_def split: prod.splits)
lemma cut_back_head_shape:
  "(\<exists>ts. cut_term_back h = SFun (LogicUser f) ts \<and> length ts=n) \<longleftrightarrow>
   (\<exists>ts. h = Fun (LPCUser f) ts \<and> length ts=n)"
proof (cases h)
  case (Var x) then show ?thesis by simp
next
  case (Fun g ts) then show ?thesis by (cases g) auto
qed
lemma cut_back_slice:
  "logic_slice (cut_program_back P) f n = lp_cut_slice P (LPCUser f) n"
  unfolding logic_slice_def lp_cut_slice_def
  by (rule filter_cong) (auto simp: cut_back_program_nth cut_back_head_shape)
lemma cut_back_lower:
  "lp_cut_lower m a gs \<Longrightarrow>
   logic_lower m (cut_tree_back a) (map (cut_goal_back cut_tree_back) gs)"
  by (induct rule: lp_cut_lower.induct) (auto intro: logic_lower.intros)

end
