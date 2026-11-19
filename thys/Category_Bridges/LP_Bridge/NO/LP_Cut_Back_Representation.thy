theory LP_Cut_Back_Representation
  imports Category_LP_Bridge.LP_Cut_MGU_Representation
    Category_LP_Bridge.LP_Cut_Finite_Unification
begin

text \<open>Ordinary predicate goals decode only from user-headed applications.
The auxiliary decoders are total. Roundtrip and substitution proofs use only
user-headed atom applications, guarded by explicit shape predicates.
Meta-call and unification operands remain terms.\<close>
fun cut_iatom_shape :: "('f lp_cut_symbol,'v) lp_iterm \<Rightarrow> bool" where
  "cut_iatom_shape (LPIFun (LPCUser f) ts) = True"
| "cut_iatom_shape t = False"
fun cut_fatom_shape :: "('f lp_cut_symbol,'v) term \<Rightarrow> bool" where
  "cut_fatom_shape (Fun (LPCUser f) ts) = True"
| "cut_fatom_shape t = False"
fun cut_iatom_back ::
  "('f lp_cut_symbol,'v) lp_iterm \<Rightarrow> ('f,('f logic_symbol,'v) logic_tree) logic_atom" where
  "cut_iatom_back (LPIFun (LPCUser f) ts) = LAtom f (map cut_tree_back ts)"
| "cut_iatom_back t = LAtom undefined []"
fun cut_fatom_back ::
  "('f lp_cut_symbol,'v) term \<Rightarrow> ('f,('f logic_symbol,'v) fo_term) logic_atom" where
  "cut_fatom_back (Fun (LPCUser f) ts) = LAtom f (map cut_term_back ts)"
| "cut_fatom_back t = LAtom undefined []"
fun cut_goal_shape :: "('t \<Rightarrow> bool) \<Rightarrow> 't lp_cut_goal \<Rightarrow> bool" where
  "cut_goal_shape atom_ok (LPCAtom a) = atom_ok a"
| "cut_goal_shape atom_ok (LPCExpand a m) = False"
| "cut_goal_shape atom_ok g = True"
fun cut_choice_shape :: "('t \<Rightarrow> bool) \<Rightarrow> 't lp_cut_entry \<Rightarrow> bool" where
  "cut_choice_shape atom_ok (LPCGoals gs) = list_all (cut_goal_shape atom_ok) gs"
| "cut_choice_shape atom_ok (LPCClause gs c m) = list_all (cut_goal_shape atom_ok) gs"
| "cut_choice_shape atom_ok (LPCBarrier m) = True"

fun cut_goal_back ::
  "('s \<Rightarrow> ('p,'t) logic_atom) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> 's lp_cut_goal \<Rightarrow> ('p,'t) logic_goal" where
  "cut_goal_back atom_back f (LPCAtom a) = LogicAtom (atom_back a)"
| "cut_goal_back atom_back f (LPCCut m) = LogicCut m"
| "cut_goal_back atom_back f LPCTrue = LogicSuccess"
| "cut_goal_back atom_back f LPCFail = LogicFailure"
| "cut_goal_back atom_back f (LPCMeta a) = LogicMeta (f a)"
| "cut_goal_back atom_back f (LPCExpand a m) = LogicMeta (f a)"
| "cut_goal_back atom_back f (LPCUnify a b) = LogicUnify (f a) (f b)"
fun cut_choice_back ::
  "('s \<Rightarrow> ('p,'t) logic_atom) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> 's lp_cut_entry \<Rightarrow> ('p,'t) logic_choice" where
  "cut_choice_back atom_back f (LPCGoals gs) = LogicGoals (map (cut_goal_back atom_back f) gs)"
| "cut_choice_back atom_back f (LPCClause gs c m) = LogicClause (map (cut_goal_back atom_back f) gs) c m"
| "cut_choice_back atom_back f (LPCBarrier m) = LogicBarrier m"
abbreviation cut_igoal_back where "cut_igoal_back \<equiv> cut_goal_back cut_iatom_back cut_tree_back"
abbreviation cut_fgoal_back where "cut_fgoal_back \<equiv> cut_goal_back cut_fatom_back cut_term_back"
abbreviation cut_ichoice_back where "cut_ichoice_back \<equiv> cut_choice_back cut_iatom_back cut_tree_back"
abbreviation cut_state_back where "cut_state_back s \<equiv> map cut_ichoice_back s"
definition cut_program_back :: "('f,'v) lp_cut_program \<Rightarrow> ('f,'v) logic_cut_program" where
  "cut_program_back P = map (\<lambda>(h,bs). (cut_fatom_back h,map cut_fgoal_back bs)) P"

lemma cut_term_back_inverse[simp]: "cut_term_back (cut_term t) = t"
  by (induct t) (auto simp: map_map o_def intro!: map_idI)
lemma cut_iatom_back_inverse[simp]: "cut_iatom_back (cut_atom a) = a"
  by (cases a) (simp add: map_map o_def)
lemma cut_fatom_back_inverse[simp]: "cut_fatom_back (cut_head a) = a"
  by (cases a) (simp add: map_map o_def)
lemma cut_back_goal_term_inverse[simp]: "cut_fgoal_back (cut_fgoal g) = g"
  by (cases g) (simp_all add: map_map o_def split: logic_atom.splits)
lemma cut_back_goal_tree_inverse[simp]: "cut_igoal_back (cut_igoal g) = g"
  by (cases g) (simp_all add: map_map o_def split: logic_atom.splits)
lemma cut_back_choice_inverse[simp]: "cut_ichoice_back (cut_ichoice e) = e"
  by (cases e) (simp_all add: map_map o_def)
lemma cut_back_state_inverse[simp]: "cut_state_back (cut_state s) = s"
  by (simp add: map_map o_def)
lemma cut_program_back_inverse[simp]: "cut_program_back (cut_program P) = P"
  by (simp add: cut_program_back_def cut_program_def map_map o_def split_def)
lemma cut_state_injective[simp]: "cut_state s = cut_state t \<longleftrightarrow> s=t"
  by (metis cut_back_state_inverse)

lemma cut_term_forward_back[simp]: "cut_term (cut_term_back t) = t"
  by (induct t) (auto simp: map_map o_def intro!: map_idI)
lemma cut_iatom_forward_back:
  "cut_iatom_shape a \<Longrightarrow> cut_atom (cut_iatom_back a) = a"
  by (cases a rule: cut_iatom_shape.cases) (simp_all add: map_map o_def)
lemma cut_fatom_forward_back:
  "cut_fatom_shape a \<Longrightarrow> cut_head (cut_fatom_back a) = a"
  by (cases a rule: cut_fatom_shape.cases) (simp_all add: map_map o_def)
lemma cut_atom_selectors:
  "cut_atom a = LPIFun (LPCUser (logic_predicate a)) (map cut_tree (logic_arguments a))"
  by (cases a) simp
lemma cut_head_selectors:
  "cut_head a = Fun (LPCUser (logic_predicate a)) (map cut_term (logic_arguments a))"
  by (cases a) simp
lemma cut_igoal_forward_back:
  "cut_goal_shape cut_iatom_shape g \<Longrightarrow> cut_igoal (cut_igoal_back g) = g"
  by (cases g) (simp_all add: cut_atom_selectors[symmetric] cut_iatom_forward_back)
lemma cut_fgoal_forward_back:
  "cut_goal_shape cut_fatom_shape g \<Longrightarrow> cut_fgoal (cut_fgoal_back g) = g"
  by (cases g) (simp_all add: cut_head_selectors[symmetric] cut_fatom_forward_back)
lemma cut_ichoice_forward_back:
  "cut_choice_shape cut_iatom_shape e \<Longrightarrow> cut_ichoice (cut_ichoice_back e) = e"
  by (cases e) (auto simp: map_map o_def list_all_iff intro!: map_idI intro: cut_igoal_forward_back)
lemma cut_state_forward_back:
  "list_all (cut_choice_shape cut_iatom_shape) s \<Longrightarrow> cut_state (cut_state_back s) = s"
  by (auto simp: map_map o_def list_all_iff intro!: map_idI intro: cut_ichoice_forward_back)
lemma cut_encoded_goal_shape[simp]:
  "cut_goal_shape cut_iatom_shape (cut_igoal g)"
  by (cases g) simp_all
lemma cut_encoded_fgoal_shape[simp]:
  "cut_goal_shape cut_fatom_shape (cut_fgoal g)"
  by (cases g) simp_all
lemma cut_encoded_choice_shape[simp]:
  "cut_choice_shape cut_iatom_shape (cut_ichoice e)"
  by (cases e) (simp_all add: list_all_iff)
lemma cut_encoded_state_shape:
  "list_all (cut_choice_shape cut_iatom_shape) (cut_state s)"
  by (simp add: list_all_iff)
lemma cut_iatom_subst_shape:
  "cut_iatom_shape a \<Longrightarrow> cut_iatom_shape (lp_isubst a s)"
  by (cases a rule: cut_iatom_shape.cases) simp_all
lemma cut_fatom_eval_shape:
  "cut_fatom_shape a \<Longrightarrow> cut_iatom_shape (lp_ieval a r)"
  by (cases a rule: cut_fatom_shape.cases) simp_all
lemma cut_goal_subst_shape:
  "cut_goal_shape cut_iatom_shape g \<Longrightarrow>
    cut_goal_shape cut_iatom_shape (lp_cut_map (\<lambda>t. lp_isubst t s) g)"
  by (cases g) (simp_all add: cut_iatom_subst_shape)
lemma cut_goal_eval_bind_shape:
  "cut_goal_shape cut_fatom_shape g \<Longrightarrow>
    cut_goal_shape cut_iatom_shape (lp_cut_bind m (\<lambda>t. lp_ieval t r) g)"
  by (cases g) (simp_all add: cut_fatom_eval_shape)
lemma cut_lower_shape:
  "lp_cut_lower m a gs \<Longrightarrow> list_all (cut_goal_shape cut_iatom_shape) gs"
  by (induct rule: lp_cut_lower.induct) simp_all
lemma cut_prune_shape:
  "list_all (cut_choice_shape atom_ok) es \<Longrightarrow>
    list_all (cut_choice_shape atom_ok) (lp_cut_prune m es)"
  by (induct es) (auto split: lp_cut_entry.splits)
lemma cut_admin_shape:
  "lp_cut_admin s = Some t \<Longrightarrow> list_all (cut_choice_shape atom_ok) s \<Longrightarrow>
    list_all (cut_choice_shape atom_ok) t"
  by (induct s rule: lp_cut_admin.induct)
    (auto intro: cut_prune_shape split: lp_cut_goal.splits)

lemma cut_back_subst:
  "cut_tree_back (lp_isubst t s) = logic_subst (cut_tree_back \<circ> s) (cut_tree_back t)"
  using cut_tree_subst[of "cut_tree_back \<circ> s" "cut_tree_back t"]
  by (metis cut_tree_native_roundtrip cut_tree_roundtrip comp_apply ext)
lemma cut_back_eval:
  "cut_tree_back (lp_ieval t r) = logic_eval (cut_tree_back \<circ> r) (cut_term_back t)"
  by (induct t) (auto simp: map_map o_def)
lemma cut_back_atom_subst:
  "cut_iatom_shape a \<Longrightarrow> cut_iatom_back (lp_isubst a s) =
    logic_atom_map (logic_subst (cut_tree_back \<circ> s)) (cut_iatom_back a)"
  by (cases a rule: cut_iatom_shape.cases) (simp_all add: map_map o_def cut_back_subst)
lemma cut_back_atom_eval:
  "cut_fatom_shape a \<Longrightarrow> cut_iatom_back (lp_ieval a s) =
    logic_atom_map (logic_eval (cut_tree_back \<circ> s)) (cut_fatom_back a)"
  by (cases a rule: cut_fatom_shape.cases) (simp_all add: map_map o_def cut_back_eval)
lemma cut_back_goal_subst:
  "cut_goal_shape cut_iatom_shape g \<Longrightarrow>
    cut_igoal_back (lp_cut_map (\<lambda>t. lp_isubst t s) g) =
      logic_goal_map (logic_subst (cut_tree_back \<circ> s)) (cut_igoal_back g)"
  by (cases g) (simp_all add: cut_back_atom_subst cut_back_subst)
lemma cut_back_goal_eval_bind:
  "cut_goal_shape cut_fatom_shape g \<Longrightarrow>
    cut_igoal_back (lp_cut_bind m (\<lambda>t. lp_ieval t r) g) =
      logic_bind_cut m (logic_eval (cut_tree_back \<circ> r)) (cut_fgoal_back g)"
  by (cases g) (simp_all add: cut_back_atom_eval cut_back_eval)

lemma cut_back_goal_marks:
  "logic_goal_marks (cut_goal_back atom_back f g) \<subseteq> lp_cut_goal_scopes g"
  by (cases g) auto
lemma cut_back_choice_marks:
  "logic_choice_marks (cut_choice_back atom_back f e) \<subseteq> lp_cut_entry_scopes e"
  by (cases e) (auto dest: cut_back_goal_marks[THEN subsetD])
lemma cut_back_fresh:
  "lp_cut_fresh m es \<Longrightarrow> logic_fresh_mark m (map (cut_choice_back atom_back f) es)"
  unfolding lp_cut_fresh_def logic_fresh_mark_def
  by (auto dest: cut_back_choice_marks[THEN subsetD])
lemma cut_back_prune:
  "map (cut_choice_back atom_back f) (lp_cut_prune m es) =
    logic_prune m (map (cut_choice_back atom_back f) es)"
  by (induct es) (auto split: lp_cut_entry.splits)
lemma cut_back_admin:
  "lp_cut_admin s = Some t \<Longrightarrow>
    logic_admin (map (cut_choice_back atom_back f) s) = Some (map (cut_choice_back atom_back f) t)"
  by (induct s rule: lp_cut_admin.induct)
    (auto simp: cut_back_prune split: lp_cut_goal.splits)
lemma cut_back_lower:
  "lp_cut_lower m a gs \<Longrightarrow>
    logic_lower m (cut_tree_back a) (map cut_igoal_back gs)"
  by (induct rule: lp_cut_lower.induct) (auto intro: logic_lower.intros)

end
