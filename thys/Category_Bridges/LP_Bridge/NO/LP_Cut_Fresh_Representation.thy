theory LP_Cut_Fresh_Representation
  imports LP_Cut_Domain_NO_Shape Category_LP_Bridge.LP_Ranked_Representation Category_Properties.LP_Arity_MGU_Properties
begin

text \<open>The atom constructor changes which terms are collected, but not
which variables occur. Freshening therefore uses exactly the same namespaces
on the native and specification sides.\<close>
lemma cut_subtree_forward:
  "logic_subtree u t \<Longrightarrow>
    logic_subtree (logic_from_native (cut_tree u)) (logic_from_native (cut_tree t))"
  by (induct rule: logic_subtree.induct)
    (auto simp: o_def intro: logic_subtree.root intro!: logic_subtree.child[where u="logic_from_native (cut_tree u)" for u])
lemma cut_subtree_backward:
  "logic_subtree u t \<Longrightarrow>
    logic_subtree (cut_tree_back (logic_to_native u)) (cut_tree_back (logic_to_native t))"
  by (induct rule: logic_subtree.induct)
    (auto simp: o_def intro: logic_subtree.root intro!: logic_subtree.child[where u="cut_tree_back (logic_to_native u)" for u])
lemma cut_tree_variables[simp]:
  "lp_runtime_variables (cut_tree t) = logic_variables t"
proof (rule Set.set_eqI)
  fix x
  show "x \<in> lp_runtime_variables (cut_tree t) \<longleftrightarrow> x \<in> logic_variables t"
    unfolding lp_runtime_variables_def logic_variables_def
    using cut_subtree_forward[of "LVar x" t]
      cut_subtree_backward[of "LVar x" "logic_from_native (cut_tree t)"] by auto
qed
lemma cut_term_variables[simp]:
  "vars_term (cut_term t) = logic_variables (logic_embed t)"
  by (induct t) auto
lemma cut_atom_variables[simp]:
  "lp_runtime_variables (cut_atom a) = \<Union>(logic_variables ` set (logic_arguments a))"
  by (cases a) auto
lemma cut_head_variables[simp]:
  "vars_term (cut_head a) = \<Union>((logic_variables \<circ> logic_embed) ` set (logic_arguments a))"
  by (cases a) (auto simp: image_image)
lemma cut_igoal_variables:
  "\<Union>(lp_runtime_variables ` set (lp_cut_terms (cut_igoal g))) =
    \<Union>(logic_variables ` set (logic_goal_terms g))"
  by (cases g) (auto split: logic_atom.splits)
lemma cut_fgoal_variables:
  "\<Union>(vars_term ` set (lp_cut_terms (cut_fgoal g))) =
    \<Union>((logic_variables \<circ> logic_embed) ` set (logic_goal_terms g))"
  by (cases g) (auto simp: image_image split: logic_atom.splits)
lemma cut_freshening_iff:
  "lp_runtime_freshening r
      (cut_atom a # concat (map lp_cut_terms (map cut_igoal gs)))
      (cut_head h # concat (map lp_cut_terms (map cut_fgoal bs))) \<longleftrightarrow>
    logic_freshening r (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments h @ concat (map logic_goal_terms bs))"
proof -
  have flatten: "\<Union>(\<Union>x\<in>X. F x) = (\<Union>x\<in>X. \<Union>(F x))" for X F by blast
  show ?thesis unfolding lp_runtime_freshening_def logic_freshening_def
    by (simp add: Let_def image_UN UN_Un flatten cut_igoal_variables cut_fgoal_variables)
qed

lemma cut_atom_global_mgu:
  "logic_mgu (\<lambda>t. D (cut_tree t)) a b s \<longleftrightarrow>
    lp_runtime_mgu D ((),[cut_atom a]) ((),[cut_atom b]) (cut_tree \<circ> s)"
  by (cases a; cases b)
    (simp add: cut_tree_native.mgu_iff lp_runtime_mgu_def lp_iatom_subst_def)


lemma cut_fresh_resolution_canonical:
  assumes native: "lp_fresh_resolution D (cut_atom a) (map cut_igoal gs)
      (cut_head h) (map cut_fgoal bs) sigma rho"
  shows "\<exists>r. logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments h @ concat (map logic_goal_terms bs)) \<and>
    rho = sigma \<circ> r \<and>
    logic_mgu (\<lambda>t. D (cut_tree t)) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) h) (cut_tree_back \<circ> sigma)"
proof -
  obtain r where fresh: "lp_runtime_freshening r
      (cut_atom a # concat (map lp_cut_terms (map cut_igoal gs)))
      (cut_head h # concat (map lp_cut_terms (map cut_fgoal bs)))"
    and rho: "rho = sigma \<circ> r"
    and mgu: "lp_runtime_mgu D ((),[cut_atom a])
      ((),[lp_ieval (cut_head h) (LPIVar \<circ> r)]) sigma"
    using native unfolding lp_fresh_resolution_def by blast
  have head: "cut_atom (logic_atom_map (logic_eval (LVar \<circ> r)) h) =
      lp_ieval (cut_head h) (LPIVar \<circ> r)"
    by (simp add: cut_head_eval o_def)
  have canonical: "logic_mgu (\<lambda>t. D (cut_tree t)) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) h) (cut_tree_back \<circ> sigma)"
    using mgu by (simp add: cut_atom_global_mgu head[unfolded o_def] o_def)
  show ?thesis using fresh rho canonical cut_freshening_iff by blast
qed

lemma cut_fresh_resolution_typed:
  assumes native: "lp_fresh_resolution D (cut_atom a) (map cut_igoal gs)
      (cut_head h) (map cut_fgoal bs) sigma rho"
    and caller: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and clause: "list_all (arity_correct A) (logic_arguments h)"
    and projection: "\<And>t. D (cut_tree t) \<Longrightarrow> D (cut_tree (logic_arity_project A z t))"
  shows "\<exists>r. logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments h @ concat (map logic_goal_terms bs)) \<and>
    rho = sigma \<circ> r \<and>
    logic_mgu (\<lambda>t. D (cut_tree t) \<and> logic_tree_arity_correct A t) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) h) (cut_tree_back \<circ> sigma)"
proof -
  obtain r where fresh: "logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments h @ concat (map logic_goal_terms bs))"
    and rho: "rho = sigma \<circ> r"
    and mgu: "logic_mgu (\<lambda>t. D (cut_tree t)) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) h) (cut_tree_back \<circ> sigma)"
    using cut_fresh_resolution_canonical[OF native] by blast
  have renamed: "list_all (logic_tree_arity_correct A)
      (logic_arguments (logic_atom_map (logic_eval (LVar \<circ> r)) h))"
    using clause by (cases h) (auto simp: list_all_iff intro: logic_subst_arity_correct)
  have typed: "logic_mgu (\<lambda>t. D (cut_tree t) \<and> logic_tree_arity_correct A t) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) h) (cut_tree_back \<circ> sigma)"
    by (rule logic_mgu_correct_arity[OF mgu caller renamed projection])
  show ?thesis using fresh rho typed by blast
qed


lemma cut_resolution_step:
  assumes index: "c<length P"
    and native: "lp_fresh_resolution D (cut_atom a) (map cut_igoal gs)
      (cut_head (fst (P!c))) (map cut_fgoal (snd (P!c))) sigma rho"
    and caller: "list_all (logic_tree_arity_correct (logic_symbol_arity A)) (logic_arguments a)"
    and clause: "list_all (arity_correct (logic_symbol_arity A)) (logic_arguments (fst (P!c)))"
    and projection: "\<And>t. D (cut_tree t) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) z t))"
  shows "logic_cut_step A (\<lambda>t. D (cut_tree t)) P
    (LogicClause (LogicAtom a#gs) c m#es)
    (cut_state_back (LPCGoals
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (map cut_fgoal (snd (P!c))) @
       map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map cut_igoal gs)) # cut_state es))"
proof -
  obtain r where fresh: "logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c))))"
    and rho: "rho = sigma \<circ> r"
    and mgu: "logic_mgu (\<lambda>t. D (cut_tree t) \<and> logic_tree_arity_correct (logic_symbol_arity A) t) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) (fst (P!c))) (cut_tree_back \<circ> sigma)"
    using cut_fresh_resolution_typed[OF native caller clause projection] by blast
  have composition: "logic_subst (cut_tree_back \<circ> sigma) \<circ> logic_eval (LVar \<circ> r) =
      logic_eval (cut_tree_back \<circ> rho)"
    by (rule ext) (simp add: logic_subst_composition rho o_def)
  have step: "logic_cut_step A (\<lambda>t. D (cut_tree t)) P
      (LogicClause (LogicAtom a#gs) c m#es)
      (LogicGoals (map (logic_bind_cut m (logic_eval (cut_tree_back \<circ> rho))) (snd (P!c)) @
        map (logic_goal_map (logic_subst (cut_tree_back \<circ> sigma))) gs)#es)"
    using logic_cut_step.resolve[OF index fresh mgu, of m es] by (simp only: composition)
  show ?thesis using step
    by (simp add: map_map o_def cut_back_goal_eval_bind cut_back_goal_subst)
qed


lemma cut_freshening_exists:
  fixes active :: "('f logic_symbol,'v) logic_tree list"
    and clause :: "('f logic_symbol,'v) fo_term list"
  assumes infinite: "infinite (UNIV :: 'v set)"
    and finite: "\<And>t. t\<in>set active \<Longrightarrow> finite (logic_variables t)"
  shows "\<exists>r. logic_freshening r active clause"
proof -
  have caller: "finite (\<Union>(logic_variables ` set active))"
    using finite by auto
  have source: "finite (\<Union>((logic_variables \<circ> logic_embed) ` set clause))"
    by (simp add: o_def cut_term_variables[symmetric] del: cut_term_variables)
  show ?thesis using logic_fresh_renaming[OF infinite caller source]
    by (simp add: logic_freshening_def Let_def)
qed

lemma cut_backtrack_step:
  fixes a :: "('f,('f logic_symbol,'v) logic_tree) logic_atom"
  assumes index: "c<length P"
    and infinite: "infinite (UNIV :: 'v set)"
    and finite: "\<And>t. t\<in>set (logic_arguments a @ concat (map logic_goal_terms gs)) \<Longrightarrow>
      finite (logic_variables t)"
    and failure: "\<not>(\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>r.
      lp_isubst (cut_atom a) s = lp_ieval (cut_head (fst (P!c))) r)"
  shows "logic_cut_step A D P (LogicClause (LogicAtom a#gs) c m#es) es"
proof -
  obtain r where fresh: "logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c))))"
    using cut_freshening_exists[OF infinite finite] by blast
  have impossible: "\<not>(logic_atom_map (logic_subst s) a =
      logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (fst (P!c)))" for s
  proof
    assume eq: "logic_atom_map (logic_subst s) a =
      logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (fst (P!c))"
    have composition: "logic_subst s \<circ> logic_eval (LVar \<circ> r) = logic_eval (s \<circ> r)"
      by (rule ext) (simp add: logic_subst_composition o_def)
    have native_eq: "lp_isubst (cut_atom a) (cut_tree \<circ> s) =
        lp_ieval (cut_head (fst (P!c))) (cut_tree \<circ> (s \<circ> r))"
      using arg_cong[OF eq[unfolded composition], where f=cut_atom]
      by (simp only: cut_atom_subst cut_head_eval)
    show False using failure native_eq by blast
  qed
  show ?thesis by (rule logic_cut_step.backtrack[OF index fresh]) (use impossible in blast)
qed


ML \<open>
  val results = @{thms cut_freshening_iff cut_atom_global_mgu
    cut_fresh_resolution_typed cut_resolution_step cut_backtrack_step}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut fresh representation: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Cut fresh representation: oracle dependencies: " ^ commas names)
\<close>

end
