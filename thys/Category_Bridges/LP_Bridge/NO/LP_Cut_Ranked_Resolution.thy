theory LP_Cut_Ranked_Resolution
  imports LP_Cut_Fresh_Representation Category_LP_Bridge.LP_Cut_Ranked_Execution
begin

lemma cut_rank_eval:
  "cut_rank_tree (logic_eval s t) = logic_eval (cut_rank_tree \<circ> s) (cut_rank_term t)"
  by (simp add: cut_rank_subst cut_rank_embed)
lemma cut_rank_atom_eval:
  "cut_rank_runtime_atom (logic_atom_map (logic_eval s) h) =
    logic_atom_map (logic_eval (cut_rank_tree \<circ> s)) (cut_rank_atom h)"
  by (cases h) (simp add: cut_rank_runtime_atom_def map_map o_def cut_rank_eval)
lemma cut_rank_runtime_arguments:
  "logic_arguments (cut_rank_runtime_atom a) = map cut_rank_tree (logic_arguments a)"
  by (cases a) (simp add: cut_rank_runtime_atom_def)

lemma cut_rank_goal_terms:
  "logic_goal_terms (cut_rank_runtime_goal g) = map cut_rank_tree (logic_goal_terms g)"
  by (cases g) (simp_all add: cut_rank_runtime_arguments)
lemma cut_rank_fgoal_terms:
  "logic_goal_terms (cut_rank_goal g) = map cut_rank_term (logic_goal_terms g)"
  by (cases g) (simp_all split: logic_atom.splits)

text \<open>The native witness already carries a fresh renaming and a global
MGU. Ranking transports that witness; correct argument arities then supply
the restriction theorem, rather than an assumed semantic correspondence.\<close>
lemma cut_rank_fresh_resolution:
  assumes native: "lp_fresh_resolution D (cut_atom a) (map cut_igoal gs)
      (cut_head h) (map cut_fgoal bs) sigma rho"
    and caller: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (cut_rank_runtime_atom a))"
    and clause: "list_all (arity_correct (logic_symbol_arity snd))
      (logic_arguments (cut_rank_atom h))"
    and projection: "\<And>t. D (cut_tree (cut_unrank_tree t)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t)))"
  shows "\<exists>r. logic_freshening r
      (logic_arguments (cut_rank_runtime_atom a) @
        concat (map logic_goal_terms (map cut_rank_runtime_goal gs)))
      (logic_arguments (cut_rank_atom h) @ concat (map logic_goal_terms (map cut_rank_goal bs))) \<and>
    rho = sigma \<circ> r \<and>
    logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t)
      (cut_rank_runtime_atom a)
      (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom h))
      (cut_rank_tree \<circ> cut_tree_back \<circ> sigma)"
proof -
  obtain r where fresh: "logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments h @ concat (map logic_goal_terms bs))"
    and rho: "rho = sigma \<circ> r"
    and mgu: "logic_mgu (\<lambda>t. D (cut_tree t)) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) h) (cut_tree_back \<circ> sigma)"
    using cut_fresh_resolution_canonical[OF native] by blast
  have renamed: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree
        (logic_atom_map (logic_eval (LVar \<circ> r)) h)))"
    using clause by (cases h)
      (auto simp: list_all_iff cut_rank_eval o_def intro: logic_subst_arity_correct)
  have left: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree a))"
    using caller by (cases a) (simp add: cut_rank_runtime_atom_def)
  have typed: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t)
      (cut_rank_runtime_atom a)
      (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom h))
      (cut_rank_tree \<circ> cut_tree_back \<circ> sigma)"
    using cut_rank_typed_mgu[OF mgu left renamed projection]
    by (simp add: cut_rank_runtime_atom_mgu[symmetric] cut_rank_atom_eval o_def)
  have ranked_fresh: "logic_freshening r
      (logic_arguments (cut_rank_runtime_atom a) @
        concat (map logic_goal_terms (map cut_rank_runtime_goal gs)))
      (logic_arguments (cut_rank_atom h) @ concat (map logic_goal_terms (map cut_rank_goal bs)))"
    using cut_rank_freshening[of r "logic_arguments a @ concat (map logic_goal_terms gs)"
      "logic_arguments h @ concat (map logic_goal_terms bs)"] fresh
    by (simp add: cut_rank_runtime_arguments cut_rank_goal_terms cut_rank_fgoal_terms
      map_map map_concat o_def)
  show ?thesis using ranked_fresh rho typed by blast
qed

lemma cut_rank_goal_eval_bind:
  "cut_rank_runtime_goal (logic_bind_cut m (logic_eval s) g) =
    logic_bind_cut m (logic_eval (cut_rank_tree \<circ> s)) (cut_rank_goal g)"
  by (cases g) (simp_all add: cut_rank_atom_eval cut_rank_eval)
lemma cut_rank_program_nth:
  "c<length P \<Longrightarrow> cut_rank_program P!c =
    (cut_rank_atom (fst (P!c)), map cut_rank_goal (snd (P!c)))"
  by (simp add: cut_rank_program_def case_prod_unfold)

lemma cut_rank_resolution_step:
  assumes index: "c<length P"
    and native: "lp_fresh_resolution D (cut_atom a) (map cut_igoal gs)
      (cut_head (fst (P!c))) (map cut_fgoal (snd (P!c))) sigma rho"
    and caller: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (cut_rank_runtime_atom a))"
    and clause: "list_all (arity_correct (logic_symbol_arity snd))
      (logic_arguments (cut_rank_atom (fst (P!c))))"
    and projection: "\<And>t. D (cut_tree (cut_unrank_tree t)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t)))"
  shows "logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P)
    (map cut_rank_choice (LogicClause (LogicAtom a#gs) c m#es))
    (map cut_rank_choice (cut_state_back (LPCGoals
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (map cut_fgoal (snd (P!c))) @
       map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map cut_igoal gs)) # cut_state es)))"
proof -
  obtain r where fresh: "logic_freshening r
      (logic_arguments (cut_rank_runtime_atom a) @
        concat (map logic_goal_terms (map cut_rank_runtime_goal gs)))
      (logic_arguments (cut_rank_atom (fst (P!c))) @
        concat (map logic_goal_terms (map cut_rank_goal (snd (P!c)))))"
    and rho: "rho = sigma \<circ> r"
    and mgu: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t)
      (cut_rank_runtime_atom a)
      (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom (fst (P!c))))
      (cut_rank_tree \<circ> cut_tree_back \<circ> sigma)"
    using cut_rank_fresh_resolution[OF native caller clause projection] by blast
  have composition: "logic_subst (cut_rank_tree \<circ> cut_tree_back \<circ> sigma) \<circ>
      logic_eval (LVar \<circ> r) = logic_eval (cut_rank_tree \<circ> cut_tree_back \<circ> rho)"
    by (rule ext) (simp add: logic_subst_composition rho o_def)
  have step: "logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P)
      (LogicClause (LogicAtom (cut_rank_runtime_atom a)#map cut_rank_runtime_goal gs) c m#map cut_rank_choice es)
      (LogicGoals (map (logic_bind_cut m (logic_eval (cut_rank_tree \<circ> cut_tree_back \<circ> rho)))
        (map cut_rank_goal (snd (P!c))) @
        map (logic_goal_map (logic_subst (cut_rank_tree \<circ> cut_tree_back \<circ> sigma)))
          (map cut_rank_runtime_goal gs))#map cut_rank_choice es)"
    using logic_cut_step.resolve[where A=snd and D="\<lambda>t. D (cut_tree (cut_unrank_tree t))"
      and P="cut_rank_program P" and c=c and r=r and a="cut_rank_runtime_atom a"
      and gs="map cut_rank_runtime_goal gs" and s="cut_rank_tree \<circ> cut_tree_back \<circ> sigma"
      and m=m and es="map cut_rank_choice es"] index fresh mgu
    by (simp add: cut_rank_program_def case_prod_unfold composition)
  show ?thesis using step
    by (simp add: map_map o_def cut_back_goal_eval_bind cut_back_goal_subst
      cut_rank_goal_eval_bind cut_rank_goal_subst)
qed

fun cut_unrank_atom :: "('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_atom \<Rightarrow>
    ('f,('f logic_symbol,'v) logic_tree) logic_atom" where
  "cut_unrank_atom (LAtom (f,n) ts) = LAtom f (map cut_unrank_tree ts)"
lemma cut_unrank_runtime_atom[simp]:
  "cut_unrank_atom (cut_rank_runtime_atom a) = a"
  by (cases a) (simp add: cut_rank_runtime_atom_def map_map o_def)
lemma cut_unrank_atom_subst:
  "cut_unrank_atom (logic_atom_map (logic_subst s) a) =
    logic_atom_map (logic_subst (cut_unrank_tree \<circ> s)) (cut_unrank_atom a)"
  by (cases a) (auto simp: map_map o_def cut_unrank_subst split: prod.splits)
lemma cut_unrank_rank_atom_eval:
  "cut_unrank_atom (logic_atom_map (logic_eval s) (cut_rank_atom h)) =
    logic_atom_map (logic_eval (cut_unrank_tree \<circ> s)) h"
  by (cases h) (simp add: map_map o_def cut_unrank_subst cut_unrank_embed)
lemma cut_rank_failure:
  assumes failure: "\<not>(\<exists>s r. logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h)"
  shows "\<not>(\<exists>s. logic_substitution_in E s \<and>
    logic_atom_map (logic_subst s) (cut_rank_runtime_atom a) =
      logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h))"
proof
  assume "\<exists>s. logic_substitution_in E s \<and>
    logic_atom_map (logic_subst s) (cut_rank_runtime_atom a) =
      logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h)"
  then obtain s where eq: "logic_atom_map (logic_subst s) (cut_rank_runtime_atom a) =
      logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h)" by blast
  have composition: "logic_subst s \<circ> logic_eval (LVar \<circ> r) = logic_eval (s \<circ> r)"
    by (rule ext) (simp add: logic_subst_composition o_def)
  have raw: "logic_atom_map (logic_subst (cut_unrank_tree \<circ> s)) a =
    logic_atom_map (logic_eval (cut_unrank_tree \<circ> s \<circ> r)) h"
    using arg_cong[OF eq, where f=cut_unrank_atom]
    by (simp add: composition cut_unrank_atom_subst cut_unrank_rank_atom_eval o_assoc)
  show False using failure raw by blast
qed

lemma cut_rank_backtrack_step:
  fixes a :: "('f,('f logic_symbol,'v) logic_tree) logic_atom"
  assumes index: "c<length P"
    and infinite: "infinite (UNIV :: 'v set)"
    and finite: "\<And>t. t\<in>set (logic_arguments a @ concat (map logic_goal_terms gs)) \<Longrightarrow>
      finite (logic_variables t)"
    and failure: "\<not>(\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>r.
      lp_isubst (cut_atom a) s = lp_ieval (cut_head (fst (P!c))) r)"
  shows "logic_cut_step snd E (cut_rank_program P)
    (map cut_rank_choice (LogicClause (LogicAtom a#gs) c m#es)) (map cut_rank_choice es)"
proof -
  obtain r where fresh: "logic_freshening r
      (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c))))"
    using cut_freshening_exists[OF infinite finite] by blast
  have ranked_fresh: "logic_freshening r
      (logic_arguments (cut_rank_runtime_atom a) @
        concat (map logic_goal_terms (map cut_rank_runtime_goal gs)))
      (logic_arguments (cut_rank_atom (fst (P!c))) @
        concat (map logic_goal_terms (map cut_rank_goal (snd (P!c)))))"
    using cut_rank_freshening[of r "logic_arguments a @ concat (map logic_goal_terms gs)"
      "logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c)))"] fresh
    by (simp add: cut_rank_runtime_arguments cut_rank_goal_terms cut_rank_fgoal_terms
      map_map map_concat o_def)
  have raw: "\<not>(\<exists>s r. logic_atom_map (logic_subst s) a =
      logic_atom_map (logic_eval r) (fst (P!c)))"
    using failure by (simp add: cut_atom_unifiable_iff)
  note failed = cut_rank_failure[OF raw, where r=r and E="\<lambda>t. E t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t"]
  show ?thesis using logic_cut_step.backtrack[where A=snd and D=E and P="cut_rank_program P"
    and c=c and r=r and a="cut_rank_runtime_atom a" and gs="map cut_rank_runtime_goal gs"
    and m=m and es="map cut_rank_choice es"] index ranked_fresh failed
    by (simp add: cut_rank_program_def case_prod_unfold)
qed

lemma cut_rank_unify_step:
  assumes mgu: "logic_mgu (\<lambda>t. D (cut_tree t)) (LAtom () [a]) (LAtom () [b]) s"
    and left: "logic_tree_arity_correct (logic_symbol_arity snd) (cut_rank_tree a)"
    and right: "logic_tree_arity_correct (logic_symbol_arity snd) (cut_rank_tree b)"
    and projection: "\<And>t. D (cut_tree (cut_unrank_tree t)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree t) = t \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) z t)))"
  shows "logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P)
    (map cut_rank_choice (LogicGoals (LogicUnify a b#gs)#es))
    (map cut_rank_choice (LogicGoals (map (logic_goal_map (logic_subst s)) gs)#es))"
proof -
  have typed: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t)
      (LAtom () [cut_rank_tree a]) (LAtom () [cut_rank_tree b]) (cut_rank_tree \<circ> s)"
    proof -
    have la: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree (LAtom () [a])))" using left by simp
    have rb: "list_all (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_arguments (logic_atom_map cut_rank_tree (LAtom () [b])))" using right by simp
    show ?thesis using cut_rank_typed_mgu[OF mgu la rb projection]
      by (simp only: logic_atom_map.simps list.map; blast)
  qed
  show ?thesis using logic_cut_step.unify[OF typed, where P="cut_rank_program P"
    and gs="map cut_rank_runtime_goal gs" and es="map cut_rank_choice es"]
    by (simp add: map_map o_def cut_rank_goal_subst)
qed
lemma cut_rank_unify_fail_step:
  assumes failure: "\<not>(\<exists>s. logic_subst s a = logic_subst s b)"
  shows "logic_cut_step snd E (cut_rank_program P)
    (map cut_rank_choice (LogicGoals (LogicUnify a b#gs)#es)) (map cut_rank_choice es)"
proof -
  have failure': "\<not>(\<exists>s. logic_substitution_in (\<lambda>t. E t \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) s \<and>
      logic_subst s (cut_rank_tree a) = logic_subst s (cut_rank_tree b))"
  proof
    assume "\<exists>s. logic_substitution_in (\<lambda>t. E t \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) s \<and>
      logic_subst s (cut_rank_tree a) = logic_subst s (cut_rank_tree b)"
    then obtain s where eq: "logic_subst s (cut_rank_tree a) = logic_subst s (cut_rank_tree b)" by blast
    have "logic_subst (cut_unrank_tree \<circ> s) a = logic_subst (cut_unrank_tree \<circ> s) b"
      using arg_cong[OF eq, where f=cut_unrank_tree] by (simp add: cut_unrank_subst)
    then show False using failure by blast
  qed
  show ?thesis using logic_cut_step.unify_fail[OF failure', where P="cut_rank_program P"
    and gs="map cut_rank_runtime_goal gs" and es="map cut_rank_choice es"] by simp
qed

ML \<open>
  val results = @{thms cut_rank_fresh_resolution cut_rank_resolution_step cut_rank_backtrack_step cut_rank_unify_step cut_rank_unify_fail_step}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked resolution: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Ranked resolution: oracle dependency"
\<close>
end
