theory LP_Cut_Erased_Resolution
  imports LP_Cut_Erased_Freshening
begin

text \<open>Encoding an ordinary atom as a user-headed tree is confined to this
representation proof; ordinary atoms in the specification retain LAtom.\<close>
fun cut_logic_atom_tree :: "('f,('f logic_symbol,'v) logic_tree) logic_atom \<Rightarrow>
    ('f logic_symbol,'v) logic_tree" where
  "cut_logic_atom_tree (LAtom p ts) = LFun (LogicUser p) ts"
lemma cut_logic_atom_tree_correct:
  "logic_tree_arity_correct (logic_symbol_arity A) (cut_logic_atom_tree a) =
    logic_atom_correct A (logic_tree_arity_correct (logic_symbol_arity A)) a"
  by (cases a) simp
lemma cut_logic_atom_tree_mgu:
  "logic_mgu D a b s = logic_mgu D (LAtom () [cut_logic_atom_tree a])
    (LAtom () [cut_logic_atom_tree b]) s"
  by (cases a; cases b) (simp add: logic_mgu_def)
lemma cut_erased_atom_tree:
  "cut_tree (cut_unrank_tree (cut_logic_atom_tree a)) = cut_atom (cut_unrank_atom a)"
  by (cases a) (auto simp: map_map o_def split: prod.splits)
lemma cut_erased_head_tree:
  "cut_tree (cut_unrank_tree (cut_logic_atom_tree
      (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom h)))) =
    lp_ieval (cut_head h) (LPIVar \<circ> r)"
  by (simp add: cut_erased_atom_tree cut_unrank_rank_atom_eval cut_head_eval o_def)

context cut_runtime_domain
begin
lemma erased_mgu_resolve:
  assumes erasure: "cut_mgu_erasure D"
    and fresh: "logic_freshening r (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (cut_rank_atom h) @ concat (map logic_goal_terms (map cut_rank_goal bs)))"
    and caller: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd)) a"
    and head: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom h))"
    and mgu: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) a
      (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom h)) s"
  shows "mgu_resolve (cut_atom (cut_unrank_atom a)) (map cut_igoal (map cut_unrank_goal gs))
    (cut_head h) (map cut_fgoal bs) (cut_tree \<circ> cut_unrank_tree \<circ> s)
    ((cut_tree \<circ> cut_unrank_tree \<circ> s) \<circ> r)"
proof (rule fresh_resolution_mgu_resolve)
  let ?s = "cut_tree \<circ> cut_unrank_tree \<circ> s"
  let ?a = "cut_logic_atom_tree a"
  let ?b = "cut_logic_atom_tree (logic_atom_map (logic_eval (LVar \<circ> r)) (cut_rank_atom h))"
  have ca: "logic_tree_arity_correct (logic_symbol_arity snd) ?a"
    using caller by (simp only: cut_logic_atom_tree_correct)
  have cb: "logic_tree_arity_correct (logic_symbol_arity snd) ?b"
    using head by (simp only: cut_logic_atom_tree_correct)
  have wrapped: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) (LAtom () [?a]) (LAtom () [?b]) s"
    using mgu by (simp only: cut_logic_atom_tree_mgu[symmetric])
  have native: "lp_runtime_mgu D ((),[cut_atom (cut_unrank_atom a)])
    ((),[lp_ieval (cut_head h) (LPIVar \<circ> r)]) ?s"
    using erasure[unfolded cut_mgu_erasure_def, rule_format, OF ca cb wrapped]
    by (simp only: cut_erased_head_tree; simp only: cut_erased_atom_tree)
  have renamed: "lp_runtime_freshening r
    (cut_atom (cut_unrank_atom a) # concat (map lp_cut_terms (map cut_igoal (map cut_unrank_goal gs))))
    (cut_head h # concat (map lp_cut_terms (map cut_fgoal bs)))"
    using fresh by (simp only: cut_freshening_iff cut_erased_freshening)
  show "lp_fresh_resolution D (cut_atom (cut_unrank_atom a)) (map cut_igoal (map cut_unrank_goal gs))
    (cut_head h) (map cut_fgoal bs) ?s (?s \<circ> r)"
    unfolding lp_fresh_resolution_def by (intro exI[of _ r]) (simp only: renamed native simp_thms)
qed
end

ML \<open>
  val results = @{thms cut_runtime_domain.erased_mgu_resolve}
  val _ = if Thm_Deps.has_skip_proof results then error "Erased resolution: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Erased resolution: oracle dependency"
\<close>
end
