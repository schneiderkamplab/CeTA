theory LP_Cut_Erased_Freshening
  imports LP_Cut_MGU_Erasure
begin

lemma cut_unrank_subtree:
  "logic_subtree u t \<Longrightarrow> logic_subtree (cut_unrank_tree u) (cut_unrank_tree t)"
  by (induct rule: logic_subtree.induct) (fastforce intro: logic_subtree.intros)+
lemma cut_unrank_variables[simp]: "logic_variables (cut_unrank_tree t) = logic_variables t"
proof -
  have forward: "logic_subtree (LVar x) (cut_unrank_tree t) \<Longrightarrow> logic_subtree (LVar x) t" for x
  proof -
    assume premise: "logic_subtree (LVar x) (cut_unrank_tree t)"
    obtain u where u: "LVar x = cut_unrank_tree u" "logic_subtree u t"
      using logic_relabel_subtree[where k="\<lambda>f _. cut_unrank_symbol f",
        OF cut_unrank_tree_simps(1) cut_unrank_tree_simps(2) premise] by blast
    show ?thesis using u by (cases u) auto
  qed
  show ?thesis unfolding logic_variables_def
    using forward cut_unrank_subtree[of "LVar _" t] by auto
qed
lemma cut_unrank_freshening:
  "logic_freshening r (map cut_unrank_tree active) (map cut_unrank_term clause) =
    logic_freshening r active clause"
  by (simp add: logic_freshening_def image_image o_def cut_unrank_embed[symmetric])
lemma cut_unrank_arguments:
  "logic_arguments (cut_unrank_atom a) = map cut_unrank_tree (logic_arguments a)"
  by (cases a) (auto split: prod.splits)
lemma cut_unrank_goal_terms:
  "logic_goal_terms (cut_unrank_goal g) = map cut_unrank_tree (logic_goal_terms g)"
  by (cases g) (simp_all add: cut_unrank_arguments)

lemma cut_erased_freshening:
  "logic_freshening r
    (logic_arguments (cut_unrank_atom a) @ concat (map logic_goal_terms (map cut_unrank_goal gs)))
    (logic_arguments h @ concat (map logic_goal_terms bs)) =
   logic_freshening r (logic_arguments a @ concat (map logic_goal_terms gs))
    (logic_arguments (cut_rank_atom h) @ concat (map logic_goal_terms (map cut_rank_goal bs)))"
proof -
  have mapped: "map cut_unrank_term
      (logic_arguments (cut_rank_atom h) @ concat (map logic_goal_terms (map cut_rank_goal bs))) =
      logic_arguments h @ concat (map logic_goal_terms bs)"
    by (cases h) (simp add: cut_rank_fgoal_terms map_concat map_map o_def)
  show ?thesis using cut_unrank_freshening[of r
    "logic_arguments a @ concat (map logic_goal_terms gs)"
    "logic_arguments (cut_rank_atom h) @ concat (map logic_goal_terms (map cut_rank_goal bs))"]
    by (simp add: mapped cut_rank_fgoal_terms cut_unrank_arguments cut_unrank_goal_terms map_concat map_map o_def)
qed

ML \<open>
  val results = @{thms cut_unrank_variables cut_erased_freshening}
  val _ = if Thm_Deps.has_skip_proof results then error "Erased freshening: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Erased freshening: oracle dependency"
\<close>
end
