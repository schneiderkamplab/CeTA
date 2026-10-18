theory Relative_ADP_Root_Graph
  imports Relative_ADP_Derelatification_Dev.Relative_ADP_Derelatification
    Relative_ADP_Dependency_Graph_Dev.Relative_ADP_Generic_Graph_Impl
begin

lemma adp_false_step_preserves_sharp_root:
  assumes step: "(s,t) \<in> adp_step_case_rel A False"
    and sharp: "[] \<in> sharp_positions s"
  shows "Term.root t = Term.root s \<and> [] \<in> sharp_positions t"
proof -
  from step have "adp_step_case A False s t"
    unfolding adp_step_case_rel_def by simp
  from adp_step_case_falseE[OF this]
  obtain l r phi p sigma annotations where
    rule: "(l,r) \<in> A"
    and lhs: "plain_adp_term_pred l"
    and vrf: "valid_vrf (l,r) phi"
    and pos: "p \<in> fun_poss s"
    and plain: "False = (p \<in> sharp_positions s)"
    and match: "erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma"
    and annotations: "annotations = (if False then sharp_positions r else {}) \<union>
      transported_annotations phi l (s |_ p)"
    and target: "t = (ctxt_of_pos_term p s)\<langle>
      annotate_term annotations (erase_adp_term r \<cdot> sigma)\<rangle>" .
  have nonempty: "p \<noteq> []" using plain sharp by auto
  show ?thesis using pos nonempty sharp target
    by (cases s; cases p) (auto simp: sharp_positions_def)
qed

lemma adp_false_steps_preserve_sharp_root:
  assumes steps: "(s,t) \<in> (adp_step_case_rel A False)^*"
    and sharp: "[] \<in> sharp_positions s"
  shows "Term.root t = Term.root s \<and> [] \<in> sharp_positions t"
  using steps sharp
  by (induct rule: rtrancl_induct) (auto dest: adp_false_step_preserves_sharp_root)

lemma adp_semantic_edge_has_matching_roots:
  assumes edge: "relative_adp_dependency_edge A source target"
    and lhs: "is_Fun (fst target)"
  shows "\<exists>u \<in> annotated_rhs_subterms source.
    Term.root (erase_adp_term u) = Term.root (erase_adp_term (fst target))"
proof -
  from edge obtain u sigma tau where
      u: "u \<in> annotated_rhs_subterms source"
    and steps: "(mark_adp_root u \<cdot> sigma,
      mark_adp_root (fst target) \<cdot> tau) \<in>
      (adp_step_case_rel (erase_annotations_adp ` A) False)^*"
    unfolding relative_adp_dependency_edge_def by blast
  have fun_u: "is_Fun u"
    using u unfolding annotated_rhs_subterms_def sharp_positions_def
    by (auto split: option.splits term.splits)
  have sharp: "[] \<in> sharp_positions (mark_adp_root u \<cdot> sigma)"
    using fun_u by (cases u) (auto simp: mark_adp_root_def annotate_term_def sharp_positions_def)
  from adp_false_steps_preserve_sharp_root[OF steps sharp]
  have roots: "Term.root (mark_adp_root (fst target) \<cdot> tau) =
      Term.root (mark_adp_root u \<cdot> sigma)" by simp
  have "Term.root (erase_adp_term u) = Term.root (erase_adp_term (fst target))"
    using roots fun_u lhs
    by (cases u; cases "fst target") (auto simp: mark_adp_root_def annotate_term_def)
  with u show ?thesis by blast
qed

definition relative_adp_root_successors where
  "relative_adp_root_successors problem source = filter (\<lambda>target.
    \<not> is_Fun (fst (problem ! target)) \<or>
    list_ex (\<lambda>u. Term.root (erase_adp_term u) =
      Term.root (erase_adp_term (fst (problem ! target))))
      (annotated_rhs_subterms_list (problem ! source)))
    (relative_adp_estimated_successors problem source)"

lemma relative_adp_root_successors_bounds:
  "target \<in> set (relative_adp_root_successors problem source) \<Longrightarrow>
    target < length problem"
  unfolding relative_adp_root_successors_def
  by (auto dest: relative_adp_estimated_successors_bounds)

lemma relative_adp_root_successors_sound:
  assumes source: "source < length problem" and target: "target < length problem"
    and edge: "relative_adp_dependency_edge (set problem)
      (problem ! source) (problem ! target)"
  shows "target \<in> set (relative_adp_root_successors problem source)"
  using relative_adp_estimated_successors_sound[OF source target edge]
    adp_semantic_edge_has_matching_roots[OF edge]
  unfolding relative_adp_root_successors_def
  by (auto simp: list_ex_iff annotated_rhs_subterms_list_sound)

global_interpretation root_guard: relative_adp_graph_estimator relative_adp_root_successors
  by standard (auto intro: relative_adp_root_successors_bounds relative_adp_root_successors_sound)

definition relative_adp_root_graph_candidates where
  "relative_adp_root_graph_candidates P B =
    Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_graph_candidates relative_adp_root_successors P B"

lemmas relative_adp_root_graph_processor = root_guard.relative_adp_estimated_graph_processor

end
