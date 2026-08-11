theory Relative_ADP_Dependency_Graph_Impl
  imports
    Relative_ADP_Dependency_Graph
    Auxx.Gabow_SCC_RBT
    "Transitive-Closure-II.RTrancl"
begin

text \<open>
  Executable indexed estimated graph and SCC decomposition. Reflexive edges
  keep isolated nodes in Gabow's nontrivial-SCC interface without changing
  mutual reachability.
\<close>

definition relative_adp_estimated_edges ::
  "('f, 'v) adp list \<Rightarrow> (nat \<times> nat) list" where
  "relative_adp_estimated_edges problem = concat
    (map (\<lambda>source. map (Pair source)
      (relative_adp_estimated_successors problem source))
      [0..<length problem])"

definition relative_adp_reflexive_estimated_edges ::
  "('f, 'v) adp list \<Rightarrow> (nat \<times> nat) list" where
  "relative_adp_reflexive_estimated_edges problem =
    map (\<lambda>i. (i,i)) [0..<length problem] @
      relative_adp_estimated_edges problem"

definition relative_adp_estimated_sccs ::
  "('f, 'v) adp list \<Rightarrow> nat list list" where
  "relative_adp_estimated_sccs problem =
    scc_decomp (relative_adp_reflexive_estimated_edges problem)"

lemma relative_adp_estimated_edges_iff:
  "(source,target) \<in> set (relative_adp_estimated_edges problem) \<longleftrightarrow>
    source < length problem \<and>
    target \<in> set (relative_adp_estimated_successors problem source)"
  unfolding relative_adp_estimated_edges_def by auto

lemma relative_adp_estimated_edge_bounds:
  assumes "(source,target) \<in> set (relative_adp_estimated_edges problem)"
  shows "source < length problem" "target < length problem"
  using assms relative_adp_estimated_successors_bounds
  unfolding relative_adp_estimated_edges_iff by auto

definition relative_adp_index_successors ::
  "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_index_successors edges source =
    map snd (filter (\<lambda>edge. fst edge = source) edges)"

lemma relative_adp_index_successors_set:
  "set (relative_adp_index_successors edges source) =
    {target. (source,target) \<in> set edges}"
  unfolding relative_adp_index_successors_def by auto

definition relative_adp_estimated_reachable ::
  "('f, 'v) adp list \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_estimated_reachable problem source =
    mk_rtrancl_list (=)
      (relative_adp_index_successors
        (relative_adp_estimated_edges problem)) [source]"

lemma relative_adp_estimated_reachable_set:
  "set (relative_adp_estimated_reachable problem source) =
    (set (relative_adp_estimated_edges problem))\<^sup>* `` {source}"
proof -
  let ?successors = "relative_adp_index_successors
    (relative_adp_estimated_edges problem)"
  let ?E = "{(source,target). target \<in> set (?successors source)}"
  have E: "?E = set (relative_adp_estimated_edges problem)"
    unfolding relative_adp_index_successors_set by auto
  have finite_reachable: "\<And>source. finite {target. (source,target) \<in> ?E\<^sup>*}"
  proof -
    fix source
    have subset: "{target. (source,target) \<in> ?E\<^sup>*} \<subseteq>
        insert source {target. target < length problem}"
    proof
      fix target
      assume target: "target \<in> {target. (source,target) \<in> ?E\<^sup>*}"
      then have reach: "(source,target) \<in> ?E\<^sup>*" by simp
      show "target \<in> insert source {target. target < length problem}"
        using reach
      proof (induction rule: rtrancl_induct)
        case base
        then show ?case by simp
      next
        case (step middle successor)
        have "(middle,successor) \<in>
            set (relative_adp_estimated_edges problem)"
          using step.hyps(2) unfolding E .
        then have "successor < length problem"
          by (rule relative_adp_estimated_edge_bounds(2))
        then show ?case by simp
      qed
    qed
    show "finite {target. (source,target) \<in> ?E\<^sup>*}"
      by (rule finite_subset[OF subset]) simp
  qed
  interpret reach: relation_subsumption_list ?successors "(=)"
  proof
    fix source
    show "finite {target. (source,target) \<in> ?E\<^sup>*}"
      by (rule finite_reachable)
  qed auto
  show ?thesis
    unfolding relative_adp_estimated_reachable_def
      reach.mk_rtrancl_list reach.mk_rtrancl_no_subsumption[OF HOL.refl] E
    by simp
qed

definition relative_adp_index_predecessors ::
  "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_index_predecessors edges target =
    map fst (filter (\<lambda>edge. snd edge = target) edges)"

lemma relative_adp_index_predecessors_set:
  "set (relative_adp_index_predecessors edges target) =
    {source. (source,target) \<in> set edges}"
  unfolding relative_adp_index_predecessors_def by auto

definition relative_adp_estimated_coreachable ::
  "('f, 'v) adp list \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_estimated_coreachable problem target =
    mk_rtrancl_list (=)
      (relative_adp_index_predecessors
        (relative_adp_estimated_edges problem)) [target]"

lemma relative_adp_estimated_coreachable_set:
  "set (relative_adp_estimated_coreachable problem target) =
    {(source,target). (target,source) \<in>
      set (relative_adp_estimated_edges problem)}\<^sup>* `` {target}"
proof -
  let ?predecessors = "relative_adp_index_predecessors
    (relative_adp_estimated_edges problem)"
  let ?E = "{(target,source). source \<in> set (?predecessors target)}"
  have E: "?E = {(target,source). (source,target) \<in>
      set (relative_adp_estimated_edges problem)}"
    unfolding relative_adp_index_predecessors_set by auto
  have finite_reachable: "\<And>target.
      finite {source. (target,source) \<in> ?E\<^sup>*}"
  proof -
    fix target
    have subset: "{source. (target,source) \<in> ?E\<^sup>*} \<subseteq>
        insert target {source. source < length problem}"
    proof
      fix source
      assume source: "source \<in> {source. (target,source) \<in> ?E\<^sup>*}"
      then have reach: "(target,source) \<in> ?E\<^sup>*" by simp
      show "source \<in> insert target {source. source < length problem}"
        using reach
      proof (induction rule: rtrancl_induct)
        case base
        then show ?case by simp
      next
        case (step middle predecessor)
        have "(predecessor,middle) \<in>
            set (relative_adp_estimated_edges problem)"
          using step.hyps(2) unfolding E by simp
        then have "predecessor < length problem"
          by (rule relative_adp_estimated_edge_bounds(1))
        then show ?case by simp
      qed
    qed
    show "finite {source. (target,source) \<in> ?E\<^sup>*}"
      by (rule finite_subset[OF subset]) simp
  qed
  interpret reach: relation_subsumption_list ?predecessors "(=)"
  proof
    fix target
    show "finite {source. (target,source) \<in> ?E\<^sup>*}"
      by (rule finite_reachable)
  qed auto
  show ?thesis
    unfolding relative_adp_estimated_coreachable_def
      reach.mk_rtrancl_list reach.mk_rtrancl_no_subsumption[OF HOL.refl] E
    by simp
qed

definition relative_adp_estimated_corridor ::
  "('f, 'v) adp list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_estimated_corridor problem source target =
    filter (\<lambda>middle.
      middle \<in> set (relative_adp_estimated_reachable problem source) \<and>
      middle \<in> set (relative_adp_estimated_coreachable problem target))
      [0..<length problem]"

lemma relative_adp_estimated_corridor_set:
  "set (relative_adp_estimated_corridor problem source target) =
    {node_index. node_index < length problem \<and>
      (source,node_index) \<in>
        (set (relative_adp_estimated_edges problem))\<^sup>* \<and>
      (node_index,target) \<in>
        (set (relative_adp_estimated_edges problem))\<^sup>*}"
proof -
  have reverse_edges:
      "{(source,target). (target,source) \<in>
        set (relative_adp_estimated_edges problem)} =
       (set (relative_adp_estimated_edges problem))\<inverse>"
    by auto
  have converse_rtrancl: "(target,node_index) \<in>
        {(source,target). (target,source) \<in>
          set (relative_adp_estimated_edges problem)}\<^sup>* \<longleftrightarrow>
      (node_index,target) \<in>
        (set (relative_adp_estimated_edges problem))\<^sup>*" for node_index
    unfolding reverse_edges by (simp add: rtrancl_converse)
  show ?thesis
    unfolding relative_adp_estimated_corridor_def
      relative_adp_estimated_reachable_set
      relative_adp_estimated_coreachable_set
    using converse_rtrancl by auto
qed

lemma relative_adp_semantic_edge_in_estimated_edges:
  assumes source: "source < length problem"
    and target: "target < length problem"
    and edge: "relative_adp_dependency_edge (set problem)
      (problem ! source) (problem ! target)"
  shows "(source,target) \<in> set (relative_adp_estimated_edges problem)"
  unfolding relative_adp_estimated_edges_iff
  using source relative_adp_estimated_successors_sound[
    OF source target edge] by simp

lemma relative_adp_reflexive_estimated_edges_set:
  "set (relative_adp_reflexive_estimated_edges problem) =
    {(i,i) |i. i < length problem} \<union>
      set (relative_adp_estimated_edges problem)"
  unfolding relative_adp_reflexive_estimated_edges_def by auto

lemma relative_adp_reflexive_estimated_edge_bounds:
  assumes "(source,target) \<in>
    set (relative_adp_reflexive_estimated_edges problem)"
  shows "source < length problem" "target < length problem"
  using assms relative_adp_estimated_edge_bounds
  unfolding relative_adp_reflexive_estimated_edges_set by auto

lemma relative_adp_estimated_sccs_exact:
  "set ` set (relative_adp_estimated_sccs problem) =
    {C. is_scc (set (relative_adp_reflexive_estimated_edges problem)) C \<and>
      C \<times> C \<subseteq>
        (set (relative_adp_reflexive_estimated_edges problem))\<^sup>+}"
  unfolding relative_adp_estimated_sccs_def by (rule scc_decomp)

lemma relative_adp_estimated_scc_nonempty:
  assumes "component \<in> set (relative_adp_estimated_sccs problem)"
  shows "component \<noteq> []"
proof -
  have "is_scc (set (relative_adp_reflexive_estimated_edges problem))
      (set component)"
    using assms relative_adp_estimated_sccs_exact by blast
  then have "set component \<noteq> {}" by (rule scc_non_empty')
  then show ?thesis by simp
qed

lemma relative_adp_estimated_scc_indices:
  assumes component: "component \<in> set (relative_adp_estimated_sccs problem)"
    and member: "node_index \<in> set component"
  shows "node_index < length problem"
proof -
  have loop: "(node_index,node_index) \<in>
      (set (relative_adp_reflexive_estimated_edges problem))\<^sup>+"
    using component member relative_adp_estimated_sccs_exact by blast
  from tranclD[OF loop] obtain successor where edge:
    "(node_index,successor) \<in>
      set (relative_adp_reflexive_estimated_edges problem)" by blast
  show ?thesis
    by (rule relative_adp_reflexive_estimated_edge_bounds(1)[OF edge])
qed

lemma relative_adp_estimated_sccs_cover_index:
  assumes node: "node_index < length problem"
  obtains component where
    "component \<in> set (relative_adp_estimated_sccs problem)"
    "node_index \<in> set component"
proof -
  let ?E = "set (relative_adp_reflexive_estimated_edges problem)"
  have loop_edge: "(node_index,node_index) \<in> ?E"
    using node unfolding relative_adp_reflexive_estimated_edges_set by blast
  then have loop: "(node_index,node_index) \<in> ?E\<^sup>+" by simp
  have singleton_positive: "{node_index} \<times> {node_index} \<subseteq> ?E\<^sup>+"
    using loop by simp
  from get_scc_from_component[
      where C="{node_index}" and E="?E", OF _ singleton_positive]
  obtain C where singleton: "{node_index} \<subseteq> C"
    and scc: "is_scc ?E C"
    and positive: "C \<times> C \<subseteq> ?E\<^sup>+" by blast
  have in_sets: "C \<in> set ` set (relative_adp_estimated_sccs problem)"
    using scc positive relative_adp_estimated_sccs_exact by blast
  then obtain component where component:
      "component \<in> set (relative_adp_estimated_sccs problem)"
    and C: "C = set component" by blast
  have member: "node_index \<in> set component" using singleton unfolding C by simp
  show thesis by (rule that[OF component member])
qed

lemma relative_adp_estimated_sccs_cover:
  "\<Union>(set ` set (relative_adp_estimated_sccs problem)) =
    {i. i < length problem}"
proof
  show "\<Union>(set ` set (relative_adp_estimated_sccs problem)) \<subseteq>
      {i. i < length problem}"
    using relative_adp_estimated_scc_indices by blast
  show "{i. i < length problem} \<subseteq>
      \<Union>(set ` set (relative_adp_estimated_sccs problem))"
  proof
    fix node_index
    assume "node_index \<in> {i. i < length problem}"
    then have node: "node_index < length problem" by simp
    from relative_adp_estimated_sccs_cover_index[OF node]
    obtain component where
      "component \<in> set (relative_adp_estimated_sccs problem)"
      "node_index \<in> set component" .
    then show "node_index \<in>
        \<Union>(set ` set (relative_adp_estimated_sccs problem))" by blast
  qed
qed

lemma relative_adp_estimated_sccs_disjoint:
  assumes first: "first \<in> set (relative_adp_estimated_sccs problem)"
    and second: "second \<in> set (relative_adp_estimated_sccs problem)"
    and overlap: "set first \<inter> set second \<noteq> {}"
  shows "set first = set second"
proof -
  have first_scc: "is_scc
      (set (relative_adp_reflexive_estimated_edges problem)) (set first)"
    using first relative_adp_estimated_sccs_exact by blast
  have second_scc: "is_scc
      (set (relative_adp_reflexive_estimated_edges problem)) (set second)"
    using second relative_adp_estimated_sccs_exact by blast
  from overlap obtain node_index where
    "node_index \<in> set first" "node_index \<in> set second" by blast
  then show ?thesis by (rule is_scc_unique[OF first_scc second_scc])
qed

theorem relative_adp_estimated_path_eventual_scc:
  assumes nodes: "\<And>n. node_stream n < length problem"
    and edges: "\<And>n. (node_stream n, node_stream (Suc n)) \<in>
      set (relative_adp_estimated_edges problem)"
  obtains component N where
    "component \<in> set (relative_adp_estimated_sccs problem)"
    "\<And>n. N \<le> n \<Longrightarrow> node_stream n \<in> set component"
proof -
  let ?V = "{i. i < length problem}"
  let ?E = "set (relative_adp_estimated_edges problem)"
  let ?ER = "set (relative_adp_reflexive_estimated_edges problem)"
  have finite_V: "finite ?V" by simp
  have range: "range node_stream \<subseteq> ?V" using nodes by blast
  have witness: "\<exists>anchor N. anchor \<in> ?V \<and>
      (\<forall>n. N \<le> n \<longrightarrow> (anchor,node_stream n) \<in> ?E\<^sup>*) \<and>
      (\<forall>n. N \<le> n \<longrightarrow> (node_stream n,anchor) \<in> ?E\<^sup>*)"
  proof (rule finite_ipath_has_eventual_mutual_anchor[
      where V="?V" and p=node_stream and E="?E",
      OF finite_V range edges])
    fix anchor N
    assume anchor: "anchor \<in> ?V"
      and forward: "\<And>n. N \<le> n \<Longrightarrow>
        (anchor,node_stream n) \<in> ?E\<^sup>*"
      and backward: "\<And>n. N \<le> n \<Longrightarrow>
        (node_stream n,anchor) \<in> ?E\<^sup>*"
    show "\<exists>anchor N. anchor \<in> ?V \<and>
        (\<forall>n. N \<le> n \<longrightarrow> (anchor,node_stream n) \<in> ?E\<^sup>*) \<and>
        (\<forall>n. N \<le> n \<longrightarrow> (node_stream n,anchor) \<in> ?E\<^sup>*)"
      by (rule exI[of _ anchor], rule exI[of _ N])
         (use anchor forward backward in blast)
  qed
  from witness obtain anchor N where anchor: "anchor \<in> ?V"
    and forward: "\<And>n. N \<le> n \<Longrightarrow>
      (anchor,node_stream n) \<in> ?E\<^sup>*"
    and backward: "\<And>n. N \<le> n \<Longrightarrow>
      (node_stream n,anchor) \<in> ?E\<^sup>*" by blast
  from relative_adp_estimated_sccs_cover_index[of anchor problem]
  obtain component where component:
      "component \<in> set (relative_adp_estimated_sccs problem)"
    and anchor_component: "anchor \<in> set component"
    using anchor by auto
  have scc: "is_scc ?ER (set component)"
    using component relative_adp_estimated_sccs_exact by blast
  have edge_subset: "?E \<subseteq> ?ER"
    unfolding relative_adp_reflexive_estimated_edges_set by blast
  have eventual: "\<And>n. N \<le> n \<Longrightarrow>
      node_stream n \<in> set component"
  proof -
    fix n
    assume Nn: "N \<le> n"
    have to_node: "(anchor,node_stream n) \<in> ?ER\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF edge_subset] forward[OF Nn]])
    have from_node: "(node_stream n,anchor) \<in> ?ER\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF edge_subset] backward[OF Nn]])
    show "node_stream n \<in> set component"
      by (rule is_scc_closed[OF scc anchor_component to_node from_node])
  qed
  show thesis by (rule that[OF component eventual])
qed

definition relative_adp_pair_index ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp \<Rightarrow> nat" where
  "relative_adp_pair_index problem pair =
    (SOME i. i < length problem \<and> problem ! i = pair)"

lemma relative_adp_pair_index_correct:
  assumes "pair \<in> set problem"
  shows "relative_adp_pair_index problem pair < length problem"
    "problem ! relative_adp_pair_index problem pair = pair"
proof -
  have exists: "\<exists>i. i < length problem \<and> problem ! i = pair"
    using assms by (auto simp: in_set_conv_nth)
  have chosen: "relative_adp_pair_index problem pair < length problem \<and>
      problem ! relative_adp_pair_index problem pair = pair"
    unfolding relative_adp_pair_index_def by (rule someI_ex[OF exists])
  then show "relative_adp_pair_index problem pair < length problem"
    "problem ! relative_adp_pair_index problem pair = pair" by auto
qed

lemma relative_adp_semantic_path_in_estimated_path:
  assumes source: "source_pair \<in> set problem"
    and path: "(source_pair,target_pair) \<in>
      (relative_adp_dependency_graph (set problem))\<^sup>*"
  shows "(relative_adp_pair_index problem source_pair,
      relative_adp_pair_index problem target_pair) \<in>
    (set (relative_adp_estimated_edges problem))\<^sup>*"
  using path source
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step middle successor)
  have middle: "middle \<in> set problem"
    using step.hyps(2) unfolding relative_adp_dependency_graph_def by blast
  have successor: "successor \<in> set problem"
    using step.hyps(2) unfolding relative_adp_dependency_graph_def by blast
  have estimated: "(relative_adp_pair_index problem middle,
      relative_adp_pair_index problem successor) \<in>
      set (relative_adp_estimated_edges problem)"
    by (rule relative_adp_semantic_edge_in_estimated_edges[
        OF relative_adp_pair_index_correct(1)[OF middle]
          relative_adp_pair_index_correct(1)[OF successor]])
       (use step.hyps(2) relative_adp_pair_index_correct(2)[OF middle]
          relative_adp_pair_index_correct(2)[OF successor] in
          \<open>simp add: relative_adp_dependency_graph_def\<close>)
  show ?case
    by (rule rtrancl_into_rtrancl[OF step.IH[OF step.prems] estimated])
qed

lemma relative_adp_semantic_corridor_in_estimated_corridor:
  assumes source: "source_pair \<in> set problem"
    and middle: "middle_pair \<in> set problem"
    and target: "target_pair \<in> set problem"
    and prefix: "(source_pair,middle_pair) \<in>
      (relative_adp_dependency_graph (set problem))\<^sup>*"
    and suffix: "(middle_pair,target_pair) \<in>
      (relative_adp_dependency_graph (set problem))\<^sup>*"
  shows "middle_pair \<in> (\<lambda>i. problem ! i) `
    set (relative_adp_estimated_corridor problem
      (relative_adp_pair_index problem source_pair)
      (relative_adp_pair_index problem target_pair))"
proof -
  let ?middle = "relative_adp_pair_index problem middle_pair"
  have bound: "?middle < length problem"
    by (rule relative_adp_pair_index_correct(1)[OF middle])
  have prefix_estimated:
      "(relative_adp_pair_index problem source_pair,?middle) \<in>
        (set (relative_adp_estimated_edges problem))\<^sup>*"
    by (rule relative_adp_semantic_path_in_estimated_path[OF source prefix])
  have suffix_estimated:
      "(?middle,relative_adp_pair_index problem target_pair) \<in>
        (set (relative_adp_estimated_edges problem))\<^sup>*"
    by (rule relative_adp_semantic_path_in_estimated_path[OF middle suffix])
  have in_corridor: "?middle \<in>
      set (relative_adp_estimated_corridor problem
        (relative_adp_pair_index problem source_pair)
        (relative_adp_pair_index problem target_pair))"
    unfolding relative_adp_estimated_corridor_set
    using bound prefix_estimated suffix_estimated by blast
  have nth: "problem ! ?middle = middle_pair"
    by (rule relative_adp_pair_index_correct(2)[OF middle])
  have "problem ! ?middle \<in> (\<lambda>i. problem ! i) `
      set (relative_adp_estimated_corridor problem
        (relative_adp_pair_index problem source_pair)
        (relative_adp_pair_index problem target_pair))"
    by (rule imageI[OF in_corridor])
  then show ?thesis unfolding nth .
qed

definition relative_adp_problem_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list" where
  "relative_adp_problem_list P B = remdups (P @ B)"

definition relative_adp_lasso_problem_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list" where
  "relative_adp_lasso_problem_list P B =
    remdups (map erase_annotations_adp P @ B)"

lemma relative_adp_problem_list_set:
  "set (relative_adp_problem_list P B) = set P \<union> set B"
  unfolding relative_adp_problem_list_def by simp

lemma relative_adp_lasso_problem_list_set:
  "set (relative_adp_lasso_problem_list P B) =
    relative_adp_lasso_graph_problem (set P) (set B)"
  unfolding relative_adp_lasso_problem_list_def
    relative_adp_lasso_graph_problem_def by auto

definition relative_adp_estimated_lasso_candidate ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('f, 'v) adp list" where
  "relative_adp_estimated_lasso_candidate P B component source target =
    (let problem = relative_adp_problem_list P B;
         lasso_problem = relative_adp_lasso_problem_list P B
     in remdups
       (map ((!) lasso_problem) component @
        map ((!) problem)
          (relative_adp_estimated_corridor problem source target)))"

definition relative_adp_estimated_lasso_candidates_for_component ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    nat list \<Rightarrow> ('f, 'v) adp list list" where
  "relative_adp_estimated_lasso_candidates_for_component P B component =
    (let problem = relative_adp_problem_list P B;
         lasso_problem = relative_adp_lasso_problem_list P B;
         component_pairs = ((!) lasso_problem) ` set component
     in [relative_adp_estimated_lasso_candidate P B component source target.
          source <- [0..<length problem],
          problem ! source \<in> set B \<and>
            problem ! source \<in> component_pairs \<and>
            relative_adp_branching_pair_list (problem ! source),
          target <- [0..<length problem],
          problem ! target \<in> set P \<and>
            target \<in> set (relative_adp_estimated_reachable problem source)])"

definition relative_adp_estimated_lasso_candidates ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list list" where
  "relative_adp_estimated_lasso_candidates P B =
    concat (map
      (relative_adp_estimated_lasso_candidates_for_component P B)
      (relative_adp_estimated_sccs
        (relative_adp_lasso_problem_list P B)))"

lemma relative_adp_estimated_lasso_candidate_set:
  "set (relative_adp_estimated_lasso_candidate P B component source target) =
    ((\<lambda>i. relative_adp_lasso_problem_list P B ! i) ` set component) \<union>
    ((\<lambda>i. relative_adp_problem_list P B ! i) `
      set (relative_adp_estimated_corridor
        (relative_adp_problem_list P B) source target))"
  unfolding relative_adp_estimated_lasso_candidate_def by (simp add: Let_def)

lemma relative_adp_estimated_lasso_candidate_in_global:
  assumes component: "component \<in> set (relative_adp_estimated_sccs
      (relative_adp_lasso_problem_list P B))"
    and source: "source < length (relative_adp_problem_list P B)"
      "relative_adp_problem_list P B ! source \<in> set B"
      "relative_adp_problem_list P B ! source \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P B ! i) ` set component"
      "relative_adp_branching_pair
        (relative_adp_problem_list P B ! source)"
    and target: "target < length (relative_adp_problem_list P B)"
      "relative_adp_problem_list P B ! target \<in> set P"
      "target \<in> set (relative_adp_estimated_reachable
        (relative_adp_problem_list P B) source)"
  shows "relative_adp_estimated_lasso_candidate P B component source target
    \<in> set (relative_adp_estimated_lasso_candidates P B)"
proof -
  have source_guard: "source \<in>
      set [0..<length (relative_adp_problem_list P B)] \<and>
      relative_adp_problem_list P B ! source \<in> set B \<and>
      relative_adp_problem_list P B ! source \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P B ! i) ` set component \<and>
      relative_adp_branching_pair_list
        (relative_adp_problem_list P B ! source)"
    using source unfolding relative_adp_branching_pair_list_sound by simp
  have target_guard: "target \<in>
      set [0..<length (relative_adp_problem_list P B)] \<and>
      relative_adp_problem_list P B ! target \<in> set P \<and>
      target \<in> set (relative_adp_estimated_reachable
        (relative_adp_problem_list P B) source)"
    using target by simp
  have local: "relative_adp_estimated_lasso_candidate P B component source target
      \<in> set (relative_adp_estimated_lasso_candidates_for_component
        P B component)"
    unfolding relative_adp_estimated_lasso_candidates_for_component_def
    apply (simp add: Let_def)
    apply (rule bexI[where x=source])
     apply (rule bexI[where x=target])
      apply simp
     apply (use target_guard in auto)
    apply (use source_guard in auto)
    done
  show ?thesis
    unfolding relative_adp_estimated_lasso_candidates_def
    using component local by auto
qed

theorem relative_adp_pair_stream_eventual_estimated_scc:
  assumes nodes: "\<And>n. pair_stream n \<in> set problem"
    and edges: "\<And>n. relative_adp_dependency_edge (set problem)
      (pair_stream n) (pair_stream (Suc n))"
  obtains component N where
    "component \<in> set (relative_adp_estimated_sccs problem)"
    "\<And>n. N \<le> n \<Longrightarrow>
      pair_stream n \<in> (\<lambda>i. problem ! i) ` set component"
proof -
  let ?indices = "\<lambda>n. relative_adp_pair_index problem (pair_stream n)"
  have index_bounds: "\<And>n. ?indices n < length problem"
    by (rule relative_adp_pair_index_correct(1)[OF nodes])
  have index_pair: "\<And>n. problem ! ?indices n = pair_stream n"
    by (rule relative_adp_pair_index_correct(2)[OF nodes])
  have index_edges: "\<And>n. (?indices n, ?indices (Suc n)) \<in>
      set (relative_adp_estimated_edges problem)"
  proof -
    fix n
    show "(?indices n, ?indices (Suc n)) \<in>
        set (relative_adp_estimated_edges problem)"
      by (rule relative_adp_semantic_edge_in_estimated_edges[OF
          index_bounds index_bounds])
         (use edges index_pair in simp)
  qed
  have witness: "\<exists>component N.
      component \<in> set (relative_adp_estimated_sccs problem) \<and>
      (\<forall>n. N \<le> n \<longrightarrow> ?indices n \<in> set component)"
  proof (rule relative_adp_estimated_path_eventual_scc[
      where node_stream="?indices" and problem=problem,
      OF index_bounds index_edges])
    fix component N
    assume component: "component \<in>
        set (relative_adp_estimated_sccs problem)"
      and eventual: "\<And>n. N \<le> n \<Longrightarrow> ?indices n \<in> set component"
    show "\<exists>component N.
        component \<in> set (relative_adp_estimated_sccs problem) \<and>
        (\<forall>n. N \<le> n \<longrightarrow> ?indices n \<in> set component)"
      by (rule exI[of _ component], rule exI[of _ N])
         (use component eventual in blast)
  qed
  from witness obtain component N where component:
      "component \<in> set (relative_adp_estimated_sccs problem)"
    and eventual: "\<And>n. N \<le> n \<Longrightarrow> ?indices n \<in> set component"
    by blast
  have pair_eventual: "\<And>n. N \<le> n \<Longrightarrow>
      pair_stream n \<in> (\<lambda>i. problem ! i) ` set component"
  proof -
    fix n
    assume "N \<le> n"
    then have "?indices n \<in> set component" by (rule eventual)
    moreover have "pair_stream n = problem ! ?indices n"
      using index_pair[of n] by simp
    ultimately show "pair_stream n \<in>
        (\<lambda>i. problem ! i) ` set component" by blast
  qed
  show thesis by (rule that[OF component pair_eventual])
qed

theorem relative_adp_selected_estimated_main_scc_child_not_SN:
  assumes problem: "set problem = A"
    and main: "INFM n.
      relative_adp_selected_chain_main_event P A terms (origin_path n)"
    and path_edge: "\<And>n. (origin_path n, origin_path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>n. (terms n, terms (Suc n)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains component where
    "component \<in> set (relative_adp_estimated_sccs problem)"
    "((\<lambda>i. problem ! i) ` set component) \<inter> P \<noteq> {}"
    "\<not> adp_problem_SN
      (P \<inter> ((\<lambda>i. problem ! i) ` set component),
       (((\<lambda>i. problem ! i) ` set component) \<union>
          erase_annotations_adp `
            (A - ((\<lambda>i. problem ! i) ` set component))) -
        (P \<inter> ((\<lambda>i. problem ! i) ` set component)))"
proof -
  let ?indices = "relative_adp_selected_label_indices P A terms origin_path"
  let ?labels = "relative_adp_selected_label_stream P A terms origin_path"
  have infinite: "infinite ?indices"
  proof -
    have main_infinite:
        "infinite {n. relative_adp_selected_chain_main_event P A terms
          (origin_path n)}"
      using main unfolding INFM_iff_infinite .
    have inclusion:
        "{n. relative_adp_selected_chain_main_event P A terms (origin_path n)}
          \<subseteq> ?indices"
      unfolding relative_adp_selected_chain_main_event_iff_node_label
        relative_adp_selected_label_indices_def by blast
    show ?thesis by (rule infinite_super[OF inclusion main_infinite])
  qed
  have labels_in_problem: "\<And>n. ?labels n \<in> set problem"
    using relative_adp_selected_label_stream_in_problem[
      OF infinite steps subset] unfolding problem by blast
  have label_edges: "\<And>n. relative_adp_dependency_edge (set problem)
      (?labels n) (?labels (Suc n))"
    using relative_adp_selected_label_stream_dependency_edge[
      OF infinite path_edge steps subset lhs_fun]
    unfolding problem .
  have witness: "\<exists>component N.
      component \<in> set (relative_adp_estimated_sccs problem) \<and>
      (\<forall>n. N \<le> n \<longrightarrow>
        ?labels n \<in> (\<lambda>i. problem ! i) ` set component)"
  proof (rule relative_adp_pair_stream_eventual_estimated_scc[
      where pair_stream="?labels" and problem=problem,
      OF labels_in_problem label_edges])
    fix component N
    assume component:
        "component \<in> set (relative_adp_estimated_sccs problem)"
      and eventual: "\<And>n. N \<le> n \<Longrightarrow>
        ?labels n \<in> (\<lambda>i. problem ! i) ` set component"
    show "\<exists>component N.
        component \<in> set (relative_adp_estimated_sccs problem) \<and>
        (\<forall>n. N \<le> n \<longrightarrow>
          ?labels n \<in> (\<lambda>i. problem ! i) ` set component)"
      by (rule exI[of _ component], rule exI[of _ N])
         (use component eventual in blast)
  qed
  from witness obtain component N where component:
      "component \<in> set (relative_adp_estimated_sccs problem)"
    and eventual: "\<And>n. N \<le> n \<Longrightarrow>
      ?labels n \<in> (\<lambda>i. problem ! i) ` set component"
    by blast
  let ?Q = "(\<lambda>i. problem ! i) ` set component"
  have main_stream: "INFM n. ?labels n \<in> P"
    by (rule relative_adp_selected_main_events_give_main_label_stream[OF main])
  from main_stream[unfolded INFM_nat]
  obtain n where Nn: "N < n" and in_P: "?labels n \<in> P" by blast
  have in_Q: "?labels n \<in> ?Q" by (rule eventual) (use Nn in simp)
  have intersects: "?Q \<inter> P \<noteq> {}" using in_P in_Q by blast
  have child: "\<not> adp_problem_SN
      (P \<inter> ?Q, (?Q \<union> erase_annotations_adp ` (A - ?Q)) - (P \<inter> ?Q))"
    by (rule relative_adp_selected_main_component_child_not_SN[
        OF main path_edge steps subset infinite eventual])
  show thesis by (rule that[OF component intersects child])
qed

end
