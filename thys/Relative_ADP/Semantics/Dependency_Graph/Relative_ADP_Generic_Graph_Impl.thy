theory Relative_ADP_Generic_Graph_Impl
  imports Relative_ADP_Dependency_Graph Auxx.Gabow_SCC_RBT "Transitive-Closure-II.RTrancl"
begin

text \<open>The executable graph functions are total definitions independent of
estimator correctness. The locale below supplies bounds and edge coverage only
for their soundness proofs. Both checked estimators use these same functions.\<close>

definition relative_adp_estimated_edges ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> (nat \<times> nat) list" where
  "(relative_adp_estimated_edges estimated_successors) problem = concat
    (map (\<lambda>source. map (Pair source)
      (estimated_successors problem source))
      [0..<length problem])"

definition relative_adp_reflexive_estimated_edges ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> (nat \<times> nat) list" where
  "(relative_adp_reflexive_estimated_edges estimated_successors) problem =
    map (\<lambda>i. (i,i)) [0..<length problem] @
      (relative_adp_estimated_edges estimated_successors) problem"

definition relative_adp_estimated_sccs ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> nat list list" where
  "(relative_adp_estimated_sccs estimated_successors) problem =
    scc_decomp ((relative_adp_reflexive_estimated_edges estimated_successors) problem)"

definition relative_adp_index_successors ::
  "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_index_successors edges source =
    map snd (filter (\<lambda>edge. fst edge = source) edges)"

definition relative_adp_estimated_reachable ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> nat \<Rightarrow> nat list" where
  "(relative_adp_estimated_reachable estimated_successors) problem source =
    mk_rtrancl_list (=)
      (relative_adp_index_successors
        ((relative_adp_estimated_edges estimated_successors) problem)) [source]"

definition relative_adp_index_predecessors ::
  "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "relative_adp_index_predecessors edges target =
    map fst (filter (\<lambda>edge. snd edge = target) edges)"

definition relative_adp_estimated_coreachable ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> nat \<Rightarrow> nat list" where
  "(relative_adp_estimated_coreachable estimated_successors) problem target =
    mk_rtrancl_list (=)
      (relative_adp_index_predecessors
        ((relative_adp_estimated_edges estimated_successors) problem)) [target]"

definition relative_adp_estimated_corridor ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "(relative_adp_estimated_corridor estimated_successors) problem source target =
    filter (\<lambda>middle.
      middle \<in> set ((relative_adp_estimated_reachable estimated_successors) problem source) \<and>
      middle \<in> set ((relative_adp_estimated_coreachable estimated_successors) problem target))
      [0..<length problem]"

definition relative_adp_pair_index ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp \<Rightarrow> nat" where
  "relative_adp_pair_index problem pair =
    (SOME i. i < length problem \<and> problem ! i = pair)"

definition relative_adp_problem_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list" where
  "relative_adp_problem_list P B = remdups (P @ B)"

definition relative_adp_lasso_problem_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list" where
  "relative_adp_lasso_problem_list P B =
    remdups (map erase_annotations_adp P @ B)"

definition relative_adp_estimated_lasso_candidate ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('f, 'v) adp list" where
  "(relative_adp_estimated_lasso_candidate estimated_successors) P B component source target =
    (let problem = relative_adp_problem_list P B;
         lasso_problem = relative_adp_lasso_problem_list P B
     in remdups
       (map ((!) lasso_problem) component @
        map ((!) problem)
          ((relative_adp_estimated_coreachable estimated_successors) problem source) @
        map ((!) problem)
          ((relative_adp_estimated_corridor estimated_successors) problem source target)))"

definition relative_adp_estimated_lasso_candidates_for_component ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    nat list \<Rightarrow> ('f, 'v) adp list list" where
  "(relative_adp_estimated_lasso_candidates_for_component estimated_successors) P B component =
    (let problem = relative_adp_problem_list P B;
         lasso_problem = relative_adp_lasso_problem_list P B;
         component_pairs = map ((!) lasso_problem) component
     in [(relative_adp_estimated_lasso_candidate estimated_successors) P B component source target.
          source <- [0..<length problem],
          problem ! source \<in> set B \<and>
            problem ! source \<in> set component_pairs \<and>
            relative_adp_branching_pair_list (problem ! source),
          target <- [0..<length problem],
          problem ! target \<in> set P \<and>
            target \<in> set ((relative_adp_estimated_reachable estimated_successors) problem source)])"

definition relative_adp_estimated_lasso_candidates ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list list" where
  "(relative_adp_estimated_lasso_candidates estimated_successors) P B =
    concat (map
      ((relative_adp_estimated_lasso_candidates_for_component estimated_successors) P B)
      ((relative_adp_estimated_sccs estimated_successors)
        (relative_adp_lasso_problem_list P B)))"

definition relative_adp_estimated_main_scc_candidates ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list list" where
  "(relative_adp_estimated_main_scc_candidates estimated_successors) P B =
    (let problem = relative_adp_problem_list P B
     in [map ((!) problem) component.
          component <- (relative_adp_estimated_sccs estimated_successors) problem,
          list_ex (\<lambda>pair. pair \<in> set P)
            (map ((!) problem) component)])"

definition relative_adp_estimated_graph_candidates ::
  "(('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list) \<Rightarrow>
    ('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
    ('f, 'v) adp list list" where
  "(relative_adp_estimated_graph_candidates estimated_successors) P B =
    remdups ((relative_adp_estimated_main_scc_candidates estimated_successors) P B @
      (relative_adp_estimated_lasso_candidates estimated_successors) P B)"

locale relative_adp_graph_estimator =
  fixes estimated_successors :: "('f,'v) adp list \<Rightarrow> nat \<Rightarrow> nat list"
  assumes estimated_successors_bounds:
    "target \<in> set (estimated_successors problem source) \<Longrightarrow> target < length problem"
  and estimated_successors_sound:
    "source < length problem \<Longrightarrow> target < length problem \<Longrightarrow>
      relative_adp_dependency_edge (set problem) (problem ! source) (problem ! target) \<Longrightarrow>
      target \<in> set (estimated_successors problem source)"
begin

abbreviation relative_adp_estimated_edges where
  "relative_adp_estimated_edges \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_edges estimated_successors"

lemmas relative_adp_estimated_edges_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_edges_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_reflexive_estimated_edges where
  "relative_adp_reflexive_estimated_edges \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_reflexive_estimated_edges estimated_successors"

lemmas relative_adp_reflexive_estimated_edges_def = Relative_ADP_Generic_Graph_Impl.relative_adp_reflexive_estimated_edges_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_estimated_sccs where
  "relative_adp_estimated_sccs \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_sccs estimated_successors"

lemmas relative_adp_estimated_sccs_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_sccs_def[where estimated_successors=estimated_successors]

lemmas relative_adp_index_successors_def = Relative_ADP_Generic_Graph_Impl.relative_adp_index_successors_def

abbreviation relative_adp_estimated_reachable where
  "relative_adp_estimated_reachable \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_reachable estimated_successors"

lemmas relative_adp_estimated_reachable_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_reachable_def[where estimated_successors=estimated_successors]

lemmas relative_adp_index_predecessors_def = Relative_ADP_Generic_Graph_Impl.relative_adp_index_predecessors_def

abbreviation relative_adp_estimated_coreachable where
  "relative_adp_estimated_coreachable \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_coreachable estimated_successors"

lemmas relative_adp_estimated_coreachable_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_coreachable_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_estimated_corridor where
  "relative_adp_estimated_corridor \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_corridor estimated_successors"

lemmas relative_adp_estimated_corridor_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_corridor_def[where estimated_successors=estimated_successors]

lemmas relative_adp_pair_index_def = Relative_ADP_Generic_Graph_Impl.relative_adp_pair_index_def

lemmas relative_adp_problem_list_def = Relative_ADP_Generic_Graph_Impl.relative_adp_problem_list_def

lemmas relative_adp_lasso_problem_list_def = Relative_ADP_Generic_Graph_Impl.relative_adp_lasso_problem_list_def

abbreviation relative_adp_estimated_lasso_candidate where
  "relative_adp_estimated_lasso_candidate \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_lasso_candidate estimated_successors"

lemmas relative_adp_estimated_lasso_candidate_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_lasso_candidate_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_estimated_lasso_candidates_for_component where
  "relative_adp_estimated_lasso_candidates_for_component \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_lasso_candidates_for_component estimated_successors"

lemmas relative_adp_estimated_lasso_candidates_for_component_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_lasso_candidates_for_component_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_estimated_lasso_candidates where
  "relative_adp_estimated_lasso_candidates \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_lasso_candidates estimated_successors"

lemmas relative_adp_estimated_lasso_candidates_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_lasso_candidates_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_estimated_main_scc_candidates where
  "relative_adp_estimated_main_scc_candidates \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_main_scc_candidates estimated_successors"

lemmas relative_adp_estimated_main_scc_candidates_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_main_scc_candidates_def[where estimated_successors=estimated_successors]

abbreviation relative_adp_estimated_graph_candidates where
  "relative_adp_estimated_graph_candidates \<equiv> Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_graph_candidates estimated_successors"

lemmas relative_adp_estimated_graph_candidates_def = Relative_ADP_Generic_Graph_Impl.relative_adp_estimated_graph_candidates_def[where estimated_successors=estimated_successors]


text \<open>
  Executable indexed estimated graph and SCC decomposition. Reflexive edges
  keep isolated nodes in Gabow's nontrivial-SCC interface without changing
  mutual reachability.
\<close>




lemma relative_adp_estimated_edges_iff:
  "(source,target) \<in> set (relative_adp_estimated_edges problem) \<longleftrightarrow>
    source < length problem \<and>
    target \<in> set (estimated_successors problem source)"
  unfolding relative_adp_estimated_edges_def by auto

lemma relative_adp_estimated_edge_bounds:
  assumes "(source,target) \<in> set (relative_adp_estimated_edges problem)"
  shows "source < length problem" "target < length problem"
  using assms estimated_successors_bounds
  unfolding relative_adp_estimated_edges_iff by auto


lemma relative_adp_index_successors_set:
  "set (relative_adp_index_successors edges source) =
    {target. (source,target) \<in> set edges}"
  unfolding relative_adp_index_successors_def by auto


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


lemma relative_adp_index_predecessors_set:
  "set (relative_adp_index_predecessors edges target) =
    {source. (source,target) \<in> set edges}"
  unfolding relative_adp_index_predecessors_def by auto


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
  using source estimated_successors_sound[
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

lemma relative_adp_selected_labeled_node_label_in_problem:
  assumes labeled:
      "relative_adp_selected_chain_labeled P A terms node"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "relative_adp_selected_chain_node_label P A terms node \<in> A"
proof -
  obtain i q where node: "node = (i,q)" by (cases node) auto
  have label: "relative_adp_selected_chain_label P A terms (i,q)
      (relative_adp_selected_chain_node_label P A terms node)"
    using relative_adp_selected_chain_labeled_has_node_label[OF labeled]
    unfolding node .
  show ?thesis
    by (rule relative_adp_selected_label_in_problem[
        where i=i and q=q, OF steps[of i] subset label])
qed

lemma relative_adp_selected_event_segment_dependency_graph_edge:
  assumes segment: "(source_node,target_node) \<in> event_segment
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_labeled P A terms)"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "(relative_adp_selected_chain_node_label P A terms source_node,
      relative_adp_selected_chain_node_label P A terms target_node) \<in>
    relative_adp_dependency_graph A"
proof -
  have source_labeled:
      "relative_adp_selected_chain_labeled P A terms source_node"
    and target_labeled:
      "relative_adp_selected_chain_labeled P A terms target_node"
    using segment unfolding event_segment_def by auto
  have source_in: "relative_adp_selected_chain_node_label P A terms
      source_node \<in> A"
    by (rule relative_adp_selected_labeled_node_label_in_problem[
        OF source_labeled steps subset])
  have target_in: "relative_adp_selected_chain_node_label P A terms
      target_node \<in> A"
    by (rule relative_adp_selected_labeled_node_label_in_problem[
        OF target_labeled steps subset])
  have edge: "relative_adp_dependency_edge A
      (relative_adp_selected_chain_node_label P A terms source_node)
      (relative_adp_selected_chain_node_label P A terms target_node)"
    by (rule relative_adp_selected_event_segment_dependency_edge[
        OF segment steps subset lhs_fun])
  show ?thesis using source_in target_in edge
    unfolding relative_adp_dependency_graph_def by simp
qed

lemma relative_adp_selected_labeled_origin_path_dependency_graph_path:
  assumes origin: "(source_node,target_node) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
    and source_labeled:
      "relative_adp_selected_chain_labeled P A terms source_node"
    and target_labeled:
      "relative_adp_selected_chain_labeled P A terms target_node"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "(relative_adp_selected_chain_node_label P A terms source_node,
      relative_adp_selected_chain_node_label P A terms target_node) \<in>
    (relative_adp_dependency_graph A)\<^sup>*"
proof -
  have compressed: "(source_node,target_node) \<in> (event_segment
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_labeled P A terms))\<^sup>*"
    by (rule rtrancl_between_events_compresses[
        OF origin source_labeled target_labeled])
  show ?thesis using compressed
  proof (induction rule: rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step middle_node successor_node)
    have edge: "(relative_adp_selected_chain_node_label P A terms middle_node,
        relative_adp_selected_chain_node_label P A terms successor_node) \<in>
      relative_adp_dependency_graph A"
      by (rule relative_adp_selected_event_segment_dependency_graph_edge[
          OF step.hyps(2) steps subset lhs_fun])
    show ?case by (rule rtrancl_into_rtrancl[OF step.IH edge])
  qed
qed

lemma rtrancl_path_edge_mono:
  assumes path: "(start,finish) \<in> E\<^sup>*"
    and retained: "\<And>source target.
      (source,target) \<in> E \<Longrightarrow>
      (start,source) \<in> E\<^sup>* \<Longrightarrow>
      (target,finish) \<in> E\<^sup>* \<Longrightarrow>
      (source,target) \<in> R"
  shows "(start,finish) \<in> R\<^sup>*"
proof -
  have suffix: "(middle,finish) \<in> E\<^sup>* \<Longrightarrow>
      (start,middle) \<in> E\<^sup>* \<Longrightarrow>
      (middle,finish) \<in> R\<^sup>*" for middle
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step source target)
    have prefix_target: "(start,target) \<in> E\<^sup>*"
      by (rule rtrancl_into_rtrancl[OF step.prems step.hyps(1)])
    have edge: "(source,target) \<in> R"
      by (rule retained[OF step.hyps(1) step.prems step.hyps(2)])
    have tail: "(target,finish) \<in> R\<^sup>*"
      by (rule step.IH[OF prefix_target])
    show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF edge] tail])
  qed
  show ?thesis by (rule suffix[OF path]) simp
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

lemma relative_adp_selected_origin_path_retained_by_estimated_corridor:
  assumes problem: "set problem = A"
    and origin: "(source_node,target_node) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
    and source_labeled:
      "relative_adp_selected_chain_labeled P A terms source_node"
    and target_labeled:
      "relative_adp_selected_chain_labeled P A terms target_node"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
    and corridor: "(\<lambda>i. problem ! i) `
      set (relative_adp_estimated_corridor problem
        (relative_adp_pair_index problem
          (relative_adp_selected_chain_node_label P A terms source_node))
        (relative_adp_pair_index problem
          (relative_adp_selected_chain_node_label P A terms target_node))) \<subseteq> Q"
  shows "(source_node,target_node) \<in>
    (relative_adp_selected_retained_origin_edge Q P A terms)\<^sup>*"
proof (rule rtrancl_path_edge_mono[
    where E="relative_adp_selected_chain_origin_edge P A terms",
    OF origin])
  fix middle_node successor_node
  assume edge: "(middle_node,successor_node) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and prefix_nodes: "(source_node,middle_node) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
    and suffix_nodes: "(successor_node,target_node) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
  have middle_to_target: "(middle_node,target_node) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
    by (rule rtrancl_trans[OF r_into_rtrancl[OF edge] suffix_nodes])
  show "(middle_node,successor_node) \<in>
      relative_adp_selected_retained_origin_edge Q P A terms"
  proof (cases "relative_adp_selected_chain_labeled P A terms middle_node")
    case False
    show ?thesis using edge False
      unfolding relative_adp_selected_retained_origin_edge_def by simp
  next
    case True
    let ?source_pair =
      "relative_adp_selected_chain_node_label P A terms source_node"
    let ?middle_pair =
      "relative_adp_selected_chain_node_label P A terms middle_node"
    let ?target_pair =
      "relative_adp_selected_chain_node_label P A terms target_node"
    have source_in: "?source_pair \<in> set problem"
      using relative_adp_selected_labeled_node_label_in_problem[
        OF source_labeled steps subset] unfolding problem .
    have middle_in: "?middle_pair \<in> set problem"
      using relative_adp_selected_labeled_node_label_in_problem[
        OF True steps subset] unfolding problem .
    have target_in: "?target_pair \<in> set problem"
      using relative_adp_selected_labeled_node_label_in_problem[
        OF target_labeled steps subset] unfolding problem .
    have prefix_graph: "(?source_pair,?middle_pair) \<in>
        (relative_adp_dependency_graph (set problem))\<^sup>*"
      using relative_adp_selected_labeled_origin_path_dependency_graph_path[
        OF prefix_nodes source_labeled True steps subset lhs_fun]
      unfolding problem .
    have suffix_graph: "(?middle_pair,?target_pair) \<in>
        (relative_adp_dependency_graph (set problem))\<^sup>*"
      using relative_adp_selected_labeled_origin_path_dependency_graph_path[
        OF middle_to_target True target_labeled steps subset lhs_fun]
      unfolding problem .
    have in_corridor: "?middle_pair \<in> (\<lambda>i. problem ! i) `
        set (relative_adp_estimated_corridor problem
          (relative_adp_pair_index problem ?source_pair)
          (relative_adp_pair_index problem ?target_pair))"
      by (rule relative_adp_semantic_corridor_in_estimated_corridor[
          OF source_in middle_in target_in prefix_graph suffix_graph])
    have in_Q: "?middle_pair \<in> Q" using corridor in_corridor by blast
    show ?thesis using edge True in_Q
      unfolding relative_adp_selected_retained_origin_edge_def by simp
  qed
qed



lemma relative_adp_problem_list_set:
  "set (relative_adp_problem_list P B) = set P \<union> set B"
  unfolding relative_adp_problem_list_def by simp

lemma relative_adp_lasso_problem_list_set:
  "set (relative_adp_lasso_problem_list P B) =
    relative_adp_lasso_graph_problem (set P) (set B)"
  unfolding relative_adp_lasso_problem_list_def
    relative_adp_lasso_graph_problem_def by auto






lemma relative_adp_estimated_lasso_candidate_set:
  "set (relative_adp_estimated_lasso_candidate P B component source target) =
    ((\<lambda>i. relative_adp_lasso_problem_list P B ! i) ` set component) \<union>
    ((\<lambda>i. relative_adp_problem_list P B ! i) `
      set (relative_adp_estimated_coreachable
        (relative_adp_problem_list P B) source)) \<union>
    ((\<lambda>i. relative_adp_problem_list P B ! i) `
      set (relative_adp_estimated_corridor
        (relative_adp_problem_list P B) source target))"
  unfolding relative_adp_estimated_lasso_candidate_def
  by (simp add: Let_def Un_assoc)

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

theorem relative_adp_selected_offshoot_covered_by_lasso_candidate:
  assumes P_def: "P = set P_list"
    and B_def: "B = set B_list"
    and A_def: "A = P \<union> B"
    and component: "component \<in> set (relative_adp_estimated_sccs
      (relative_adp_lasso_problem_list P_list B_list))"
    and source_labeled:
      "relative_adp_selected_chain_labeled P A terms source_node"
    and source_B:
      "relative_adp_selected_chain_node_label P A terms source_node \<in> B"
    and source_component:
      "relative_adp_selected_chain_node_label P A terms source_node \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
          set component"
    and branching: "relative_adp_branching_pair
      (relative_adp_selected_chain_node_label P A terms source_node)"
    and origin: "(source_node,target_node) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
    and main:
      "relative_adp_selected_chain_main_event P A terms target_node"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains Q where
    "Q = relative_adp_estimated_lasso_candidate P_list B_list component
      (relative_adp_pair_index (relative_adp_problem_list P_list B_list)
        (relative_adp_selected_chain_node_label P A terms source_node))
      (relative_adp_pair_index (relative_adp_problem_list P_list B_list)
        (relative_adp_selected_chain_node_label P A terms target_node))"
    "Q \<in> set (relative_adp_estimated_lasso_candidates P_list B_list)"
    "relative_adp_selected_retained_main_reachable
      (set Q) P A terms source_node"
proof -
  let ?problem = "relative_adp_problem_list P_list B_list"
  let ?source_pair =
    "relative_adp_selected_chain_node_label P A terms source_node"
  let ?target_pair =
    "relative_adp_selected_chain_node_label P A terms target_node"
  let ?source = "relative_adp_pair_index ?problem ?source_pair"
  let ?target = "relative_adp_pair_index ?problem ?target_pair"
  let ?Q = "relative_adp_estimated_lasso_candidate
    P_list B_list component ?source ?target"
  have problem: "set ?problem = A"
    unfolding relative_adp_problem_list_set A_def P_def B_def by simp
  have subset: "P \<subseteq> A" unfolding A_def by blast
  have target_labeled:
      "relative_adp_selected_chain_labeled P A terms target_node"
    using main
    unfolding relative_adp_selected_chain_main_event_iff_node_label by blast
  have source_in: "?source_pair \<in> set ?problem"
    using relative_adp_selected_labeled_node_label_in_problem[
      OF source_labeled steps subset] unfolding problem .
  have target_in: "?target_pair \<in> set ?problem"
    using relative_adp_selected_labeled_node_label_in_problem[
      OF target_labeled steps subset] unfolding problem .
  have target_P: "?target_pair \<in> P"
    using main
    unfolding relative_adp_selected_chain_main_event_iff_node_label by simp
  have dependency_path: "(?source_pair,?target_pair) \<in>
      (relative_adp_dependency_graph (set ?problem))\<^sup>*"
    using relative_adp_selected_labeled_origin_path_dependency_graph_path[
      OF origin source_labeled target_labeled steps subset lhs_fun]
    unfolding problem .
  have estimated_path: "(?source,?target) \<in>
      (set (relative_adp_estimated_edges ?problem))\<^sup>*"
    by (rule relative_adp_semantic_path_in_estimated_path[
        OF source_in dependency_path])
  have target_reachable:
      "?target \<in> set (relative_adp_estimated_reachable ?problem ?source)"
    unfolding relative_adp_estimated_reachable_set
    using estimated_path by blast
  have source_bound: "?source < length ?problem"
    by (rule relative_adp_pair_index_correct(1)[OF source_in])
  have target_bound: "?target < length ?problem"
    by (rule relative_adp_pair_index_correct(1)[OF target_in])
  have source_nth: "?problem ! ?source = ?source_pair"
    by (rule relative_adp_pair_index_correct(2)[OF source_in])
  have target_nth: "?problem ! ?target = ?target_pair"
    by (rule relative_adp_pair_index_correct(2)[OF target_in])
  have candidate: "?Q \<in>
      set (relative_adp_estimated_lasso_candidates P_list B_list)"
    by (rule relative_adp_estimated_lasso_candidate_in_global[
        OF component source_bound])
       (use source_B source_component branching target_bound target_P
          target_reachable source_nth target_nth P_def B_def in auto)
  have corridor_subset: "(\<lambda>i. ?problem ! i) `
      set (relative_adp_estimated_corridor ?problem ?source ?target)
      \<subseteq> set ?Q"
    unfolding relative_adp_estimated_lasso_candidate_set by blast
  have retained: "(source_node,target_node) \<in>
      (relative_adp_selected_retained_origin_edge (set ?Q) P A terms)\<^sup>*"
    by (rule relative_adp_selected_origin_path_retained_by_estimated_corridor[
        OF problem origin source_labeled target_labeled steps subset lhs_fun
          corridor_subset])
  have target_in_corridor: "?target_pair \<in> (\<lambda>i. ?problem ! i) `
      set (relative_adp_estimated_corridor ?problem ?source ?target)"
    by (rule relative_adp_semantic_corridor_in_estimated_corridor[
        OF source_in target_in target_in dependency_path]) simp
  have target_Q: "?target_pair \<in> set ?Q"
    using corridor_subset target_in_corridor by blast
  have reachable: "relative_adp_selected_retained_main_reachable
      (set ?Q) P A terms source_node"
    unfolding relative_adp_selected_retained_main_reachable_def
    using retained main target_Q by blast
  show thesis
    by (rule that[where Q="?Q", OF _ candidate reachable]) simp
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

theorem relative_adp_selected_base_stream_eventual_estimated_scc:
  assumes P_def: "P = set P_list"
    and B_def: "B = set B_list"
    and A_def: "A = P \<union> B"
    and infinite: "infinite
      (relative_adp_selected_label_indices P A terms origin_path)"
    and no_main: "\<not> (INFM n.
      relative_adp_selected_chain_main_event P A terms (origin_path n))"
    and path_edge: "\<And>n. (origin_path n, origin_path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains component N where
    "component \<in> set (relative_adp_estimated_sccs
      (relative_adp_lasso_problem_list P_list B_list))"
    "\<And>n. N \<le> n \<Longrightarrow>
      relative_adp_selected_label_stream P A terms origin_path n \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
          set component"
proof -
  let ?labels =
    "relative_adp_selected_label_stream P A terms origin_path"
  let ?lasso_problem = "relative_adp_lasso_problem_list P_list B_list"
  have subset: "P \<subseteq> A" unfolding A_def by blast
  have base_witness: "\<exists>K. \<forall>n. K \<le> n \<longrightarrow> ?labels n \<in> A - P"
  proof (rule relative_adp_selected_no_main_eventual_base_stream[
      OF infinite no_main steps subset])
    fix K
    assume base: "\<And>n. K \<le> n \<Longrightarrow> ?labels n \<in> A - P"
    show "\<exists>K. \<forall>n. K \<le> n \<longrightarrow> ?labels n \<in> A - P"
      by (rule exI[of _ K]) (use base in blast)
  qed
  from base_witness obtain K where
    base: "\<And>n. K \<le> n \<Longrightarrow> ?labels n \<in> A - P" by blast
  have late_B: "\<And>n. K \<le> n \<Longrightarrow> ?labels n \<in> B"
    using base unfolding A_def by blast
  let ?shifted = "\<lambda>n. ?labels (K+n)"
  have shifted_nodes: "\<And>n. ?shifted n \<in> set ?lasso_problem"
    using late_B[of "K+_", simplified]
    unfolding relative_adp_lasso_problem_list_set
      relative_adp_lasso_graph_problem_def B_def by blast
  have erased_problem:
      "erase_annotations_adp ` A = erase_annotations_adp ` set ?lasso_problem"
    unfolding relative_adp_lasso_problem_list_set
      relative_adp_lasso_graph_problem_erasure A_def P_def B_def by simp
  have shifted_edges: "\<And>n. relative_adp_dependency_edge
      (set ?lasso_problem) (?shifted n) (?shifted (Suc n))"
  proof -
    fix n
    have original: "relative_adp_dependency_edge A
        (?labels (K+n)) (?labels (Suc (K+n)))"
      by (rule relative_adp_selected_label_stream_dependency_edge[
          OF infinite path_edge steps subset lhs_fun])
    have transferred: "relative_adp_dependency_edge (set ?lasso_problem)
        (?labels (K+n)) (?labels (Suc (K+n)))"
      by (rule relative_adp_dependency_edge_erasure_cong[
          OF erased_problem, THEN iffD1, OF original])
    show "relative_adp_dependency_edge (set ?lasso_problem)
        (?shifted n) (?shifted (Suc n))"
      using transferred by simp
  qed
  have witness: "\<exists>component M.
      component \<in> set (relative_adp_estimated_sccs ?lasso_problem) \<and>
      (\<forall>n. M \<le> n \<longrightarrow>
        ?shifted n \<in> (\<lambda>i. ?lasso_problem ! i) ` set component)"
  proof (rule relative_adp_pair_stream_eventual_estimated_scc[
      where pair_stream="?shifted" and problem="?lasso_problem",
      OF shifted_nodes shifted_edges])
    fix component M
    assume component:
        "component \<in> set (relative_adp_estimated_sccs ?lasso_problem)"
      and eventual: "\<And>n. M \<le> n \<Longrightarrow>
        ?shifted n \<in> (\<lambda>i. ?lasso_problem ! i) ` set component"
    show "\<exists>component M.
        component \<in> set (relative_adp_estimated_sccs ?lasso_problem) \<and>
        (\<forall>n. M \<le> n \<longrightarrow>
          ?shifted n \<in> (\<lambda>i. ?lasso_problem ! i) ` set component)"
      by (rule exI[of _ component], rule exI[of _ M])
         (use component eventual in blast)
  qed
  from witness obtain component M where component:
      "component \<in> set (relative_adp_estimated_sccs ?lasso_problem)"
    and shifted_eventual: "\<And>n. M \<le> n \<Longrightarrow>
      ?shifted n \<in> (\<lambda>i. ?lasso_problem ! i) ` set component"
    by blast
  have eventual: "\<And>n. K+M \<le> n \<Longrightarrow>
      ?labels n \<in> (\<lambda>i. ?lasso_problem ! i) ` set component"
  proof -
    fix n
    assume KMn: "K+M \<le> n"
    have n: "K + (n-K) = n" using KMn by simp
    have M: "M \<le> n-K" using KMn by simp
    have "?labels (K + (n-K)) \<in>
        (\<lambda>i. ?lasso_problem ! i) ` set component"
      by (rule shifted_eventual[OF M])
    then show "?labels n \<in> (\<lambda>i. ?lasso_problem ! i) ` set component"
      unfolding n .
  qed
  show thesis by (rule that[OF component eventual])
qed

lemma relative_adp_late_lasso_candidate_retains_base_path:
  assumes P_def: "P = set P_list"
    and B_def: "B = set B_list"
    and A_def: "A = P \<union> B"
    and infinite: "infinite
      (relative_adp_selected_label_indices P A terms origin_path)"
    and path_edge: "\<And>m. (origin_path m, origin_path (Suc m)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
    and eventual: "\<And>j. N \<le> j \<Longrightarrow>
      relative_adp_selected_label_stream P A terms origin_path j \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
          set component"
    and late: "N \<le> n"
  shows "\<And>m. (origin_path m, origin_path (Suc m)) \<in>
    relative_adp_selected_retained_origin_edge
      (set (relative_adp_estimated_lasso_candidate P_list B_list component
        (relative_adp_pair_index (relative_adp_problem_list P_list B_list)
          (relative_adp_selected_label_stream P A terms origin_path n))
        target_index)) P A terms"
proof -
  let ?I = "relative_adp_selected_label_indices P A terms origin_path"
  let ?labels = "relative_adp_selected_label_stream P A terms origin_path"
  let ?problem = "relative_adp_problem_list P_list B_list"
  let ?source_pair = "?labels n"
  let ?source = "relative_adp_pair_index ?problem ?source_pair"
  let ?Q = "set (relative_adp_estimated_lasso_candidate
    P_list B_list component ?source target_index)"
  have problem: "set ?problem = A"
    unfolding relative_adp_problem_list_set A_def P_def B_def by simp
  have subset: "P \<subseteq> A" unfolding A_def by blast
  have source_in: "?source_pair \<in> set ?problem"
    using relative_adp_selected_label_stream_in_problem[
      OF infinite steps subset, of n] unfolding problem .
  have candidate_set: "?Q =
      ((\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
        set component) \<union>
      ((\<lambda>i. ?problem ! i) `
        set (relative_adp_estimated_coreachable ?problem ?source)) \<union>
      ((\<lambda>i. ?problem ! i) `
        set (relative_adp_estimated_corridor ?problem ?source target_index))"
    by (rule relative_adp_estimated_lasso_candidate_set)
  fix m
  have edge: "(origin_path m, origin_path (Suc m)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    by (rule path_edge)
  show "(origin_path m, origin_path (Suc m)) \<in>
      relative_adp_selected_retained_origin_edge ?Q P A terms"
  proof (cases "relative_adp_selected_chain_labeled P A terms (origin_path m)")
    case False
    show ?thesis using edge False
      unfolding relative_adp_selected_retained_origin_edge_def by simp
  next
    case True
    note middle_labeled = True
    have mI: "m \<in> ?I"
      using middle_labeled
      unfolding relative_adp_selected_label_indices_def by simp
    from range_enumerate[OF infinite] mI obtain j where
      m: "m = enumerate ?I j" by blast
    have current_pair:
        "relative_adp_selected_chain_node_label P A terms (origin_path m) =
          ?labels j"
      unfolding m relative_adp_selected_label_stream_def by simp
    have in_Q: "?labels j \<in> ?Q"
    proof (cases "j \<le> n")
      case True
      have indices: "enumerate ?I j \<le> enumerate ?I n"
        by (rule monoD[OF strict_mono_mono[OF
            strict_mono_enumerate[OF infinite]] True])
      have origin_prefix: "(origin_path (enumerate ?I j),
          origin_path (enumerate ?I n)) \<in>
        (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
        by (rule ipath_interval_rtrancl[
            where p=origin_path
              and E="relative_adp_selected_chain_origin_edge P A terms"
              and i="enumerate ?I j" and j="enumerate ?I n",
            OF path_edge indices])
      have source_labeled:
          "relative_adp_selected_chain_labeled P A terms
            (origin_path (enumerate ?I j))"
        using enumerate_in_set[OF infinite, of j]
        unfolding relative_adp_selected_label_indices_def by simp
      have target_labeled:
          "relative_adp_selected_chain_labeled P A terms
            (origin_path (enumerate ?I n))"
        using enumerate_in_set[OF infinite, of n]
        unfolding relative_adp_selected_label_indices_def by simp
      have graph_path: "(?labels j,?source_pair) \<in>
          (relative_adp_dependency_graph (set ?problem))\<^sup>*"
        using relative_adp_selected_labeled_origin_path_dependency_graph_path[
          OF origin_prefix source_labeled target_labeled steps subset lhs_fun]
        unfolding problem relative_adp_selected_label_stream_def .
      have current_in: "?labels j \<in> set ?problem"
        using relative_adp_selected_label_stream_in_problem[
          OF infinite steps subset, of j] unfolding problem .
      have estimated: "(relative_adp_pair_index ?problem (?labels j),?source)
          \<in> (set (relative_adp_estimated_edges ?problem))\<^sup>*"
        by (rule relative_adp_semantic_path_in_estimated_path[
            OF current_in graph_path])
      have reverse_edges:
          "{(source,target). (target,source) \<in>
            set (relative_adp_estimated_edges ?problem)} =
           (set (relative_adp_estimated_edges ?problem))\<inverse>"
        by auto
      have reverse: "(?source,relative_adp_pair_index ?problem (?labels j)) \<in>
          {(source,target). (target,source) \<in>
            set (relative_adp_estimated_edges ?problem)}\<^sup>*"
        using estimated unfolding reverse_edges
        by (simp add: rtrancl_converse)
      have in_coreachable: "relative_adp_pair_index ?problem (?labels j) \<in>
          set (relative_adp_estimated_coreachable ?problem ?source)"
        unfolding relative_adp_estimated_coreachable_set using reverse by blast
      have nth: "?problem ! relative_adp_pair_index ?problem (?labels j) =
          ?labels j"
        by (rule relative_adp_pair_index_correct(2)[OF current_in])
      have "?labels j \<in> (\<lambda>i. ?problem ! i) `
          set (relative_adp_estimated_coreachable ?problem ?source)"
        using in_coreachable nth by force
      then show ?thesis unfolding candidate_set by blast
    next
      case False
      have "N \<le> j" using late False by simp
      then have "?labels j \<in>
          (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
            set component"
        by (rule eventual)
      then show ?thesis unfolding candidate_set by blast
    qed
    have node_in_Q:
        "relative_adp_selected_chain_node_label P A terms (origin_path m)
          \<in> ?Q"
      using current_pair in_Q by simp
    show ?thesis using edge middle_labeled node_in_Q
      unfolding relative_adp_selected_retained_origin_edge_def by simp
  qed
qed

theorem relative_adp_selected_estimated_lasso_child_not_SN:
  assumes P_def: "P = set P_list"
    and B_def: "B = set B_list"
    and A_def: "A = P \<union> B"
    and offshoots: "INFM n. event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) origin_path n"
    and no_main: "\<not> (INFM n.
      relative_adp_selected_chain_main_event P A terms (origin_path n))"
    and path_root: "origin_path 0 = (0,root_pos)"
    and root_marked: "root_pos \<in> sharp_positions (terms 0)"
    and path_edge: "\<And>n. (origin_path n, origin_path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains Q where
    "Q \<in> set (relative_adp_estimated_lasso_candidates P_list B_list)"
    "\<not> adp_problem_SN
      (P \<inter> set Q,
        (set Q \<union> erase_annotations_adp ` (A - set Q)) -
          (P \<inter> set Q))"
proof -
  let ?I = "relative_adp_selected_label_indices P A terms origin_path"
  let ?labels = "relative_adp_selected_label_stream P A terms origin_path"
  let ?candidates =
    "set (relative_adp_estimated_lasso_candidates P_list B_list)"
  let ?family = "{Q. \<exists>Q_list \<in> ?candidates.
    Q = set Q_list \<and> (\<forall>m. (origin_path m, origin_path (Suc m)) \<in>
      relative_adp_selected_retained_origin_edge Q P A terms)}"
  have subset: "P \<subseteq> A" unfolding A_def by blast
  have infinite: "infinite ?I"
    by (rule relative_adp_selected_offshoots_give_labeled_stream[
        OF offshoots path_edge steps subset])
  have component_witness: "\<exists>component N.
      component \<in> set (relative_adp_estimated_sccs
        (relative_adp_lasso_problem_list P_list B_list)) \<and>
      (\<forall>n. N \<le> n \<longrightarrow> ?labels n \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
          set component)"
  proof (rule relative_adp_selected_base_stream_eventual_estimated_scc[
      OF P_def B_def A_def infinite no_main path_edge steps lhs_fun])
    fix component N
    assume component: "component \<in> set (relative_adp_estimated_sccs
        (relative_adp_lasso_problem_list P_list B_list))"
      and eventual: "\<And>n. N \<le> n \<Longrightarrow> ?labels n \<in>
        (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
          set component"
    show "\<exists>component N.
        component \<in> set (relative_adp_estimated_sccs
          (relative_adp_lasso_problem_list P_list B_list)) \<and>
        (\<forall>n. N \<le> n \<longrightarrow> ?labels n \<in>
          (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
            set component)"
      by (rule exI[of _ component], rule exI[of _ N])
         (use component eventual in blast)
  qed
  from component_witness obtain component N where component:
      "component \<in> set (relative_adp_estimated_sccs
        (relative_adp_lasso_problem_list P_list B_list))"
    and eventual: "\<And>n. N \<le> n \<Longrightarrow> ?labels n \<in>
      (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
        set component"
    by blast
  have branching_stream: "INFM n. ?labels n \<in> A - P \<and>
      relative_adp_branching_pair (?labels n) \<and>
      event_offshoot (relative_adp_selected_chain_origin_edge P A terms)
        (relative_adp_selected_chain_main_event P A terms) origin_path
        (enumerate ?I n)"
    by (rule relative_adp_selected_offshoots_give_branching_base_stream[
        OF offshoots no_main path_edge steps subset lhs_fun])
  have finite_family: "finite ?family"
  proof -
    have "?family \<subseteq> set ` ?candidates" by blast
    then show ?thesis by (rule finite_subset) simp
  qed
  have path_retained: "\<And>Q m. Q \<in> ?family \<Longrightarrow>
      (origin_path m, origin_path (Suc m)) \<in>
        relative_adp_selected_retained_origin_edge Q P A terms"
    by blast
  have covered: "INFM n. \<exists>Q \<in> ?family.
      relative_adp_selected_retained_main_reachable
        Q P A terms (origin_path n)"
    unfolding INFM_nat
  proof
    fix M
    from branching_stream[unfolded INFM_nat]
    obtain n where large: "max M N < n"
      and base: "?labels n \<in> A - P"
      and branching: "relative_adp_branching_pair (?labels n)"
      and offshoot: "event_offshoot
        (relative_adp_selected_chain_origin_edge P A terms)
        (relative_adp_selected_chain_main_event P A terms) origin_path
        (enumerate ?I n)" by blast
    let ?source_node = "origin_path (enumerate ?I n)"
    have source_labeled:
        "relative_adp_selected_chain_labeled P A terms ?source_node"
      by (rule relative_adp_selected_event_offshoot_is_labeled[
          where P=P and A=A and terms=terms and path=origin_path
            and n="enumerate ?I n",
          OF offshoot path_edge steps subset])
    have source_pair: "relative_adp_selected_chain_node_label
        P A terms ?source_node = ?labels n"
      unfolding relative_adp_selected_label_stream_def by simp
    have label_B: "?labels n \<in> B"
      using base unfolding A_def by blast
    have source_B: "relative_adp_selected_chain_node_label
        P A terms ?source_node \<in> B"
      using source_pair label_B by simp
    have source_component: "relative_adp_selected_chain_node_label
        P A terms ?source_node \<in>
      (\<lambda>i. relative_adp_lasso_problem_list P_list B_list ! i) `
        set component"
      using eventual[of n] large unfolding source_pair by simp
    from offshoot obtain first target_node where first:
        "(?source_node,first) \<in>
          relative_adp_selected_chain_origin_edge P A terms"
      and tail: "(first,target_node) \<in>
        (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
      and main: "relative_adp_selected_chain_main_event
        P A terms target_node"
      unfolding event_offshoot_def reachable_events_def by blast
    have origin: "(?source_node,target_node) \<in>
        (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
      by (rule rtrancl_trans[OF r_into_rtrancl[OF first] tail])
    have candidate_witness: "\<exists>Q_list.
        Q_list \<in> ?candidates \<and>
        Q_list = relative_adp_estimated_lasso_candidate P_list B_list component
          (relative_adp_pair_index
            (relative_adp_problem_list P_list B_list) (?labels n))
          (relative_adp_pair_index
            (relative_adp_problem_list P_list B_list)
            (relative_adp_selected_chain_node_label
              P A terms target_node)) \<and>
        relative_adp_selected_retained_main_reachable
          (set Q_list) P A terms ?source_node"
    proof (rule relative_adp_selected_offshoot_covered_by_lasso_candidate[
        OF P_def B_def A_def component source_labeled source_B
          source_component _ origin main steps lhs_fun])
      show "relative_adp_branching_pair
          (relative_adp_selected_chain_node_label P A terms ?source_node)"
        using branching unfolding source_pair .
    next
      fix Q_list
      assume equality: "Q_list = relative_adp_estimated_lasso_candidate
          P_list B_list component
          (relative_adp_pair_index (relative_adp_problem_list P_list B_list)
            (relative_adp_selected_chain_node_label P A terms ?source_node))
          (relative_adp_pair_index (relative_adp_problem_list P_list B_list)
            (relative_adp_selected_chain_node_label P A terms target_node))"
        and candidate: "Q_list \<in> ?candidates"
        and reachable: "relative_adp_selected_retained_main_reachable
          (set Q_list) P A terms ?source_node"
      show "\<exists>Q_list. Q_list \<in> ?candidates \<and>
          Q_list = relative_adp_estimated_lasso_candidate P_list B_list component
            (relative_adp_pair_index
              (relative_adp_problem_list P_list B_list) (?labels n))
            (relative_adp_pair_index
              (relative_adp_problem_list P_list B_list)
              (relative_adp_selected_chain_node_label
                P A terms target_node)) \<and>
          relative_adp_selected_retained_main_reachable
            (set Q_list) P A terms ?source_node"
        by (rule exI[of _ Q_list])
           (use equality candidate reachable source_pair in simp)
    qed
    from candidate_witness obtain Q_list where candidate:
        "Q_list \<in> ?candidates"
      and equality: "Q_list = relative_adp_estimated_lasso_candidate
        P_list B_list component
        (relative_adp_pair_index
          (relative_adp_problem_list P_list B_list) (?labels n))
        (relative_adp_pair_index
          (relative_adp_problem_list P_list B_list)
          (relative_adp_selected_chain_node_label P A terms target_node))"
      and reachable: "relative_adp_selected_retained_main_reachable
        (set Q_list) P A terms ?source_node" by blast
    have late_n: "N \<le> n" using large by simp
    have retained_all: "\<forall>m. (origin_path m, origin_path (Suc m)) \<in>
        relative_adp_selected_retained_origin_edge (set Q_list) P A terms"
      unfolding equality
      by (intro allI, rule relative_adp_late_lasso_candidate_retains_base_path[
          OF P_def B_def A_def infinite path_edge steps lhs_fun eventual late_n])
    have family: "set Q_list \<in> ?family"
      using candidate retained_all by blast
    show "\<exists>n>M. \<exists>Q \<in> ?family.
        relative_adp_selected_retained_main_reachable
          Q P A terms (origin_path n)"
      by (rule exI[of _ "enumerate ?I n"], rule conjI)
         (use large enumerate_nat_lower_bound[OF infinite, of n]
            family reachable in auto)
  qed
  have non_SN_witness: "\<exists>Q \<in> ?family.
      \<not> adp_problem_SN
        (P \<inter> Q, (Q \<union> erase_annotations_adp ` (A - Q)) - (P \<inter> Q))"
  proof (rule relative_adp_selected_finite_lasso_family_has_non_SN_child[
      where family="?family" and source="terms 0" and path=origin_path
        and root_pos=root_pos,
      OF steps subset finite_family _ path_root root_marked path_retained covered])
    show "erase_adp_term (terms 0) = erase_adp_term (terms 0)" by simp
  next
    fix Q
    assume Q: "Q \<in> ?family"
      and non_SN: "\<not> adp_problem_SN
        (P \<inter> Q, (Q \<union> erase_annotations_adp ` (A - Q)) - (P \<inter> Q))"
    show "\<exists>Q \<in> ?family. \<not> adp_problem_SN
        (P \<inter> Q, (Q \<union> erase_annotations_adp ` (A - Q)) - (P \<inter> Q))"
      using Q non_SN by blast
  qed
  from non_SN_witness obtain Q where Q: "Q \<in> ?family"
    and non_SN: "\<not> adp_problem_SN
      (P \<inter> Q, (Q \<union> erase_annotations_adp ` (A - Q)) - (P \<inter> Q))"
    by blast
  from Q obtain Q_list where candidate: "Q_list \<in> ?candidates"
    and equality: "Q = set Q_list" by blast
  show thesis using candidate non_SN unfolding equality by (rule that)
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

theorem relative_adp_estimated_graph_has_non_SN_child:
  assumes not_SN: "\<not> adp_problem_SN (set P_list,set B_list)"
    and lhs_fun: "\<And>pair. pair \<in> set P_list \<union> set B_list \<Longrightarrow>
      is_Fun (fst pair)"
  obtains Q where
    "Q \<in> set (relative_adp_estimated_graph_candidates P_list B_list)"
    "\<not> adp_problem_SN
      (set P_list \<inter> set Q,
        (set Q \<union> erase_annotations_adp `
          ((set P_list \<union> set B_list) - set Q)) -
          (set P_list \<inter> set Q))"
proof -
  let ?P = "set P_list"
  let ?B = "set B_list"
  let ?A = "?P \<union> ?B"
  let ?problem = "relative_adp_problem_list P_list B_list"
  have problem: "set ?problem = ?A"
    unfolding relative_adp_problem_list_set by simp
  have subset: "?P \<subseteq> ?A" by blast
  from not_SN obtain terms where deriv:
      "ideriv (adp_step_case_rel ?P True) (adp_step ?A) terms"
    unfolding adp_problem_SN_def SN_rel_ideriv by auto
  have steps: "\<And>n. (terms n, terms (Suc n)) \<in> adp_step ?A"
    by (rule relative_adp_ideriv_chain_steps[OF deriv subset])
  have path_witness: "\<exists>root origin_path.
      root \<in> sharp_positions (terms 0) \<and>
      origin_path 0 = (0,root) \<and>
      (\<forall>n. (origin_path n, origin_path (Suc n)) \<in>
        relative_adp_selected_chain_origin_edge ?P ?A terms) \<and>
      ((INFM n. relative_adp_selected_chain_main_event
          ?P ?A terms (origin_path n)) \<or>
       (INFM n. event_offshoot
          (relative_adp_selected_chain_origin_edge ?P ?A terms)
          (relative_adp_selected_chain_main_event ?P ?A terms)
          origin_path n))"
  proof -
    let ?E = "relative_adp_selected_chain_origin_edge ?P ?A terms"
    let ?event = "relative_adp_selected_chain_main_event ?P ?A terms"
    from relative_adp_ideriv_has_selected_heavy_root[OF deriv subset]
    obtain root where root: "root \<in> sharp_positions (terms 0)"
      and heavy: "heavy_node ?E ?event (0,root)" .
    let ?origin_path = "heavy_path ?E ?event (0,root)"
    from finite_branching_event_dichotomy[OF heavy]
    have dichotomy: "(\<forall>n. (?origin_path n, ?origin_path (Suc n)) \<in> ?E) \<and>
        ((INFM n. ?event (?origin_path n)) \<or>
         (INFM n. event_offshoot ?E ?event ?origin_path n))"
      by (simp add: finite_relative_adp_selected_chain_origin_successors)
    show ?thesis
      by (rule exI[of _ root], rule exI[of _ ?origin_path])
         (use root dichotomy in simp)
  qed
  from path_witness obtain root origin_path where root:
      "root \<in> sharp_positions (terms 0)"
    and path_root: "origin_path 0 = (0,root)"
    and path_edge: "\<And>n. (origin_path n, origin_path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge ?P ?A terms"
    and dichotomy: "(INFM n. relative_adp_selected_chain_main_event
        ?P ?A terms (origin_path n)) \<or>
      (INFM n. event_offshoot
        (relative_adp_selected_chain_origin_edge ?P ?A terms)
        (relative_adp_selected_chain_main_event ?P ?A terms)
        origin_path n)" by blast
  show thesis
  proof (cases "INFM n. relative_adp_selected_chain_main_event
      ?P ?A terms (origin_path n)")
    case True
    have main_witness: "\<exists>component.
        component \<in> set (relative_adp_estimated_sccs ?problem) \<and>
        ((\<lambda>i. ?problem ! i) ` set component) \<inter> ?P \<noteq> {} \<and>
        (\<not> adp_problem_SN
          (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component),
           (((\<lambda>i. ?problem ! i) ` set component) \<union>
              erase_annotations_adp `
                (?A - ((\<lambda>i. ?problem ! i) ` set component))) -
            (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component))))"
    proof (rule relative_adp_selected_estimated_main_scc_child_not_SN[
        OF problem True path_edge steps subset lhs_fun])
      fix component
      assume component: "component \<in>
          set (relative_adp_estimated_sccs ?problem)"
        and intersects: "((\<lambda>i. ?problem ! i) ` set component) \<inter> ?P
          \<noteq> {}"
        and child: "\<not> adp_problem_SN
          (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component),
           (((\<lambda>i. ?problem ! i) ` set component) \<union>
              erase_annotations_adp `
                (?A - ((\<lambda>i. ?problem ! i) ` set component))) -
            (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component)))"
      show "\<exists>component.
          component \<in> set (relative_adp_estimated_sccs ?problem) \<and>
          ((\<lambda>i. ?problem ! i) ` set component) \<inter> ?P \<noteq> {} \<and>
          (\<not> adp_problem_SN
            (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component),
             (((\<lambda>i. ?problem ! i) ` set component) \<union>
                erase_annotations_adp `
                  (?A - ((\<lambda>i. ?problem ! i) ` set component))) -
              (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component))))"
        by (rule exI[of _ component])
           (use component intersects child in blast)
    qed
    from main_witness obtain component where component:
        "component \<in> set (relative_adp_estimated_sccs ?problem)"
      and intersects: "((\<lambda>i. ?problem ! i) ` set component) \<inter> ?P
        \<noteq> {}"
      and child: "\<not> adp_problem_SN
        (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component),
         (((\<lambda>i. ?problem ! i) ` set component) \<union>
            erase_annotations_adp `
              (?A - ((\<lambda>i. ?problem ! i) ` set component))) -
          (?P \<inter> ((\<lambda>i. ?problem ! i) ` set component)))"
      by blast
    let ?Q = "map ((!) ?problem) component"
    have Q_set: "set ?Q = (\<lambda>i. ?problem ! i) ` set component" by simp
    have overlap: "list_ex (\<lambda>pair. pair \<in> set P_list) ?Q"
      using intersects Q_set unfolding list_ex_iff by blast
    have main_candidate: "?Q \<in>
        set (relative_adp_estimated_main_scc_candidates P_list B_list)"
      using component overlap
      unfolding relative_adp_estimated_main_scc_candidates_def
      by (auto simp: Let_def)
    have candidate: "?Q \<in>
        set (relative_adp_estimated_graph_candidates P_list B_list)"
      using main_candidate
      unfolding relative_adp_estimated_graph_candidates_def by simp
    show thesis by (rule that[OF candidate]) (use child Q_set in simp)
  next
    case False
    have offshoots: "INFM n. event_offshoot
        (relative_adp_selected_chain_origin_edge ?P ?A terms)
        (relative_adp_selected_chain_main_event ?P ?A terms)
        origin_path n"
      using dichotomy False by blast
    have lasso_witness: "\<exists>Q.
        Q \<in> set (relative_adp_estimated_lasso_candidates P_list B_list) \<and>
        (\<not> adp_problem_SN
          (?P \<inter> set Q,
            (set Q \<union> erase_annotations_adp ` (?A - set Q)) -
              (?P \<inter> set Q)))"
    proof (rule relative_adp_selected_estimated_lasso_child_not_SN[
        where root_pos=root and origin_path=origin_path,
        OF HOL.refl HOL.refl HOL.refl offshoots False path_root root
          path_edge steps lhs_fun])
    next
      fix Q
      assume candidate: "Q \<in>
          set (relative_adp_estimated_lasso_candidates P_list B_list)"
        and child: "\<not> adp_problem_SN
          (?P \<inter> set Q,
            (set Q \<union> erase_annotations_adp ` (?A - set Q)) -
              (?P \<inter> set Q))"
      show "\<exists>Q.
          Q \<in> set (relative_adp_estimated_lasso_candidates P_list B_list) \<and>
          (\<not> adp_problem_SN
            (?P \<inter> set Q,
              (set Q \<union> erase_annotations_adp ` (?A - set Q)) -
                (?P \<inter> set Q)))"
        using candidate child by blast
    qed
    from lasso_witness obtain Q where lasso_candidate:
        "Q \<in> set (relative_adp_estimated_lasso_candidates P_list B_list)"
      and child: "\<not> adp_problem_SN
        (?P \<inter> set Q,
          (set Q \<union> erase_annotations_adp ` (?A - set Q)) -
            (?P \<inter> set Q))" by blast
    have candidate: "Q \<in>
        set (relative_adp_estimated_graph_candidates P_list B_list)"
      using lasso_candidate
      unfolding relative_adp_estimated_graph_candidates_def by simp
    show thesis by (rule that[OF candidate child])
  qed
qed

theorem relative_adp_estimated_graph_processor:
  assumes lhs_fun: "\<And>pair. pair \<in> set P \<union> set B \<Longrightarrow>
      is_Fun (fst pair)"
    and children: "\<And>Q.
      Q \<in> set (relative_adp_estimated_graph_candidates P B) \<Longrightarrow>
      adp_problem_SN
        (set P \<inter> set Q,
          (set Q \<union> erase_annotations_adp `
            ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))"
  shows "adp_problem_SN (set P,set B)"
proof (rule ccontr)
  assume not_SN: "\<not> adp_problem_SN (set P,set B)"
  from relative_adp_estimated_graph_has_non_SN_child[OF not_SN lhs_fun]
  obtain Q where candidate:
      "Q \<in> set (relative_adp_estimated_graph_candidates P B)"
    and child_not_SN: "\<not> adp_problem_SN
      (set P \<inter> set Q,
        (set Q \<union> erase_annotations_adp `
          ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))" .
  have child_SN: "adp_problem_SN
      (set P \<inter> set Q,
        (set Q \<union> erase_annotations_adp `
          ((set P \<union> set B) - set Q)) - (set P \<inter> set Q))"
    by (rule children[OF candidate])
  show False using child_SN child_not_SN by contradiction
qed

end

end
