theory Relative_ADP_Dependency_Graph_Impl
  imports
    Relative_ADP_Dependency_Graph
    Auxx.Gabow_SCC_RBT
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
