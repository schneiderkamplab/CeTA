theory Relative_ADP_Derelatification
  imports Relative_ADP_Dependency_Graph_Dev.Relative_ADP_Dependency_Graph_Impl
begin

text \<open>
  The first derelatifying processor (DRP1) of Kassing, Vartanyan, and
  Giesl converts an ADP problem whose base is annotation-free into an
  ordinary, non-minimal DP problem.  We retain the ADP-symbol carrier here:
  ordinary DP roots are @{const Sharp} symbols and rewrite rules contain only
  @{const Plain} symbols.  This makes the semantic bridge independent of CPF's
  concrete symbol representation.
\<close>

definition relative_adp_dp_pairs ::
  "('f, 'v) adp set \<Rightarrow> ('f adp_symbol, 'v) trs" where
  "relative_adp_dp_pairs P =
    {(mark_adp_root (fst pair), mark_adp_root u) | pair u.
      pair \<in> P \<and> u \<in> annotated_rhs_subterms pair}"

definition relative_adp_flat_rules ::
  "('f, 'v) adp set \<Rightarrow> ('f adp_symbol, 'v) trs" where
  "relative_adp_flat_rules A = erase_annotations_adp ` A"

definition relative_adp_base_flat :: "('f, 'v) adp set \<Rightarrow> bool" where
  "relative_adp_base_flat B \<longleftrightarrow>
    (\<forall>pair \<in> B. sharp_positions (snd pair) = {})"

definition relative_adp_dp_pairs_list ::
  "('f, 'v) adp list \<Rightarrow> ('f adp_symbol, 'v) rules" where
  "relative_adp_dp_pairs_list P = concat (map (\<lambda>pair.
    map (\<lambda>u. (mark_adp_root (fst pair), mark_adp_root u))
      (annotated_rhs_subterms_list pair)) P)"

definition relative_adp_flat_rules_list ::
  "('f, 'v) adp list \<Rightarrow> ('f adp_symbol, 'v) rules" where
  "relative_adp_flat_rules_list A = map erase_annotations_adp A"

definition relative_adp_base_flat_list :: "('f, 'v) adp list \<Rightarrow> bool" where
  "relative_adp_base_flat_list B = list_all
    (\<lambda>pair. annotated_rhs_subterms_list pair = []) B"

lemma relative_adp_dp_pairs_list_sound:
  "set (relative_adp_dp_pairs_list P) = relative_adp_dp_pairs (set P)"
proof
  show "set (relative_adp_dp_pairs_list P) \<subseteq>
      relative_adp_dp_pairs (set P)"
  proof
    fix dp
    assume "dp \<in> set (relative_adp_dp_pairs_list P)"
    then obtain pair u where pair: "pair \<in> set P"
      and u: "u \<in> set (annotated_rhs_subterms_list pair)"
      and dp: "dp = (mark_adp_root (fst pair), mark_adp_root u)"
      unfolding relative_adp_dp_pairs_list_def by auto
    have "u \<in> annotated_rhs_subterms pair"
      using u annotated_rhs_subterms_list_sound[of pair] by simp
    with pair dp show "dp \<in> relative_adp_dp_pairs (set P)"
      unfolding relative_adp_dp_pairs_def by blast
  qed
  show "relative_adp_dp_pairs (set P) \<subseteq>
      set (relative_adp_dp_pairs_list P)"
  proof
    fix dp
    assume "dp \<in> relative_adp_dp_pairs (set P)"
    then obtain pair u where pair: "pair \<in> set P"
      and u: "u \<in> annotated_rhs_subterms pair"
      and dp: "dp = (mark_adp_root (fst pair), mark_adp_root u)"
      unfolding relative_adp_dp_pairs_def by blast
    have "u \<in> set (annotated_rhs_subterms_list pair)"
      using u annotated_rhs_subterms_list_sound[of pair] by simp
    with pair dp show "dp \<in> set (relative_adp_dp_pairs_list P)"
      unfolding relative_adp_dp_pairs_list_def by auto
  qed
qed

lemma relative_adp_flat_rules_list_sound:
  "set (relative_adp_flat_rules_list A) = relative_adp_flat_rules (set A)"
  unfolding relative_adp_flat_rules_list_def relative_adp_flat_rules_def by simp

lemma annotated_rhs_subterms_empty_iff:
  "annotated_rhs_subterms pair = {} \<longleftrightarrow>
    sharp_positions (snd pair) = {}"
proof
  assume empty: "annotated_rhs_subterms pair = {}"
  show "sharp_positions (snd pair) = {}"
  proof (rule ccontr)
    assume "sharp_positions (snd pair) \<noteq> {}"
    then obtain q where q: "q \<in> sharp_positions (snd pair)" by blast
    then have "snd pair |_ q \<in> annotated_rhs_subterms pair"
      unfolding annotated_rhs_subterms_def by blast
    with empty show False by simp
  qed
next
  assume "sharp_positions (snd pair) = {}"
  then show "annotated_rhs_subterms pair = {}"
    unfolding annotated_rhs_subterms_def by simp
qed

lemma relative_adp_base_flat_list_sound:
  "relative_adp_base_flat_list B \<longleftrightarrow>
    relative_adp_base_flat (set B)"
proof
  assume flat: "relative_adp_base_flat_list B"
  show "relative_adp_base_flat (set B)"
    unfolding relative_adp_base_flat_def
  proof
    fix pair
    assume pair: "pair \<in> set B"
    from flat pair have list_empty:
        "annotated_rhs_subterms_list pair = []"
      unfolding relative_adp_base_flat_list_def list_all_iff by blast
    have "annotated_rhs_subterms pair = {}"
      using annotated_rhs_subterms_list_sound[of pair] list_empty by simp
    then show "sharp_positions (snd pair) = {}"
      using annotated_rhs_subterms_empty_iff[of pair] by simp
  qed
next
  assume flat: "relative_adp_base_flat (set B)"
  show "relative_adp_base_flat_list B"
    unfolding relative_adp_base_flat_list_def list_all_iff
  proof
    fix pair
    assume pair: "pair \<in> set B"
    from flat pair have "sharp_positions (snd pair) = {}"
      unfolding relative_adp_base_flat_def by blast
    then have "annotated_rhs_subterms pair = {}"
      using annotated_rhs_subterms_empty_iff[of pair] by simp
    then have "set (annotated_rhs_subterms_list pair) = {}"
      using annotated_rhs_subterms_list_sound[of pair] by simp
    then show "annotated_rhs_subterms_list pair = []" by simp
  qed
qed

lemma relative_adp_flat_rules_union:
  "relative_adp_flat_rules (P \<union> B) =
    relative_adp_flat_rules P \<union> relative_adp_flat_rules B"
  unfolding relative_adp_flat_rules_def by blast

lemma relative_adp_selected_labeled_edge_pair_instance:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and label:
      "relative_adp_selected_chain_label P A terms (i,q) pair"
    and lhs_fun: "is_Fun (fst pair)"
  obtains alpha sigma where
    "alpha \<in> sharp_positions (snd pair)"
    "mark_adp_root (terms i |_ q) =
      mark_adp_root (fst pair) \<cdot> sigma"
    "mark_adp_root (terms (Suc i) |_ q') =
      mark_adp_root (snd pair |_ alpha) \<cdot> sigma"
    "\<forall>x. sigma x = plain_adp_term (erase_adp_term (sigma x))"
proof -
  from relative_adp_selected_labeled_edge_enters_rhs[
      OF edge label lhs_fun]
  obtain alpha where alpha: "alpha \<in> sharp_positions (snd pair)"
    and q': "q' = q @ alpha" .
  let ?application = "relative_adp_selected_application P A terms i"
  from edge have source_sharp: "q \<in> sharp_positions (terms i)"
    and origin: "relative_adp_canonical_origin_edge A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application)) q q'"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  from label have pair: "fst (snd ?application) = pair"
    and redex: "snd (snd ?application) = q"
    unfolding relative_adp_selected_chain_label_def
    by (auto simp: Let_def)
  from origin obtain l r phi sigma annotations where
      pair_lr: "fst (snd ?application) = (l,r)"
    and lhs: "erase_adp_term
        (terms i |_ snd (snd ?application)) =
      erase_adp_term l \<cdot> sigma"
    and target: "terms (Suc i) = replace_at (terms i)
      (snd (snd ?application))
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have pair_eq: "pair = (l,r)" using pair pair_lr by simp
  have source_instance: "erase_adp_term (terms i |_ q) =
      erase_adp_term (fst pair) \<cdot> sigma"
    using lhs redex pair_eq by simp
  have marked_source: "mark_adp_root (terms i |_ q) =
      mark_adp_root (fst pair) \<cdot> (plain_adp_term \<circ> sigma)"
    by (rule mark_adp_root_erased_instance[OF lhs_fun source_instance])
  have q_poss: "q \<in> poss (terms i)"
    using source_sharp unfolding sharp_positions_def by auto
  have q_after: "q \<in> poss (terms (Suc i))"
    unfolding target redex
    by (rule replace_at_below_poss[OF q_poss]) simp
  have local_target: "terms (Suc i) |_ q =
      annotate_term annotations (erase_adp_term r \<cdot> sigma)"
    unfolding target redex by (rule replace_at_subt_at[OF q_poss])
  have alpha_poss: "alpha \<in> poss r"
    using alpha pair_eq unfolding sharp_positions_def by auto
  have alpha_erased_poss: "alpha \<in> poss (erase_adp_term r)"
    using alpha_poss by simp
  have alpha_subst_poss: "alpha \<in> poss (erase_adp_term r \<cdot> sigma)"
    using alpha_erased_poss by simp
  have alpha_annotated_poss: "alpha \<in> poss
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    using alpha_subst_poss poss_annotate_term_at[
        of annotations "[]" "erase_adp_term r \<cdot> sigma"]
    unfolding annotate_term_def by simp
  have target_instance:
      "erase_adp_term (terms (Suc i) |_ q') =
        erase_adp_term (snd pair |_ alpha) \<cdot> sigma"
    using subt_at_append[OF q_after, of alpha] local_target
      subt_at_subst[OF alpha_erased_poss, of sigma]
      erase_adp_term_subt_at[OF alpha_poss]
      erase_adp_term_subt_at[OF alpha_annotated_poss]
    unfolding q' pair_eq by simp
  have rhs_fun: "is_Fun (snd pair |_ alpha)"
    using alpha unfolding sharp_positions_def
    by (auto split: option.splits)
  have marked_target: "mark_adp_root (terms (Suc i) |_ q') =
      mark_adp_root (snd pair |_ alpha) \<cdot>
        (plain_adp_term \<circ> sigma)"
    by (rule mark_adp_root_erased_instance[OF rhs_fun target_instance])
  have plain: "\<forall>x. (plain_adp_term \<circ> sigma) x =
      plain_adp_term (erase_adp_term ((plain_adp_term \<circ> sigma) x))"
    by (simp add: comp_def)
  show thesis
    by (rule that[OF alpha marked_source marked_target plain])
qed

lemma relative_adp_flat_base_path_source_unlabeled:
  assumes flat: "relative_adp_base_flat B"
    and A: "A = P \<union> B"
    and edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
    and nonmain:
      "\<not> relative_adp_selected_chain_main_event P A terms (i,q)"
  shows "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
proof
  assume labeled:
      "relative_adp_selected_chain_labeled P A terms (i,q)"
  from labeled obtain pair where label:
      "relative_adp_selected_chain_label P A terms (i,q) pair"
    unfolding relative_adp_selected_chain_labeled_def by blast
  have subset: "P \<subseteq> A" unfolding A by blast
  have pair_A: "pair \<in> A"
    by (rule relative_adp_selected_label_in_problem[OF step subset label])
  have pair_not_P: "pair \<notin> P"
  proof
    assume "pair \<in> P"
    then have "relative_adp_selected_chain_main_event P A terms (i,q)"
      by (rule relative_adp_selected_label_in_main_is_main_event[OF label])
    with nonmain show False by contradiction
  qed
  have pair_B: "pair \<in> B" using pair_A pair_not_P unfolding A by blast
  from relative_adp_selected_labeled_edge_enters_rhs[
      OF edge label lhs_fun[OF pair_A]]
  obtain alpha where "alpha \<in> sharp_positions (snd pair)" by blast
  moreover from flat pair_B have "sharp_positions (snd pair) = {}"
    unfolding relative_adp_base_flat_def by blast
  ultimately show False by simp
qed

definition relative_adp_drp1_main_indices ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat set" where
  "relative_adp_drp1_main_indices P A terms nodes =
    {n. relative_adp_selected_chain_main_event P A terms (nodes n)}"

definition relative_adp_drp1_node ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow> nat \<times> pos" where
  "relative_adp_drp1_node P A terms nodes n = nodes
    (enumerate (relative_adp_drp1_main_indices P A terms nodes) n)"

definition relative_adp_drp1_pair ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow> ('f, 'v) adp" where
  "relative_adp_drp1_pair P A terms nodes n =
    relative_adp_selected_chain_node_label P A terms
      (relative_adp_drp1_node P A terms nodes n)"

definition relative_adp_drp1_instance_witness ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow>
    pos \<times> ('v \<Rightarrow> ('f adp_symbol, 'v) term)" where
  "relative_adp_drp1_instance_witness P A terms nodes n = (SOME w.
    let node = relative_adp_drp1_node P A terms nodes n;
        pair = relative_adp_drp1_pair P A terms nodes n;
        next = nodes (Suc (enumerate
          (relative_adp_drp1_main_indices P A terms nodes) n))
    in fst w \<in> sharp_positions (snd pair) \<and>
      mark_adp_root (terms (fst node) |_ snd node) =
        mark_adp_root (fst pair) \<cdot> snd w \<and>
      mark_adp_root (terms (fst next) |_ snd next) =
        mark_adp_root (snd pair |_ fst w) \<cdot> snd w \<and>
      (\<forall>x. snd w x = plain_adp_term (erase_adp_term (snd w x))))"

lemma relative_adp_drp1_instance_witness:
  fixes n :: nat
  assumes infinite: "infinite
      (relative_adp_drp1_main_indices P A terms nodes)"
    and path_edge: "\<And>n. (nodes n, nodes (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  defines "node \<equiv> relative_adp_drp1_node P A terms nodes n"
    and "pair \<equiv> relative_adp_drp1_pair P A terms nodes n"
    and "witness \<equiv> relative_adp_drp1_instance_witness P A terms nodes n"
  shows "pair \<in> P"
    "fst witness \<in> sharp_positions (snd pair)"
    "mark_adp_root (terms (fst node) |_ snd node) =
      mark_adp_root (fst pair) \<cdot> snd witness"
    "mark_adp_root
      (terms (fst (nodes (Suc (enumerate
        (relative_adp_drp1_main_indices P A terms nodes) n)))) |_
        snd (nodes (Suc (enumerate
          (relative_adp_drp1_main_indices P A terms nodes) n)))) =
      mark_adp_root (snd pair |_ fst witness) \<cdot> snd witness"
    "\<forall>x. snd witness x =
      plain_adp_term (erase_adp_term (snd witness x))"
proof -
  let ?I = "relative_adp_drp1_main_indices P A terms nodes"
  let ?k = "enumerate ?I n"
  have kI: "?k \<in> ?I" by (rule enumerate_in_set[OF infinite])
  have main: "relative_adp_selected_chain_main_event P A terms (nodes ?k)"
    using kI unfolding relative_adp_drp1_main_indices_def by simp
  have labeled: "relative_adp_selected_chain_labeled P A terms (nodes ?k)"
    using main unfolding relative_adp_selected_chain_main_event_iff_node_label
    by blast
  have label: "relative_adp_selected_chain_label P A terms (nodes ?k) pair"
    using relative_adp_selected_chain_labeled_has_node_label[OF labeled]
    unfolding pair_def relative_adp_drp1_pair_def node_def
      relative_adp_drp1_node_def by simp
  have pair_P: "pair \<in> P"
    using main unfolding pair_def relative_adp_drp1_pair_def node_def
      relative_adp_drp1_node_def
      relative_adp_selected_chain_main_event_iff_node_label by simp
  then have pair_A: "pair \<in> A" using subset by blast
  obtain i q where current: "nodes ?k = (i,q)" by (cases "nodes ?k") auto
  obtain j q' where following: "nodes (Suc ?k) = (j,q')"
    by (cases "nodes (Suc ?k)") auto
  have edge_raw: "((i,q),(j,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using path_edge[of ?k] unfolding current following .
  have j: "j = Suc i"
    by (rule relative_adp_selected_chain_origin_edge_time[OF edge_raw])
  have edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using edge_raw unfolding j .
  have label': "relative_adp_selected_chain_label P A terms (i,q) pair"
    using label unfolding current .
  from relative_adp_selected_labeled_edge_pair_instance[
      OF edge label' lhs_fun[OF pair_A]]
  obtain alpha sigma where alpha: "alpha \<in> sharp_positions (snd pair)"
    and source: "mark_adp_root (terms i |_ q) =
      mark_adp_root (fst pair) \<cdot> sigma"
    and target: "mark_adp_root (terms (Suc i) |_ q') =
      mark_adp_root (snd pair |_ alpha) \<cdot> sigma"
    and sigma_plain: "\<forall>x. sigma x =
      plain_adp_term (erase_adp_term (sigma x))" .
  let ?property = "\<lambda>w. let
      node = relative_adp_drp1_node P A terms nodes n;
      pair = relative_adp_drp1_pair P A terms nodes n;
      next = nodes (Suc (enumerate ?I n))
    in fst w \<in> sharp_positions (snd pair) \<and>
      mark_adp_root (terms (fst node) |_ snd node) =
        mark_adp_root (fst pair) \<cdot> snd w \<and>
      mark_adp_root (terms (fst next) |_ snd next) =
        mark_adp_root (snd pair |_ fst w) \<cdot> snd w \<and>
      (\<forall>x. snd w x = plain_adp_term (erase_adp_term (snd w x)))"
  have node_eq: "relative_adp_drp1_node P A terms nodes n = (i,q)"
    unfolding relative_adp_drp1_node_def current by simp
  have pair_eq': "relative_adp_drp1_pair P A terms nodes n = pair"
    unfolding pair_def by simp
  have next_eq: "nodes (Suc (enumerate ?I n)) = (Suc i,q')"
    using following j by simp
  have property: "?property (alpha,sigma)"
    using alpha source target sigma_plain
    by (simp add: node_eq pair_eq' next_eq)
  have selected: "?property witness"
    unfolding witness_def relative_adp_drp1_instance_witness_def
    apply (rule someI[where x="(alpha,sigma)"])
    using property by (simp add: Let_def)
  show "pair \<in> P" by (fact pair_P)
  show "fst witness \<in> sharp_positions (snd pair)"
    using selected unfolding node_def pair_def by (simp add: Let_def)
  show "mark_adp_root (terms (fst node) |_ snd node) =
      mark_adp_root (fst pair) \<cdot> snd witness"
    using selected unfolding node_def pair_def by (simp add: Let_def)
  show "mark_adp_root
      (terms (fst (nodes (Suc (enumerate ?I n)))) |_
        snd (nodes (Suc (enumerate ?I n)))) =
      mark_adp_root (snd pair |_ fst witness) \<cdot> snd witness"
    using selected unfolding node_def pair_def by (simp add: Let_def)
  show "\<forall>x. snd witness x =
      plain_adp_term (erase_adp_term (snd witness x))"
    using selected unfolding node_def pair_def by (simp add: Let_def)
qed

definition relative_adp_drp1_lhs ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow>
    ('f adp_symbol, 'v) term" where
  "relative_adp_drp1_lhs P A terms nodes n = mark_adp_root
    (fst (relative_adp_drp1_pair P A terms nodes n))"

definition relative_adp_drp1_rhs ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow>
    ('f adp_symbol, 'v) term" where
  "relative_adp_drp1_rhs P A terms nodes n = mark_adp_root
    (snd (relative_adp_drp1_pair P A terms nodes n) |_
      fst (relative_adp_drp1_instance_witness P A terms nodes n))"

definition relative_adp_drp1_subst ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow>
    ('v \<Rightarrow> ('f adp_symbol, 'v) term)" where
  "relative_adp_drp1_subst P A terms nodes n =
    snd (relative_adp_drp1_instance_witness P A terms nodes n)"

lemma relative_adp_drp1_pair_member:
  assumes infinite: "infinite
      (relative_adp_drp1_main_indices P A terms nodes)"
    and path_edge: "\<And>n. (nodes n, nodes (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "(relative_adp_drp1_lhs P A terms nodes n,
      relative_adp_drp1_rhs P A terms nodes n) \<in>
    relative_adp_dp_pairs P"
proof -
  let ?pair = "relative_adp_drp1_pair P A terms nodes n"
  let ?witness = "relative_adp_drp1_instance_witness P A terms nodes n"
  have pair: "?pair \<in> P"
    and alpha: "fst ?witness \<in> sharp_positions (snd ?pair)"
    using relative_adp_drp1_instance_witness[
        OF infinite path_edge steps subset lhs_fun, of n]
    by simp_all
  have subterm: "snd ?pair |_ fst ?witness \<in>
      annotated_rhs_subterms ?pair"
    using alpha unfolding annotated_rhs_subterms_def by blast
  show ?thesis
    using pair subterm
    unfolding relative_adp_dp_pairs_def relative_adp_drp1_lhs_def
      relative_adp_drp1_rhs_def by blast
qed

lemma relative_adp_drp1_link:
  assumes flat: "relative_adp_base_flat B"
    and A: "A = P \<union> B"
    and infinite: "infinite
      (relative_adp_drp1_main_indices P A terms nodes)"
    and path_edge: "\<And>n. (nodes n, nodes (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "(relative_adp_drp1_rhs P A terms nodes n \<cdot>
        relative_adp_drp1_subst P A terms nodes n,
      relative_adp_drp1_lhs P A terms nodes (Suc n) \<cdot>
        relative_adp_drp1_subst P A terms nodes (Suc n)) \<in>
    (adp_step_case_rel (relative_adp_flat_rules A) False)\<^sup>*"
proof -
  let ?I = "relative_adp_drp1_main_indices P A terms nodes"
  let ?k = "enumerate ?I n"
  let ?j = "enumerate ?I (Suc n)"
  have subset: "P \<subseteq> A" unfolding A by blast
  have kI: "?k \<in> ?I" and jI: "?j \<in> ?I"
    by (rule enumerate_in_set[OF infinite])+
  have kj: "?k < ?j" by (rule enumerate_mono[OF _ infinite]) simp
  have no_main: "\<And>m. Suc ?k \<le> m \<Longrightarrow> m < ?j \<Longrightarrow>
      \<not> relative_adp_selected_chain_main_event P A terms (nodes m)"
  proof -
    fix m
    assume lower: "Suc ?k \<le> m" and upper: "m < ?j"
    have strict_lower: "?k < m" using lower by simp
    have strict_lower': "enumerate
        {k. relative_adp_selected_chain_main_event P A terms (nodes k)} n < m"
      using strict_lower unfolding relative_adp_drp1_main_indices_def by simp
    have upper': "m < enumerate
        {k. relative_adp_selected_chain_main_event P A terms (nodes k)} (Suc n)"
      using upper unfolding relative_adp_drp1_main_indices_def by simp
    show "\<not> relative_adp_selected_chain_main_event P A terms (nodes m)"
      by (rule between_consecutive_enumerated_events[
          of "relative_adp_selected_chain_main_event P A terms" nodes n m,
          OF infinite[unfolded relative_adp_drp1_main_indices_def]
            strict_lower' upper'])
  qed
  have unlabeled: "\<And>m. Suc ?k \<le> m \<Longrightarrow> m < ?j \<Longrightarrow>
      \<not> relative_adp_selected_chain_labeled P A terms (nodes m)"
  proof -
    fix m
    assume lower: "Suc ?k \<le> m" and upper: "m < ?j"
    obtain i q where source: "nodes m = (i,q)" by (cases "nodes m") auto
    obtain i' q' where target: "nodes (Suc m) = (i',q')"
      by (cases "nodes (Suc m)") auto
    have edge_raw: "((i,q),(i',q')) \<in>
        relative_adp_selected_chain_origin_edge P A terms"
      using path_edge[of m] unfolding source target .
    have i': "i' = Suc i"
      by (rule relative_adp_selected_chain_origin_edge_time[OF edge_raw])
    have edge: "((i,q),(Suc i,q')) \<in>
        relative_adp_selected_chain_origin_edge P A terms"
      using edge_raw unfolding i' .
    have nonmain: "\<not> relative_adp_selected_chain_main_event
        P A terms (i,q)"
      using no_main[OF lower upper] unfolding source .
    show "\<not> relative_adp_selected_chain_labeled P A terms (nodes m)"
      unfolding source
      by (rule relative_adp_flat_base_path_source_unlabeled[
          OF flat A edge steps[of i] lhs_fun nonmain])
  qed
  have segment: "(nodes (Suc ?k), nodes ?j) \<in>
      {(source,target). (source,target) \<in>
          relative_adp_selected_chain_origin_edge P A terms \<and>
        \<not> relative_adp_selected_chain_labeled P A terms source}\<^sup>*"
    by (rule ipath_interval_restricted_rtrancl[
        where p=nodes
          and E="relative_adp_selected_chain_origin_edge P A terms"
          and i="Suc ?k" and j="?j"
          and allowed="\<lambda>source.
            \<not> relative_adp_selected_chain_labeled P A terms source"])
       (use path_edge kj unlabeled in auto)
  have projection:
      "(mark_adp_root (terms (fst (nodes (Suc ?k))) |_ snd (nodes (Suc ?k))),
        mark_adp_root (terms (fst (nodes ?j)) |_ snd (nodes ?j))) \<in>
      (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
    by (rule relative_adp_selected_unlabeled_rtrancl_projection[
        OF segment steps subset])
  have source_instance:
      "mark_adp_root (terms (fst (nodes (Suc ?k))) |_ snd (nodes (Suc ?k))) =
        relative_adp_drp1_rhs P A terms nodes n \<cdot>
          relative_adp_drp1_subst P A terms nodes n"
    using relative_adp_drp1_instance_witness[
        OF infinite path_edge steps subset lhs_fun, of n]
    unfolding relative_adp_drp1_rhs_def relative_adp_drp1_subst_def
    by simp
  have target_instance:
      "mark_adp_root (terms (fst (nodes ?j)) |_ snd (nodes ?j)) =
        relative_adp_drp1_lhs P A terms nodes (Suc n) \<cdot>
          relative_adp_drp1_subst P A terms nodes (Suc n)"
    using relative_adp_drp1_instance_witness[
        OF infinite path_edge steps subset lhs_fun, of "Suc n"]
    unfolding relative_adp_drp1_lhs_def relative_adp_drp1_subst_def
      relative_adp_drp1_node_def by simp
  show ?thesis
    using projection unfolding source_instance target_instance
      relative_adp_flat_rules_def .
qed

lemma adp_step_case_falseE:
  assumes step: "adp_step_case R False s t"
  obtains l r phi p sigma annotations where
    "(l,r) \<in> R"
    "plain_adp_term_pred l"
    "valid_vrf (l,r) phi"
    "p \<in> fun_poss s"
    "False = (p \<in> sharp_positions s)"
    "erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma"
    "annotations = (if False then sharp_positions r else {}) \<union>
      transported_annotations phi l (s |_ p)"
    "t = (ctxt_of_pos_term p s)\<langle>
      annotate_term annotations (erase_adp_term r \<cdot> sigma)\<rangle>"
proof -
  from step show thesis
  proof cases
    case adp_stepI
    then show thesis by (auto intro: that)
  qed
qed

lemma relative_adp_flat_step_is_rstep:
  assumes step: "(s,t) \<in> adp_step_case_rel
      (relative_adp_flat_rules A) False"
    and source: "s = mark_adp_root u"
  shows "(s,t) \<in> rstep (relative_adp_flat_rules A)"
    and "\<exists>v. t = mark_adp_root v"
proof -
  from step have case_step:
      "adp_step_case (relative_adp_flat_rules A) False s t"
    unfolding adp_step_case_rel_def by simp
  from adp_step_case_falseE[OF case_step]
  obtain l r phi p sigma annotations where
      rule: "(l,r) \<in> relative_adp_flat_rules A"
    and plain: "plain_adp_term_pred l"
    and vrf: "valid_vrf (l,r) phi"
    and p_fun: "p \<in> fun_poss s"
    and at_sharp: "False = (p \<in> sharp_positions s)"
    and match: "erase_adp_term (s |_ p) =
      erase_adp_term l \<cdot> sigma"
    and annotations: "annotations =
      (if False then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ p)"
    and target_ctxt: "t = (ctxt_of_pos_term p s)\<langle>
      annotate_term annotations (erase_adp_term r \<cdot> sigma)\<rangle>" .
  have not_sharp: "p \<notin> sharp_positions s" using at_sharp by simp
  have annotations': "annotations = transported_annotations phi l (s |_ p)"
    using annotations by simp
  from rule obtain pair where pair: "pair \<in> A"
    and l: "l = plain_adp_term (erase_adp_term (fst pair))"
    and r: "r = plain_adp_term (erase_adp_term (snd pair))"
    unfolding relative_adp_flat_rules_def erase_annotations_adp_def by blast
  have p_poss: "p \<in> poss s" by (rule fun_poss_imp_poss[OF p_fun])
  have target: "t = replace_at s p
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    using target_ctxt p_poss by simp
  have p_nonempty: "p \<noteq> []"
  proof
    assume p: "p = []"
    from p_fun have root_fun: "[] \<in> fun_poss s" unfolding p by simp
    then obtain f ts where s_fun: "s = Fun f ts"
      by (cases s) auto
    from source s_fun obtain g us where u_fun: "erase_adp_term u = Fun g us"
      by (cases u) (auto simp: mark_adp_root_def annotate_term_def)
    have "[] \<in> sharp_positions (mark_adp_root u)"
      unfolding mark_adp_root_def
      using sharp_positions_annotate_term[of "[]" "erase_adp_term u" "{[]}"]
        u_fun by simp
    with not_sharp source p show False by simp
  qed
  have p_u: "p \<in> poss u"
    using p_poss source by (simp add: mark_adp_root_def annotate_term_def)
  have source_at: "s |_ p = plain_adp_term (erase_adp_term u |_ p)"
    unfolding source
    by (rule mark_adp_root_nonroot_subt_at[OF p_u p_nonempty])
  have source_at_plain: "sharp_positions (s |_ p) = {}"
    unfolding source_at by simp
  have transported: "transported_annotations phi l (s |_ p) = {}"
    unfolding transported_annotations_def source_at_plain by simp
  have annotations_empty: "annotations = {}"
    using annotations' transported by simp
  let ?sigma = "plain_adp_term \<circ> sigma"
  have lhs_instance: "s |_ p = l \<cdot> ?sigma"
  proof -
    have erased_at: "erase_adp_term (s |_ p) =
        erase_adp_term u |_ p"
      using source_at by simp
    have "plain_adp_term (erase_adp_term (s |_ p)) =
        plain_adp_term (erase_adp_term l \<cdot> sigma)"
      using match by simp
    then show ?thesis
      using source_at l
      by (simp add: plain_adp_term_subst)
  qed
  have rhs_instance: "annotate_term annotations
      (erase_adp_term r \<cdot> sigma) = r \<cdot> ?sigma"
    unfolding annotations_empty r
    by (simp add: plain_adp_term_subst)
  have ordinary: "(s,t) \<in> rstep_r_p_s
      (relative_adp_flat_rules A) (l,r) p ?sigma"
    unfolding rstep_r_p_s_def'
    using rule p_poss lhs_instance target rhs_instance by auto
  show "(s,t) \<in> rstep (relative_adp_flat_rules A)"
    by (rule rstep_r_p_s_imp_rstep[OF ordinary])
  have p_erased: "p \<in> poss (erase_adp_term u)"
    using p_u by simp
  let ?v = "plain_adp_term (replace_at (erase_adp_term u) p
      (erase_adp_term r \<cdot> sigma))"
  have target_marked: "t = mark_adp_root ?v"
  proof -
    have target': "t = replace_at (annotate_term {[]} (erase_adp_term u)) p
        (plain_adp_term (erase_adp_term r \<cdot> sigma))"
      using target rhs_instance source
      unfolding mark_adp_root_def annotations_empty
      by (simp add: r plain_adp_term_subst)
    have annotated: "annotate_term {[]}
        (replace_at (erase_adp_term u) p
          (erase_adp_term r \<cdot> sigma)) =
      replace_at (annotate_term {[]} (erase_adp_term u)) p
        (plain_adp_term (erase_adp_term r \<cdot> sigma))"
      by (rule annotate_single_root_replace_below[OF p_erased p_nonempty])
    show ?thesis
      using target' annotated
      unfolding mark_adp_root_def by simp
  qed
  show "\<exists>v. t = mark_adp_root v"
    by (rule exI[where x="?v"]) (fact target_marked)
qed

lemma relative_adp_flat_steps_preserve_marked:
  assumes steps: "(s,t) \<in> (adp_step_case_rel
      (relative_adp_flat_rules A) False)\<^sup>*"
    and source: "s = mark_adp_root u"
  shows "\<exists>v. t = mark_adp_root v"
  using steps source
proof (induct arbitrary: u rule: rtrancl_induct)
  case base
  show "\<exists>v. s = mark_adp_root v" using source by blast
next
  case (step middle target)
  from step.hyps(3)[OF source] obtain v where
      middle: "middle = mark_adp_root v" by blast
  from relative_adp_flat_step_is_rstep(2)[OF step.hyps(2) middle]
  show "\<exists>v. target = mark_adp_root v" .
qed

lemma relative_adp_flat_steps_are_rsteps:
  assumes steps: "(s,t) \<in> (adp_step_case_rel
      (relative_adp_flat_rules A) False)\<^sup>*"
    and source: "s = mark_adp_root u"
  shows "(s,t) \<in> (rstep (relative_adp_flat_rules A))\<^sup>*"
  using steps source
proof (induct arbitrary: u rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step middle target)
  have prefix: "(s,middle) \<in>
      (rstep (relative_adp_flat_rules A))\<^sup>*"
    by (rule step.hyps(3)[OF source])
  from relative_adp_flat_steps_preserve_marked[
      OF step.hyps(1) source]
  obtain v where middle: "middle = mark_adp_root v" by blast
  have last: "(middle,target) \<in> rstep (relative_adp_flat_rules A)"
    by (rule relative_adp_flat_step_is_rstep(1)[OF step.hyps(2) middle])
  show ?case by (rule rtrancl_into_rtrancl[OF prefix last])
qed

lemma relative_adp_drp1_rstep_link:
  assumes flat: "relative_adp_base_flat B"
    and A: "A = P \<union> B"
    and infinite: "infinite
      (relative_adp_drp1_main_indices P A terms nodes)"
    and path_edge: "\<And>n. (nodes n, nodes (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "(relative_adp_drp1_rhs P A terms nodes n \<cdot>
        relative_adp_drp1_subst P A terms nodes n,
      relative_adp_drp1_lhs P A terms nodes (Suc n) \<cdot>
        relative_adp_drp1_subst P A terms nodes (Suc n)) \<in>
    (rstep (relative_adp_flat_rules A))\<^sup>*"
proof -
  have projected: "(relative_adp_drp1_rhs P A terms nodes n \<cdot>
        relative_adp_drp1_subst P A terms nodes n,
      relative_adp_drp1_lhs P A terms nodes (Suc n) \<cdot>
        relative_adp_drp1_subst P A terms nodes (Suc n)) \<in>
    (adp_step_case_rel (relative_adp_flat_rules A) False)\<^sup>*"
    by (rule relative_adp_drp1_link[OF assms])
  let ?rhs = "snd (relative_adp_drp1_pair P A terms nodes n) |_
    fst (relative_adp_drp1_instance_witness P A terms nodes n)"
  have alpha: "fst (relative_adp_drp1_instance_witness P A terms nodes n)
      \<in> sharp_positions
        (snd (relative_adp_drp1_pair P A terms nodes n))"
    using relative_adp_drp1_instance_witness[
        OF infinite path_edge steps _ lhs_fun, of n]
    unfolding A by auto
  have rhs_fun: "is_Fun ?rhs"
    using alpha unfolding sharp_positions_def
    by (auto split: option.splits)
  have subst_plain: "\<forall>x.
      relative_adp_drp1_subst P A terms nodes n x =
      plain_adp_term (erase_adp_term
        (relative_adp_drp1_subst P A terms nodes n x))"
    using relative_adp_drp1_instance_witness(5)[
        OF infinite path_edge steps _ lhs_fun, of n]
    unfolding relative_adp_drp1_subst_def A by auto
  have source: "relative_adp_drp1_rhs P A terms nodes n \<cdot>
      relative_adp_drp1_subst P A terms nodes n =
    mark_adp_root (?rhs \<cdot>
      relative_adp_drp1_subst P A terms nodes n)"
    unfolding relative_adp_drp1_rhs_def
    using mark_adp_root_subst[OF rhs_fun,
        of "relative_adp_drp1_subst P A terms nodes n"] subst_plain
    by (simp add: fun_eq_iff comp_def)
  show ?thesis
    by (rule relative_adp_flat_steps_are_rsteps[OF projected source])
qed

theorem relative_adp_derelatification_one:
  assumes flat: "relative_adp_base_flat B"
    and lhs_fun: "\<And>pair. pair \<in> P \<union> B \<Longrightarrow>
      is_Fun (fst pair)"
    and finite_dp: "finite_dpp
      (False, False, relative_adp_dp_pairs P, {}, {}, {},
        relative_adp_flat_rules (P \<union> B))"
  shows "adp_problem_SN (P,B)"
proof (rule ccontr)
  let ?A = "P \<union> B"
  assume not_sn: "\<not> adp_problem_SN (P,B)"
  then obtain terms where deriv:
      "ideriv (adp_step_case_rel P True) (adp_step ?A) terms"
    unfolding adp_problem_SN_def SN_rel_ideriv by auto
  have subset: "P \<subseteq> ?A" by blast
  have steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step ?A"
    by (rule relative_adp_ideriv_chain_steps[OF deriv subset])
  from relative_adp_ideriv_selected_origin_dichotomy[OF deriv subset]
  obtain root nodes where path_edge:
      "\<And>n. (nodes n, nodes (Suc n)) \<in>
        relative_adp_selected_chain_origin_edge P ?A terms"
    and dichotomy:
      "(INFM n. relative_adp_selected_chain_main_event P ?A terms (nodes n)) \<or>
       (INFM n. event_offshoot
          (relative_adp_selected_chain_origin_edge P ?A terms)
          (relative_adp_selected_chain_main_event P ?A terms) nodes n)"
    by blast
  have main: "INFM n.
      relative_adp_selected_chain_main_event P ?A terms (nodes n)"
  proof (rule ccontr)
    assume no_main: "\<not> (INFM n.
        relative_adp_selected_chain_main_event P ?A terms (nodes n))"
    with dichotomy have offshoots: "INFM n. event_offshoot
        (relative_adp_selected_chain_origin_edge P ?A terms)
        (relative_adp_selected_chain_main_event P ?A terms) nodes n"
      by blast
    from relative_adp_selected_offshoots_give_branching_base_stream[
        OF offshoots no_main path_edge steps subset lhs_fun]
    have branching: "INFM n.
        relative_adp_selected_label_stream P ?A terms nodes n \<in> ?A - P \<and>
        relative_adp_branching_pair
          (relative_adp_selected_label_stream P ?A terms nodes n) \<and>
        event_offshoot
          (relative_adp_selected_chain_origin_edge P ?A terms)
          (relative_adp_selected_chain_main_event P ?A terms) nodes
          (enumerate
            (relative_adp_selected_label_indices P ?A terms nodes) n)" .
    from branching[unfolded INFM_nat] obtain n where witness:
        "relative_adp_selected_label_stream P ?A terms nodes n \<in> ?A - P"
        "relative_adp_branching_pair
          (relative_adp_selected_label_stream P ?A terms nodes n)"
      by blast
    let ?pair = "relative_adp_selected_label_stream P ?A terms nodes n"
    have pair_B: "?pair \<in> B" using witness(1) by blast
    from witness(2) obtain alpha beta where
        alpha: "alpha \<in> sharp_positions (snd ?pair)"
      and beta: "beta \<in> sharp_positions (snd ?pair)"
      and distinct: "alpha \<noteq> beta"
      unfolding relative_adp_branching_pair_def by blast
    from flat pair_B have "sharp_positions (snd ?pair) = {}"
      unfolding relative_adp_base_flat_def by blast
    with alpha show False by simp
  qed
  let ?I = "relative_adp_drp1_main_indices P ?A terms nodes"
  have infinite: "infinite ?I"
    using main unfolding relative_adp_drp1_main_indices_def INFM_iff_infinite .
  let ?s = "relative_adp_drp1_lhs P ?A terms nodes"
  let ?t = "relative_adp_drp1_rhs P ?A terms nodes"
  let ?sigma = "relative_adp_drp1_subst P ?A terms nodes"
  have A_eq: "?A = P \<union> B" by simp
  have pairs: "\<And>n. (?s n, ?t n) \<in> relative_adp_dp_pairs P"
    by (rule relative_adp_drp1_pair_member[
        OF infinite path_edge steps subset lhs_fun])
  have links: "\<And>n. (?t n \<cdot> ?sigma n,
      ?s (Suc n) \<cdot> ?sigma (Suc n)) \<in>
      (rstep (relative_adp_flat_rules ?A))\<^sup>*"
    by (rule relative_adp_drp1_rstep_link[
        OF flat A_eq infinite path_edge steps lhs_fun])
  have chain: "min_ichain
      (False, False, relative_adp_dp_pairs P, {}, {}, {},
        relative_adp_flat_rules ?A) ?s ?t ?sigma"
    unfolding min_ichain.simps ichain.simps
    using pairs links by simp
  from finite_dp show False unfolding finite_dpp_def using chain by blast
qed

end
