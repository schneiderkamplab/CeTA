theory Relative_ADP_Dependency_Graph
  imports
    Relative_ADP_Processors_Dev.Relative_ADP_Processors
    Finite_Branching_Dichotomy
begin

text \<open>
  Executable reconstruction of a dependency-graph child from Theorem 33.
  The selected indices address the canonical list @{term "P @ B"}; graph
  admissibility of the selected set is checked by the next layer.
\<close>

definition relative_adp_graph_selected ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow> nat list \<Rightarrow>
    ('f, 'v) adp list" where
  "relative_adp_graph_selected P B indices = map (\<lambda>i. (P @ B) ! i) indices"

definition relative_adp_graph_child_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow> nat list \<Rightarrow>
    ('f, 'v) adp list \<times> ('f, 'v) adp list" where
  "relative_adp_graph_child_list P B indices = (let
      Q = set (relative_adp_graph_selected P B indices)
    in (filter (\<lambda>p. p \<in> Q) P,
        remdups (filter (\<lambda>p. p \<in> Q) B @
          map erase_annotations_adp (filter (\<lambda>p. p \<notin> Q) (P @ B)))))"

lemma relative_adp_graph_selected_set:
  assumes bounds: "\<forall>i \<in> set indices. i < length (P @ B)"
  shows "set (relative_adp_graph_selected P B indices) =
    (\<lambda>i. (P @ B) ! i) ` set indices"
  using bounds unfolding relative_adp_graph_selected_def by auto

lemma relative_adp_graph_child_list_sets:
  assumes bounds: "\<forall>i \<in> set indices. i < length (P @ B)"
  defines "Q \<equiv> set (relative_adp_graph_selected P B indices)"
  shows "case relative_adp_graph_child_list P B indices of (P',B') \<Rightarrow>
    (set P', set B') =
      (set P \<inter> Q,
       (set B \<inter> Q) \<union>
         erase_annotations_adp ` ((set P \<union> set B) - Q))"
  using bounds
  by (auto simp: relative_adp_graph_child_list_def Q_def Let_def)

lemma relative_adp_graph_child_main_subset:
  "set (fst (relative_adp_graph_child_list P B indices)) \<subseteq> set P"
  by (auto simp: relative_adp_graph_child_list_def Let_def)

definition mark_adp_root ::
  "('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term" where
  "mark_adp_root t = annotate_term {[]} (erase_adp_term t)"

lemma annotate_outside_plain:
  fixes t :: "('f, 'v) term" and ts :: "('f, 'v) term list"
  shows "(\<forall>q. p @ q \<notin> A) \<Longrightarrow>
    annotate_term_at A p t = plain_adp_term t"
  and "(\<forall>q. p @ q \<notin> A) \<Longrightarrow>
    annotate_terms_at A p i ts = map plain_adp_term ts"
proof (induct t and ts arbitrary: A p and A p i
    rule: annotate_term_at_annotate_terms_at.induct)
  case (1 A p x)
  then show ?case by simp
next
  case (2 A p f ts)
  have p_notin: "p \<notin> A"
    using "2.prems"[rule_format, of "[]"] by simp
  have children: "annotate_terms_at A p 0 ts = map plain_adp_term ts"
    by (rule "2.hyps"[OF "2.prems"])
  show ?case using p_notin children by simp
next
  case (3 A p i)
  then show ?case by simp
next
  case (4 A p i t ts)
  have below: "\<forall>q. (p @ [i]) @ q \<notin> A"
    using "4.prems" by (simp add: append_assoc)
  have head: "annotate_term_at A (p @ [i]) t = plain_adp_term t"
    by (rule "4.hyps"(1)[OF below])
  have tail: "annotate_terms_at A p (Suc i) ts = map plain_adp_term ts"
    by (rule "4.hyps"(2)[OF "4.prems"])
  show ?case using head tail by simp
qed

lemma annotate_single_root_plain:
  "p \<noteq> [] \<Longrightarrow>
    annotate_term_at {[]} p t = plain_adp_term t"
  by (rule annotate_outside_plain) auto

lemma annotate_empty_plain [simp]:
  "annotate_term {} t = plain_adp_term t"
  unfolding annotate_term_def
  by (rule annotate_outside_plain) simp

lemma annotate_single_root_children:
  "annotate_terms_at {[]} [] i ts = map plain_adp_term ts"
  by (induct ts arbitrary: i) (auto simp: annotate_single_root_plain)

lemma annotate_single_root_fun [simp]:
  "annotate_term {[]} (Fun f ts) =
    Fun (Sharp f) (map plain_adp_term ts)"
  unfolding annotate_term_def
  by (simp add: annotate_single_root_children)

lemma plain_adp_term_subst:
  "plain_adp_term (t \<cdot> sigma) =
    plain_adp_term t \<cdot> (plain_adp_term \<circ> sigma)"
  by (induct t) (auto simp: map_idI)

lemma erase_adp_term_subst:
  "erase_adp_term (t \<cdot> sigma) =
    erase_adp_term t \<cdot> (erase_adp_term \<circ> sigma)"
  by (induct t) (auto simp: map_idI)

lemma mark_adp_root_subst:
  assumes "is_Fun t"
  shows "mark_adp_root (t \<cdot> sigma) =
    mark_adp_root t \<cdot>
      (plain_adp_term \<circ> erase_adp_term \<circ> sigma)"
  using assms
  by (cases t) (simp_all add: mark_adp_root_def plain_adp_term_subst
      erase_adp_term_subst comp_def)

lemma mark_adp_root_erased_instance:
  assumes t_fun: "is_Fun t"
    and erased: "erase_adp_term u = erase_adp_term t \<cdot> sigma"
  shows "mark_adp_root u =
    mark_adp_root t \<cdot> (plain_adp_term \<circ> sigma)"
  using t_fun erased
  by (cases t) (simp_all add: mark_adp_root_def plain_adp_term_subst
      comp_def)

lemma poss_plain_adp_term [simp]:
  "poss (plain_adp_term t) = poss t"
  by (induct t) auto

lemma plain_adp_term_replace_at:
  assumes p: "p \<in> poss t"
  shows "plain_adp_term (replace_at t p u) =
    replace_at (plain_adp_term t) p (plain_adp_term u)"
  using p
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t) auto
  show ?case unfolding t
    using i Cons.hyps[OF p]
    by (simp add: take_map drop_map)
qed

lemma annotate_single_root_replace_below:
  assumes p: "p \<in> poss t" and nonroot: "p \<noteq> []"
  shows "annotate_term {[]} (replace_at t p u) =
    replace_at (annotate_term {[]} t) p (plain_adp_term u)"
proof -
  from nonroot obtain i ps where p_shape: "p = i # ps"
    by (cases p) auto
  from p[unfolded p_shape] obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts" and ps: "ps \<in> poss (ts ! i)"
    by (cases t) auto
  show ?thesis unfolding t p_shape
    using i plain_adp_term_replace_at[OF ps, of u]
    by (simp add: map_update take_map drop_map)
qed

lemma annotate_term_at_subt_at:
  assumes p: "p \<in> poss t"
  shows "annotate_term_at A base t |_ p =
    annotate_term_at A (base @ p) (t |_ p)"
  using p
proof (induct p arbitrary: t base)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t) auto
  have nth: "annotate_terms_at A base 0 ts ! i =
      annotate_term_at A (base @ [i]) (ts ! i)"
    using annotate_terms_at_nth[OF i, of A base 0] by simp
  show ?case
    unfolding t using i nth Cons.hyps[OF p, of "base @ [i]"]
    by (simp add: append_assoc)
qed

lemma mark_adp_root_nonroot_subt_at:
  assumes p: "p \<in> poss t" and nonroot: "p \<noteq> []"
  shows "mark_adp_root t |_ p = plain_adp_term (erase_adp_term t |_ p)"
proof -
  have p_erased: "p \<in> poss (erase_adp_term t)" using p by simp
  have annotated: "annotate_term {[]} (erase_adp_term t) |_ p =
      annotate_term_at {[]} p (erase_adp_term t |_ p)"
    unfolding annotate_term_def
    using annotate_term_at_subt_at[OF p_erased, of "{[]}" "[]"] by simp
  show ?thesis unfolding mark_adp_root_def annotated
    by (rule annotate_single_root_plain[OF nonroot])
qed

lemma sharp_positions_plain_adp_term [simp]:
  "sharp_positions (plain_adp_term t) = {}"
proof (rule ccontr)
  assume "sharp_positions (plain_adp_term t) \<noteq> {}"
  then obtain p where sharp: "p \<in> sharp_positions (plain_adp_term t)"
    by blast
  then have p: "p \<in> poss t" unfolding sharp_positions_def by simp
  from sharp have marked:
      "case root (plain_adp_term t |_ p) of
        Some (f, _) \<Rightarrow> is_sharp_symbol f | None \<Rightarrow> False"
    unfolding sharp_positions_def by blast
  have at: "plain_adp_term t |_ p = plain_adp_term (t |_ p)"
    by (rule plain_adp_term_subt_at[OF p])
  show False using marked at by (cases "t |_ p") auto
qed

lemma annotate_single_root_below_adp_step:
  assumes rule: "(l,r) \<in> A"
    and valid: "valid_vrf (l,r) phi"
    and delta_fun: "delta \<in> fun_poss u"
    and nonroot: "delta \<noteq> []"
    and redex: "u |_ delta = erase_adp_term l \<cdot> sigma"
  shows "(annotate_term {[]} u,
      annotate_term {[]} (replace_at u delta
        (erase_adp_term r \<cdot> sigma))) \<in>
    adp_step_case_rel (erase_annotations_adp ` A) False"
proof -
  let ?source = "annotate_term {[]} u"
  let ?plain_pair = "erase_annotations_adp (l,r)"
  have pair: "?plain_pair \<in> erase_annotations_adp ` A"
    using rule by blast
  have pair_expanded:
      "(fst ?plain_pair, snd ?plain_pair) \<in> erase_annotations_adp ` A"
    using pair by simp
  have lhs_plain: "plain_adp_term_pred (fst ?plain_pair)"
    unfolding erase_annotations_adp_def by simp
  have vrf: "valid_vrf ?plain_pair (\<lambda>_. None)"
    by (rule empty_vrf_valid)
  have vrf_expanded:
      "valid_vrf (fst ?plain_pair, snd ?plain_pair) (\<lambda>_. None)"
    using vrf by simp
  have delta_poss: "delta \<in> poss u"
    by (rule fun_poss_imp_poss[OF delta_fun])
  have source_delta: "?source |_ delta = plain_adp_term (u |_ delta)"
  proof -
    have "?source = mark_adp_root (plain_adp_term u)"
      unfolding mark_adp_root_def by simp
    moreover have "delta \<in> poss (plain_adp_term u)" using delta_poss by simp
    ultimately show ?thesis
      using mark_adp_root_nonroot_subt_at[OF _ nonroot,
          of "plain_adp_term u"] by simp
  qed
  have delta_source_fun: "delta \<in> fun_poss ?source"
    using delta_fun fun_poss_erase_adp_term[of ?source] by simp
  have unsharp: "delta \<notin> sharp_positions ?source"
    using sharp_positions_annotate_term[OF delta_fun, of "{[]}"] nonroot
    by simp
  have erase_plain_sigma:
      "erase_adp_term \<circ> (plain_adp_term \<circ> sigma) = sigma"
    by (rule ext) simp
  have lhs_match: "erase_adp_term (?source |_ delta) =
      erase_adp_term (fst ?plain_pair) \<cdot> sigma"
    using source_delta redex
    unfolding erase_annotations_adp_def
    by (simp add: plain_adp_term_subst erase_adp_term_subst
        erase_plain_sigma)
  have no_transport:
      "transported_annotations (\<lambda>_. None)
        (fst ?plain_pair) (?source |_ delta) = {}"
    unfolding transported_annotations_def by simp
  have target_shape:
      "replace_at ?source delta
        (annotate_term {}
          (erase_adp_term (snd ?plain_pair) \<cdot> sigma)) =
       annotate_term {[]} (replace_at u delta
         (erase_adp_term r \<cdot> sigma))"
    unfolding erase_annotations_adp_def
    using annotate_single_root_replace_below[OF delta_poss nonroot,
        of "erase_adp_term r \<cdot> sigma"]
    by (simp add: plain_adp_term_subst)
  have "adp_step_case (erase_annotations_adp ` A) False ?source
      (annotate_term {[]} (replace_at u delta
        (erase_adp_term r \<cdot> sigma)))"
    apply (rule adp_step_case.adp_stepI[
          where sigma=sigma and A="{}",
          OF pair_expanded lhs_plain vrf_expanded delta_source_fun])
    subgoal using unsharp by simp
    subgoal by (fact lhs_match)
    subgoal using no_transport by simp
    subgoal by (rule sym[OF target_shape])
    done
  then show ?thesis unfolding adp_step_case_rel_def by simp
qed

definition annotated_rhs_subterms ::
  "('f, 'v) adp \<Rightarrow> ('f adp_symbol, 'v) term set" where
  "annotated_rhs_subterms p = {snd p |_ q | q. q \<in> sharp_positions (snd p)}"

definition relative_adp_dependency_edge ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp \<Rightarrow> ('f, 'v) adp \<Rightarrow> bool" where
  "relative_adp_dependency_edge A p q \<longleftrightarrow>
    (\<exists>u \<in> annotated_rhs_subterms p. \<exists>sigma tau.
      (mark_adp_root u \<cdot> sigma, mark_adp_root (fst q) \<cdot> tau) \<in>
        (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*)"

definition relative_adp_dependency_graph ::
  "('f, 'v) adp set \<Rightarrow> (('f, 'v) adp) rel" where
  "relative_adp_dependency_graph A =
    {(p,q). p \<in> A \<and> q \<in> A \<and> relative_adp_dependency_edge A p q}"

definition relative_adp_dependency_component ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp \<Rightarrow> ('f, 'v) adp set" where
  "relative_adp_dependency_component A anchor =
    {pair \<in> A.
      (anchor,pair) \<in> (relative_adp_dependency_graph A)\<^sup>* \<and>
      (pair,anchor) \<in> (relative_adp_dependency_graph A)\<^sup>*}"

definition relative_adp_branching_pair ::
  "('f, 'v) adp \<Rightarrow> bool" where
  "relative_adp_branching_pair pair \<longleftrightarrow>
    (\<exists>alpha beta. alpha \<in> sharp_positions (snd pair) \<and>
      beta \<in> sharp_positions (snd pair) \<and> alpha \<noteq> beta)"

definition relative_adp_lasso_graph_problem ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set" where
  "relative_adp_lasso_graph_problem P B = erase_annotations_adp ` P \<union> B"

lemma erase_annotations_adp_idem [simp]:
  "erase_annotations_adp (erase_annotations_adp pair) =
    erase_annotations_adp pair"
  by (cases pair) (simp add: erase_annotations_adp_def)

lemma relative_adp_lasso_graph_problem_erasure:
  "erase_annotations_adp ` relative_adp_lasso_graph_problem P B =
    erase_annotations_adp ` (P \<union> B)"
proof -
  have "erase_annotations_adp ` (erase_annotations_adp ` P) =
      erase_annotations_adp ` P"
    by (simp add: image_image)
  then show ?thesis unfolding relative_adp_lasso_graph_problem_def by auto
qed

lemma relative_adp_dependency_edge_erasure_cong:
  assumes "erase_annotations_adp ` A = erase_annotations_adp ` A'"
  shows "relative_adp_dependency_edge A pair next =
    relative_adp_dependency_edge A' pair next"
  using assms unfolding relative_adp_dependency_edge_def by simp

lemma finite_annotated_rhs_subterms [simp]:
  "finite (annotated_rhs_subterms p)"
proof -
  have "annotated_rhs_subterms p =
      (\<lambda>q. snd p |_ q) ` sharp_positions (snd p)"
    unfolding annotated_rhs_subterms_def by blast
  moreover have "finite (sharp_positions (snd p))"
    unfolding sharp_positions_def by (rule finite_subset[OF _ finite_poss]) auto
  ultimately show ?thesis by simp
qed

lemma relative_adp_dependency_edge_nodes:
  assumes "relative_adp_dependency_edge A p q"
    and "p \<in> A" and "q \<in> A"
  shows "(p,q) \<in> A \<times> A"
  using assms by simp

definition relative_adp_canonical_origin_edge ::
  "('f, 'v) adp set \<Rightarrow> bool \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f, 'v) adp \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool" where
  "relative_adp_canonical_origin_edge P at_sharp s t pair redex q q' \<longleftrightarrow>
    (\<exists>l r phi sigma A.
      pair = (l,r) \<and> (l,r) \<in> P \<and>
      plain_adp_term_pred l \<and> valid_vrf (l,r) phi \<and>
      redex \<in> fun_poss s \<and> at_sharp = (redex \<in> sharp_positions s) \<and>
      erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma \<and>
      A = (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ redex) \<and>
      t = replace_at s redex
        (annotate_term A (erase_adp_term r \<cdot> sigma)) \<and>
      origin_edge (erase_adp_term l) (erase_adp_term r) redex sigma
        (if at_sharp then sharp_positions r else {}) phi q q')"

lemma relative_adp_canonical_origin_edge_is_step:
  assumes edge:
    "relative_adp_canonical_origin_edge P at_sharp s t pair redex q q'"
  shows "adp_step_case P at_sharp s t"
  using edge unfolding relative_adp_canonical_origin_edge_def
  by (auto intro: adp_step_case.adp_stepI)

lemma relative_adp_canonical_origin_edge_preserves_sharp:
  assumes edge:
      "relative_adp_canonical_origin_edge P at_sharp s t pair redex q q'"
    and source: "q \<in> sharp_positions s"
  shows "q' \<in> sharp_positions t"
proof -
  from edge obtain l r phi sigma A where
      p: "redex \<in> fun_poss s"
    and at: "at_sharp = (redex \<in> sharp_positions s)"
    and A: "A = (if at_sharp then sharp_positions r else {}) \<union>
      transported_annotations phi l (s |_ redex)"
    and t: "t = replace_at s redex
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
    and origin: "origin_edge (erase_adp_term l) (erase_adp_term r)
      redex sigma (if at_sharp then sharp_positions r else {}) phi q q'"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have p_poss: "redex \<in> poss s" by (rule fun_poss_imp_poss[OF p])
  from origin show ?thesis
  proof cases
    case preserved
    have q': "q' = q" using preserved by simp
    have outside: "q <\<^sub>p redex \<or> q \<bottom> redex" using preserved by simp
    show ?thesis unfolding q' t
      by (rule sharp_positions_replace_outside[OF source p_poss outside])
  next
    case (root_target alpha)
    have at_sharp: at_sharp using root_target by (cases at_sharp) auto
    have sharp_r: "alpha \<in> sharp_positions r"
      using root_target at_sharp by simp
    from sharp_r obtain f n where alpha_poss: "alpha \<in> poss r"
      and alpha_root: "root (r |_ alpha) = Some (f,n)"
      unfolding sharp_positions_def by (auto split: option.splits prod.splits)
    have alpha_fun: "alpha \<in> fun_poss r"
    proof (rule poss_is_Fun_fun_poss[OF alpha_poss])
      show "is_Fun (r |_ alpha)"
        using alpha_root by (cases "r |_ alpha") auto
    qed
    have alpha_subst: "alpha \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
      using fun_poss_subst[of alpha "erase_adp_term r" sigma]
        alpha_fun poss_erase_adp_term
      by (metis fun_poss_erase_adp_term)
    have alpha_A: "alpha \<in> A" using A sharp_r at_sharp by simp
    have alpha_marked:
      "alpha \<in> sharp_positions
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
      using sharp_positions_annotate_term[OF alpha_subst] alpha_A by simp
    show ?thesis unfolding root_target t
      by (rule sharp_positions_replace_at_append[OF p_poss alpha_marked])
  next
    case (variable_transport rho alpha beta)
    have local_source: "rho @ beta \<in> sharp_positions (s |_ redex)"
      using source variable_transport
        sharp_positions_below_iff[OF p_poss, of "rho @ beta"]
      by simp
    have transported: "alpha @ beta \<in>
      transported_annotations phi l (s |_ redex)"
      unfolding transported_annotations_def
      using variable_transport local_source by auto
    have target_fun: "alpha @ beta \<in>
      fun_poss (erase_adp_term r \<cdot> sigma)"
      using variable_transport by simp
    have target_A: "alpha @ beta \<in> A" using A transported by simp
    have target_marked: "alpha @ beta \<in> sharp_positions
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
      using sharp_positions_annotate_term[OF target_fun] target_A by simp
    show ?thesis unfolding variable_transport t
      by (rule sharp_positions_replace_at_append[OF p_poss target_marked])
  qed
qed

lemma finite_relative_adp_canonical_origin_successors:
  assumes source: "q \<in> sharp_positions s"
  shows "finite {q'. relative_adp_canonical_origin_edge
    P at_sharp s t pair redex q q'}"
proof (rule finite_subset[of _ "sharp_positions t"])
  show "{q'. relative_adp_canonical_origin_edge
      P at_sharp s t pair redex q q'} \<subseteq> sharp_positions t"
    using relative_adp_canonical_origin_edge_preserves_sharp[OF _ source]
    by blast
  show "finite (sharp_positions t)"
    unfolding sharp_positions_def
    by (rule finite_subset[OF _ finite_poss]) auto
qed

lemma adp_pr_step_has_labeled_root_origins:
  assumes step: "adp_step_case P True s t"
  obtains pair p where
    "pair \<in> P"
    "p \<in> sharp_positions s"
    "\<forall>alpha \<in> sharp_positions (snd pair).
      relative_adp_canonical_origin_edge P True s t pair p p (p @ alpha)"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  have p_sharp: "p \<in> sharp_positions s" using adp_stepI(5) by simp
  have roots: "\<forall>alpha \<in> sharp_positions r.
      relative_adp_canonical_origin_edge P True s t (l,r) p p (p @ alpha)"
  proof (intro ballI)
    fix alpha
    assume alpha: "alpha \<in> sharp_positions r"
    show "relative_adp_canonical_origin_edge P True s t
      (l,r) p p (p @ alpha)"
      unfolding relative_adp_canonical_origin_edge_def
      apply (rule exI[where x = l])
      apply (rule exI[where x = r])
      apply (rule exI[where x = phi])
      apply (rule exI[where x = sigma])
      apply (rule exI[where x = A])
      using adp_stepI p_sharp alpha
      by (auto intro: origin_edge.root_target)
  qed
  show thesis
  proof (rule that[where pair = "(l,r)" and p = p])
    show "(l,r) \<in> P" by (rule adp_stepI(1))
    show "p \<in> sharp_positions s" by (rule p_sharp)
    show "\<forall>alpha \<in> sharp_positions (snd (l,r)).
      relative_adp_canonical_origin_edge P True s t (l,r) p p (p @ alpha)"
      using roots by simp
  qed
qed

lemma adp_pr_step_has_a_labeled_root_origin:
  assumes step: "adp_step_case P True s t"
    and annotated: "\<forall>pair \<in> P. sharp_positions (snd pair) \<noteq> {}"
  obtains pair p q where
    "pair \<in> P"
    "p \<in> sharp_positions s"
    "relative_adp_canonical_origin_edge P True s t pair p p q"
proof (rule adp_pr_step_has_labeled_root_origins[OF step])
  fix pair p
  assume pair: "pair \<in> P"
    and p: "p \<in> sharp_positions s"
    and roots: "\<forall>alpha \<in> sharp_positions (snd pair).
      relative_adp_canonical_origin_edge P True s t pair p p (p @ alpha)"
  from annotated[rule_format, OF pair]
  obtain alpha where alpha: "alpha \<in> sharp_positions (snd pair)" by blast
  show thesis by (rule that[OF pair p roots[rule_format, OF alpha]])
qed

lemma relative_adp_replace_at_overwrite:
  assumes p: "p \<in> poss t"
  shows "replace_at (replace_at t p u) p v = replace_at t p v"
proof -
  have ctxt: "ctxt_of_pos_term p (replace_at t p u) = ctxt_of_pos_term p t"
    by (rule ctxt_of_pos_term_replace_at_below[OF p, where p' = p]) simp
  show ?thesis using ctxt by simp
qed

lemma sharp_positions_replace_outside_iff:
  assumes p: "p \<in> poss s"
    and outside: "q <\<^sub>p p \<or> q \<bottom> p"
  shows "q \<in> sharp_positions (replace_at s p u) \<longleftrightarrow>
    q \<in> sharp_positions s"
proof
  assume target: "q \<in> sharp_positions (replace_at s p u)"
  have p_after: "p \<in> poss (replace_at s p u)"
    by (rule replace_at_below_poss[OF p]) simp
  have overwrite:
    "replace_at (replace_at s p u) p (s |_ p) = replace_at s p (s |_ p)"
    by (rule relative_adp_replace_at_overwrite[OF p])
  have restore_inner: "replace_at s p (s |_ p) = s"
    by (rule replace_at_ident[OF p]) simp
  have restored: "replace_at (replace_at s p u) p (s |_ p) = s"
    using overwrite restore_inner by simp
  have "q \<in> sharp_positions
      (replace_at (replace_at s p u) p (s |_ p))"
    by (rule sharp_positions_replace_outside[OF target p_after outside])
  then show "q \<in> sharp_positions s" unfolding restored .
next
  assume source: "q \<in> sharp_positions s"
  show "q \<in> sharp_positions (replace_at s p u)"
    by (rule sharp_positions_replace_outside[OF source p outside])
qed

lemma adp_step_sharp_position_has_labeled_predecessor:
  assumes step: "adp_step_case P at_sharp s t"
    and target: "q' \<in> sharp_positions t"
  obtains pair redex q where
    "pair \<in> P"
    "q \<in> sharp_positions s"
    "relative_adp_canonical_origin_edge P at_sharp s t pair redex q q'"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  have p_poss: "p \<in> poss s"
    by (rule fun_poss_imp_poss[OF adp_stepI(4)])
  have canonical:
    "\<And>q. origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
        (if at_sharp then sharp_positions r else {}) phi q q' \<Longrightarrow>
      relative_adp_canonical_origin_edge P at_sharp s t (l,r) p q q'"
    unfolding relative_adp_canonical_origin_edge_def
    using adp_stepI by blast
  from pos_cases[of p q']
  consider (below) "p \<le>\<^sub>p q'"
    | (above) "q' <\<^sub>p p"
    | (parallel) "p \<bottom> q'"
    by blast
  then show thesis
  proof cases
    case below
    from prefixE[OF below] obtain a where q': "q' = p @ a" by blast
    have p_after: "p \<in> poss t"
      unfolding adp_stepI(8)
      by (rule replace_at_below_poss[OF p_poss]) simp
    have local_target:
      "a \<in> sharp_positions
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
      using target sharp_positions_below_iff[OF p_after, of a]
        replace_at_subt_at[OF p_poss]
      unfolding adp_stepI(8) q' by simp
    from local_target have a_poss:
      "a \<in> poss (annotate_term A (erase_adp_term r \<cdot> sigma))"
      unfolding sharp_positions_def by auto
    have a_erased_poss: "a \<in> poss (erase_adp_term r \<cdot> sigma)"
      using a_poss poss_annotate_term_at[of A "[]"
        "erase_adp_term r \<cdot> sigma"]
      unfolding annotate_term_def by simp
    from local_target obtain f n where a_root:
      "root (annotate_term A (erase_adp_term r \<cdot> sigma) |_ a) =
        Some (f,n)"
      unfolding sharp_positions_def
      by (auto split: option.splits prod.splits)
    have a_fun: "a \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
    proof (rule poss_is_Fun_fun_poss[OF a_erased_poss])
      from a_root show "is_Fun (erase_adp_term r \<cdot> sigma |_ a)"
        using erase_annotate_term[of A "erase_adp_term r \<cdot> sigma"]
          erase_adp_term_subt_at[OF a_poss]
        by (cases "annotate_term A (erase_adp_term r \<cdot> sigma) |_ a")
           auto
    qed
    have a_A: "a \<in> A"
      using local_target sharp_positions_annotate_term[OF a_fun] by simp
    from a_A show thesis
      unfolding adp_stepI(7)
    proof
      assume root: "a \<in> (if at_sharp then sharp_positions r else {})"
      have at: at_sharp by (cases at_sharp) (use root in auto)
      have p_sharp: "p \<in> sharp_positions s" using adp_stepI(5) at by simp
      have edge: "origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
          (if at_sharp then sharp_positions r else {}) phi p q'"
        unfolding q' by (rule origin_edge.root_target[OF root])
      show thesis by (rule that[OF adp_stepI(1) p_sharp canonical[OF edge]])
    next
      assume transported: "a \<in> transported_annotations phi l (s |_ p)"
      then obtain rho alpha beta where
          a: "a = alpha @ beta"
        and rho: "rho \<in> var_poss l"
        and phi: "phi rho = Some alpha"
        and source_local: "rho @ beta \<in> sharp_positions (s |_ p)"
        unfolding transported_annotations_def by blast
      have source: "p @ rho @ beta \<in> sharp_positions s"
        using source_local sharp_positions_below_iff[OF p_poss, of "rho @ beta"]
        by simp
      have target_fun:
        "alpha @ beta \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
        using a_fun a by simp
      have rho_erased: "rho \<in> var_poss (erase_adp_term l)"
        using rho var_poss_erase_adp_term by simp
      have edge0: "origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
          (if at_sharp then sharp_positions r else {}) phi
          (p @ rho @ beta) (p @ alpha @ beta)"
        by (rule origin_edge.variable_transport[
              where rho = rho and l = "erase_adp_term l" and phi = phi
                and alpha = alpha and beta = beta
                and r = "erase_adp_term r" and sigma = sigma and p = p
                and A = "if at_sharp then sharp_positions r else {}"])
           (rule rho_erased, rule phi, rule target_fun)
      have edge: "origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
          (if at_sharp then sharp_positions r else {}) phi
          (p @ rho @ beta) q'"
        using edge0 unfolding q' a .
      show thesis by (rule that[OF adp_stepI(1) source canonical[OF edge]])
    qed
  next
    case above
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF p_poss]
      unfolding adp_stepI(8) by (simp add: above)
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
        (if at_sharp then sharp_positions r else {}) phi q' q'"
      by (rule origin_edge.preserved) (rule disjI1[OF above])
    show thesis by (rule that[OF adp_stepI(1) source canonical[OF edge]])
  next
    case parallel
    have outside: "q' \<bottom> p" by (rule parallel_pos_sym[OF parallel])
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF p_poss]
      unfolding adp_stepI(8) by (simp add: outside)
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
        (if at_sharp then sharp_positions r else {}) phi q' q'"
      by (rule origin_edge.preserved) (rule disjI2[OF outside])
    show thesis by (rule that[OF adp_stepI(1) source canonical[OF edge]])
  qed
qed

definition relative_adp_applied_at ::
  "('f, 'v) adp set \<Rightarrow> bool \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f, 'v) adp \<Rightarrow> pos \<Rightarrow> bool" where
  "relative_adp_applied_at P at_sharp s t pair p \<longleftrightarrow>
    (\<exists>l r phi sigma A.
      pair = (l,r) \<and> (l,r) \<in> P \<and>
      plain_adp_term_pred l \<and> valid_vrf (l,r) phi \<and>
      p \<in> fun_poss s \<and> at_sharp = (p \<in> sharp_positions s) \<and>
      erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma \<and>
      A = (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ p) \<and>
      t = replace_at s p
        (annotate_term A (erase_adp_term r \<cdot> sigma)))"

lemma adp_step_case_has_applied_witness:
  assumes step: "adp_step_case P at_sharp s t"
  obtains pair p where
    "relative_adp_applied_at P at_sharp s t pair p"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  show thesis
    by (rule that[where pair = "(l,r)" and p = p])
       (use adp_stepI in
        \<open>auto simp: relative_adp_applied_at_def\<close>)
qed

lemma relative_adp_applied_at_sharp_position_has_predecessor:
  assumes applied: "relative_adp_applied_at P at_sharp s t pair redex"
    and target: "q' \<in> sharp_positions t"
  obtains q where
    "q \<in> sharp_positions s"
    "relative_adp_canonical_origin_edge P at_sharp s t
      pair redex q q'"
proof -
  from applied obtain l r phi sigma A where
      pair: "pair = (l,r)"
    and rule: "(l,r) \<in> P"
    and plain: "plain_adp_term_pred l"
    and valid: "valid_vrf (l,r) phi"
    and redex_fun: "redex \<in> fun_poss s"
    and at: "at_sharp = (redex \<in> sharp_positions s)"
    and lhs: "erase_adp_term (s |_ redex) = erase_adp_term l \<cdot> sigma"
    and annotations: "A =
      (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ redex)"
    and target_term: "t = replace_at s redex
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_applied_at_def by blast
  have redex_poss: "redex \<in> poss s"
    by (rule fun_poss_imp_poss[OF redex_fun])
  have canonical:
    "\<And>q. origin_edge (erase_adp_term l) (erase_adp_term r) redex sigma
        (if at_sharp then sharp_positions r else {}) phi q q' \<Longrightarrow>
      relative_adp_canonical_origin_edge P at_sharp s t
        pair redex q q'"
    unfolding relative_adp_canonical_origin_edge_def
    using pair rule plain valid redex_fun at lhs annotations target_term by blast
  from pos_cases[of redex q']
  consider (below) "redex \<le>\<^sub>p q'"
    | (above) "q' <\<^sub>p redex"
    | (parallel) "redex \<bottom> q'"
    by blast
  then show thesis
  proof cases
    case below
    from prefixE[OF below] obtain a where q': "q' = redex @ a" by blast
    have redex_after: "redex \<in> poss t"
      unfolding target_term
      by (rule replace_at_below_poss[OF redex_poss]) simp
    have local_target:
      "a \<in> sharp_positions
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
      using target sharp_positions_below_iff[OF redex_after, of a]
        replace_at_subt_at[OF redex_poss]
      unfolding target_term q' by simp
    from local_target have a_poss:
      "a \<in> poss (annotate_term A (erase_adp_term r \<cdot> sigma))"
      unfolding sharp_positions_def by auto
    have a_erased_poss: "a \<in> poss (erase_adp_term r \<cdot> sigma)"
      using a_poss poss_annotate_term_at[of A "[]"
        "erase_adp_term r \<cdot> sigma"]
      unfolding annotate_term_def by simp
    from local_target obtain f n where a_root:
      "root (annotate_term A (erase_adp_term r \<cdot> sigma) |_ a) =
        Some (f,n)"
      unfolding sharp_positions_def
      by (auto split: option.splits prod.splits)
    have a_fun: "a \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
    proof (rule poss_is_Fun_fun_poss[OF a_erased_poss])
      from a_root show "is_Fun (erase_adp_term r \<cdot> sigma |_ a)"
        using erase_annotate_term[of A "erase_adp_term r \<cdot> sigma"]
          erase_adp_term_subt_at[OF a_poss]
        by (cases "annotate_term A (erase_adp_term r \<cdot> sigma) |_ a")
           auto
    qed
    have a_A: "a \<in> A"
      using local_target sharp_positions_annotate_term[OF a_fun] by simp
    from a_A show thesis
      unfolding annotations
    proof
      assume root: "a \<in> (if at_sharp then sharp_positions r else {})"
      have sharp: at_sharp by (cases at_sharp) (use root in auto)
      have redex_sharp: "redex \<in> sharp_positions s" using at sharp by simp
      have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
          redex sigma (if at_sharp then sharp_positions r else {}) phi
          redex q'"
        unfolding q' by (rule origin_edge.root_target[OF root])
      show thesis by (rule that[OF redex_sharp canonical[OF edge]])
    next
      assume transported: "a \<in>
        transported_annotations phi l (s |_ redex)"
      then obtain rho alpha beta where
          a: "a = alpha @ beta"
        and rho: "rho \<in> var_poss l"
        and phi: "phi rho = Some alpha"
        and source_local: "rho @ beta \<in> sharp_positions (s |_ redex)"
        unfolding transported_annotations_def by blast
      have source: "redex @ rho @ beta \<in> sharp_positions s"
        using source_local
          sharp_positions_below_iff[OF redex_poss, of "rho @ beta"] by simp
      have target_fun:
        "alpha @ beta \<in> fun_poss (erase_adp_term r \<cdot> sigma)"
        using a_fun a by simp
      have rho_erased: "rho \<in> var_poss (erase_adp_term l)"
        using rho var_poss_erase_adp_term by simp
      have edge0: "origin_edge (erase_adp_term l) (erase_adp_term r)
          redex sigma (if at_sharp then sharp_positions r else {}) phi
          (redex @ rho @ beta) (redex @ alpha @ beta)"
        by (rule origin_edge.variable_transport[
              where rho = rho and l = "erase_adp_term l" and phi = phi
                and alpha = alpha and beta = beta
                and r = "erase_adp_term r" and sigma = sigma and p = redex
                and A = "if at_sharp then sharp_positions r else {}"])
           (rule rho_erased, rule phi, rule target_fun)
      have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
          redex sigma (if at_sharp then sharp_positions r else {}) phi
          (redex @ rho @ beta) q'"
        using edge0 unfolding q' a .
      show thesis by (rule that[OF source canonical[OF edge]])
    qed
  next
    case above
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF redex_poss]
      unfolding target_term by (simp add: above)
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        redex sigma (if at_sharp then sharp_positions r else {}) phi q' q'"
      by (rule origin_edge.preserved) (rule disjI1[OF above])
    show thesis by (rule that[OF source canonical[OF edge]])
  next
    case parallel
    have outside: "q' \<bottom> redex" by (rule parallel_pos_sym[OF parallel])
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF redex_poss]
      unfolding target_term by (simp add: outside)
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        redex sigma (if at_sharp then sharp_positions r else {}) phi q' q'"
      by (rule origin_edge.preserved) (rule disjI2[OF outside])
    show thesis by (rule that[OF source canonical[OF edge]])
  qed
qed

definition relative_adp_chain_origin_edge ::
  "('f, 'v) adp set \<Rightarrow> (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<times> pos) rel" where
  "relative_adp_chain_origin_edge A terms =
    {((i,q),(j,q')). j = Suc i \<and> q \<in> sharp_positions (terms i) \<and>
      (\<exists>at_sharp pair redex. relative_adp_canonical_origin_edge
        A at_sharp (terms i) (terms j) pair redex q q')}"

definition relative_adp_chain_main_event ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow> nat \<times> pos \<Rightarrow> bool" where
  "relative_adp_chain_main_event P A terms node \<longleftrightarrow>
    (case node of (i,q) \<Rightarrow> \<exists>pair \<in> P.
      relative_adp_applied_at A True (terms i) (terms (Suc i)) pair q)"

lemma finite_relative_adp_chain_origin_successors:
  "finite {target. (source,target) \<in>
    relative_adp_chain_origin_edge A terms}"
proof (cases source)
  case (Pair i q)
  have subset: "{target. (source,target) \<in>
      relative_adp_chain_origin_edge A terms} \<subseteq>
      (\<lambda>q'. (Suc i,q')) ` sharp_positions (terms (Suc i))"
  proof
    fix target
    assume edge: "target \<in> {target. (source,target) \<in>
      relative_adp_chain_origin_edge A terms}"
    then obtain q' at_sharp pair redex where target: "target = (Suc i,q')"
      and source_sharp: "q \<in> sharp_positions (terms i)"
      and origin: "relative_adp_canonical_origin_edge A at_sharp
        (terms i) (terms (Suc i)) pair redex q q'"
      unfolding Pair relative_adp_chain_origin_edge_def by auto
    have "q' \<in> sharp_positions (terms (Suc i))"
      by (rule relative_adp_canonical_origin_edge_preserves_sharp[
          OF origin source_sharp])
    then show "target \<in>
      (\<lambda>q'. (Suc i,q')) ` sharp_positions (terms (Suc i))"
      unfolding target by blast
  qed
  have "finite ((\<lambda>q'. (Suc i,q')) ` sharp_positions (terms (Suc i)))"
    unfolding sharp_positions_def
    by (rule finite_imageI, rule finite_subset[OF _ finite_poss]) auto
  then show ?thesis by (rule finite_subset[OF subset])
qed

lemma relative_adp_chain_target_has_predecessor:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and target: "q' \<in> sharp_positions (terms (Suc i))"
  obtains q where
    "((i,q),(Suc i,q')) \<in> relative_adp_chain_origin_edge A terms"
proof -
  from step obtain at_sharp where
    case_step: "adp_step_case A at_sharp (terms i) (terms (Suc i))"
    unfolding adp_step_def adp_step_case_rel_def by blast
  from adp_step_sharp_position_has_labeled_predecessor[
      OF case_step target]
  obtain pair redex q where source: "q \<in> sharp_positions (terms i)"
    and edge: "relative_adp_canonical_origin_edge A at_sharp
      (terms i) (terms (Suc i)) pair redex q q'" by blast
  obtain l r where pair: "pair = (l,r)" by (cases pair) auto
  show thesis
    by (rule that[where q = q])
       (use source edge pair in
        \<open>auto simp: relative_adp_chain_origin_edge_def\<close>)
qed

lemma relative_adp_chain_marker_reachable_from_root:
  assumes steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and marked: "q \<in> sharp_positions (terms i)"
  shows "\<exists>root. root \<in> sharp_positions (terms 0) \<and>
    ((0,root),(i,q)) \<in> (relative_adp_chain_origin_edge A terms)\<^sup>*"
  using marked
proof (induction i arbitrary: q)
  case 0
  then show ?case by auto
next
  case (Suc i)
  from relative_adp_chain_target_has_predecessor[
      OF steps Suc.prems]
  obtain predecessor where edge:
    "((i,predecessor),(Suc i,q)) \<in>
      relative_adp_chain_origin_edge A terms" .
  then have predecessor_marked:
      "predecessor \<in> sharp_positions (terms i)"
    unfolding relative_adp_chain_origin_edge_def by auto
  from Suc.IH[OF predecessor_marked]
  obtain root where root: "root \<in> sharp_positions (terms 0)"
    and path: "((0,root),(i,predecessor)) \<in>
      (relative_adp_chain_origin_edge A terms)\<^sup>*" by blast
  have "((0,root),(Suc i,q)) \<in>
      (relative_adp_chain_origin_edge A terms)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF path edge])
  with root show ?case by blast
qed

lemma relative_adp_applied_at_mono:
  assumes applied: "relative_adp_applied_at P at_sharp s t pair p"
    and subset: "P \<subseteq> A"
  shows "relative_adp_applied_at A at_sharp s t pair p"
  using applied subset
  unfolding relative_adp_applied_at_def by blast

lemma relative_adp_ideriv_chain_steps:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  shows "(terms i, terms (Suc i)) \<in> adp_step A"
proof -
  have main: "adp_step_case_rel P True \<subseteq> adp_step A"
    using adp_step_case_rel_subset_adp_step[of P True]
      adp_step_mono[OF subset] by blast
  show ?thesis using deriv main unfolding ideriv_def by blast
qed

lemma relative_adp_strict_step_has_main_event:
  assumes strict: "(terms i, terms (Suc i)) \<in>
      adp_step_case_rel P True"
    and subset: "P \<subseteq> A"
  obtains q where "relative_adp_chain_main_event P A terms (i,q)"
proof -
  from strict have case_step:
      "adp_step_case P True (terms i) (terms (Suc i))"
    unfolding adp_step_case_rel_def by simp
  from adp_step_case_has_applied_witness[OF case_step]
  obtain pair q where applied:
      "relative_adp_applied_at P True
        (terms i) (terms (Suc i)) pair q" .
  have applied_A: "relative_adp_applied_at A True
      (terms i) (terms (Suc i)) pair q"
    by (rule relative_adp_applied_at_mono[OF applied subset])
  have pair: "pair \<in> P"
    using applied unfolding relative_adp_applied_at_def by blast
  have event: "relative_adp_chain_main_event P A terms (i,q)"
    unfolding relative_adp_chain_main_event_def
    using pair applied_A by blast
  show thesis by (rule that[OF event])
qed

lemma relative_adp_ideriv_infinite_main_events:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  shows "infinite {node. relative_adp_chain_main_event P A terms node}"
proof -
  let ?I = "{i. (terms i, terms (Suc i)) \<in>
    adp_step_case_rel P True}"
  let ?events = "{node. relative_adp_chain_main_event P A terms node}"
  have infinite_I: "infinite ?I"
    using deriv unfolding ideriv_def INFM_iff_infinite by simp
  have projection: "?I \<subseteq> fst ` ?events"
  proof
    fix i
    assume "i \<in> ?I"
    then have strict: "(terms i, terms (Suc i)) \<in>
      adp_step_case_rel P True" by simp
    from relative_adp_strict_step_has_main_event[OF strict subset]
    obtain q where event:
      "relative_adp_chain_main_event P A terms (i,q)" .
    then show "i \<in> fst ` ?events" by force
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> infinite ?events"
    then have "finite (fst ` ?events)" by simp
    then have "finite ?I" by (rule finite_subset[OF projection])
    with infinite_I show False by contradiction
  qed
qed

lemma relative_adp_main_event_is_marked:
  assumes event: "relative_adp_chain_main_event P A terms (i,q)"
  shows "q \<in> sharp_positions (terms i)"
  using event unfolding relative_adp_chain_main_event_def
    relative_adp_applied_at_def by auto

lemma relative_adp_ideriv_has_heavy_root:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  obtains root where
    "root \<in> sharp_positions (terms 0)"
    "heavy_node (relative_adp_chain_origin_edge A terms)
      (relative_adp_chain_main_event P A terms) (0,root)"
proof -
  let ?E = "relative_adp_chain_origin_edge A terms"
  let ?event = "relative_adp_chain_main_event P A terms"
  let ?events = "{node. ?event node}"
  let ?roots = "sharp_positions (terms 0)"
  have steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    by (rule relative_adp_ideriv_chain_steps[OF deriv subset])
  have infinite_events: "infinite ?events"
    by (rule relative_adp_ideriv_infinite_main_events[OF deriv subset])
  have finite_roots: "finite ?roots"
    unfolding sharp_positions_def
    by (rule finite_subset[OF _ finite_poss]) auto
  have cover: "?events \<subseteq>
      \<Union>(reachable_events ?E ?event ` ((\<lambda>q. (0,q)) ` ?roots))"
  proof
    fix node
    assume node: "node \<in> ?events"
    obtain i q where node_eq: "node = (i,q)" by (cases node) auto
    have event: "?event (i,q)" using node unfolding node_eq by simp
    have marked: "q \<in> sharp_positions (terms i)"
      by (rule relative_adp_main_event_is_marked[OF event])
    from relative_adp_chain_marker_reachable_from_root[OF steps marked]
    obtain root where root: "root \<in> ?roots"
      and path: "((0,root),(i,q)) \<in> ?E\<^sup>*" by blast
    have "node \<in> reachable_events ?E ?event (0,root)"
      using node path unfolding node_eq reachable_events_def by simp
    with root show "node \<in>
        \<Union>(reachable_events ?E ?event ` ((\<lambda>q. (0,q)) ` ?roots))"
      by blast
  qed
  have heavy_root: "\<exists>root \<in> ?roots.
      heavy_node ?E ?event (0,root)"
  proof (rule ccontr)
    assume none: "\<not> (\<exists>root \<in> ?roots.
      heavy_node ?E ?event (0,root))"
    have finite_each: "\<And>root. root \<in> ?roots \<Longrightarrow>
        finite (reachable_events ?E ?event (0,root))"
      using none unfolding heavy_node_def by blast
    have finite_union:
        "finite (\<Union>(reachable_events ?E ?event `
          ((\<lambda>q. (0,q)) ` ?roots)))"
      using finite_roots finite_each by simp
    have "finite ?events" by (rule finite_subset[OF cover finite_union])
    with infinite_events show False by contradiction
  qed
  from heavy_root obtain root where root: "root \<in> ?roots"
    and heavy: "heavy_node ?E ?event (0,root)" by blast
  show thesis by (rule that[OF root heavy])
qed

theorem relative_adp_ideriv_origin_dichotomy:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  obtains root path where
    "root \<in> sharp_positions (terms 0)"
    "\<forall>n. (path n, path (Suc n)) \<in>
      relative_adp_chain_origin_edge A terms"
    "(INFM n. relative_adp_chain_main_event P A terms (path n)) \<or>
      (INFM n. event_offshoot (relative_adp_chain_origin_edge A terms)
        (relative_adp_chain_main_event P A terms) path n)"
proof -
  let ?E = "relative_adp_chain_origin_edge A terms"
  let ?event = "relative_adp_chain_main_event P A terms"
  from relative_adp_ideriv_has_heavy_root[OF deriv subset]
  obtain root where root: "root \<in> sharp_positions (terms 0)"
    and heavy: "heavy_node ?E ?event (0,root)" .
  let ?path = "heavy_path ?E ?event (0,root)"
  from finite_branching_event_dichotomy[OF heavy]
  have dichotomy: "(\<forall>n. (?path n, ?path (Suc n)) \<in> ?E) \<and>
      ((INFM n. ?event (?path n)) \<or>
        (INFM n. event_offshoot ?E ?event ?path n))"
    by (simp add: finite_relative_adp_chain_origin_successors)
  show thesis
    apply (rule that[where path = ?path, OF root])
    using dichotomy apply blast
    using dichotomy apply blast
    done
qed

record ('f, 'v) relative_adp_step_witness =
  radp_witness_at_sharp :: bool
  radp_witness_pair :: "('f, 'v) adp"
  radp_witness_redex :: pos
  radp_witness_vrf :: "pos \<Rightarrow> pos option"
  radp_witness_subst :: "'v \<Rightarrow> ('f, 'v) term"
  radp_witness_annotations :: "pos set"

definition relative_adp_step_witness_valid ::
  "('f, 'v) adp set \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow>
    ('f, 'v) relative_adp_step_witness \<Rightarrow> bool" where
  "relative_adp_step_witness_valid A s t witness \<longleftrightarrow>
    (\<exists>l r.
      radp_witness_pair witness = (l,r) \<and> (l,r) \<in> A \<and>
      plain_adp_term_pred l \<and>
      valid_vrf (l,r) (radp_witness_vrf witness) \<and>
      radp_witness_redex witness \<in> fun_poss s \<and>
      radp_witness_at_sharp witness =
        (radp_witness_redex witness \<in> sharp_positions s) \<and>
      erase_adp_term (s |_ radp_witness_redex witness) =
        erase_adp_term l \<cdot> radp_witness_subst witness \<and>
      radp_witness_annotations witness =
        (if radp_witness_at_sharp witness then sharp_positions r else {}) \<union>
          transported_annotations (radp_witness_vrf witness) l
            (s |_ radp_witness_redex witness) \<and>
      t = replace_at s (radp_witness_redex witness)
        (annotate_term (radp_witness_annotations witness)
          (erase_adp_term r \<cdot> radp_witness_subst witness)))"

definition relative_adp_preferred_step_witness_valid ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f, 'v) relative_adp_step_witness \<Rightarrow> bool" where
  "relative_adp_preferred_step_witness_valid P A s t witness \<longleftrightarrow>
    relative_adp_step_witness_valid A s t witness \<and>
    ((s,t) \<in> adp_step_case_rel P True \<longrightarrow>
      radp_witness_at_sharp witness \<and> radp_witness_pair witness \<in> P)"

definition relative_adp_selected_step_witness ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow> nat \<Rightarrow>
    ('f, 'v) relative_adp_step_witness" where
  "relative_adp_selected_step_witness P A terms i =
    (SOME witness. relative_adp_preferred_step_witness_valid P A
      (terms i) (terms (Suc i)) witness)"

type_synonym ('f, 'v) relative_adp_application =
  "bool \<times> (('f, 'v) adp \<times> pos)"

definition relative_adp_application_valid ::
  "('f, 'v) adp set \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow>
    ('f, 'v) relative_adp_application \<Rightarrow> bool" where
  "relative_adp_application_valid A s t application \<longleftrightarrow>
    relative_adp_applied_at A (fst application) s t
      (fst (snd application)) (snd (snd application))"

definition relative_adp_preferred_application_valid ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow>
    ('f, 'v) relative_adp_application \<Rightarrow> bool" where
  "relative_adp_preferred_application_valid P A s t application \<longleftrightarrow>
    relative_adp_application_valid A s t application \<and>
    ((s,t) \<in> adp_step_case_rel P True \<longrightarrow>
      fst application \<and> fst (snd application) \<in> P)"

definition relative_adp_selected_application ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    nat \<Rightarrow> ('f, 'v) relative_adp_application" where
  "relative_adp_selected_application P A terms i = (let
      witness = relative_adp_selected_step_witness P A terms i
    in (radp_witness_at_sharp witness,
      (radp_witness_pair witness, radp_witness_redex witness)))"

lemma adp_step_has_valid_application:
  assumes step: "(s,t) \<in> adp_step A"
  shows "\<exists>application. relative_adp_application_valid A s t application"
proof -
  from step obtain at_sharp where case_step: "adp_step_case A at_sharp s t"
    unfolding adp_step_def adp_step_case_rel_def by blast
  from adp_step_case_has_applied_witness[OF case_step]
  obtain pair redex where applied:
    "relative_adp_applied_at A at_sharp s t pair redex" .
  show ?thesis
    by (rule exI[of _ "(at_sharp,(pair,redex))"])
       (use applied in
        \<open>simp add: relative_adp_application_valid_def\<close>)
qed

lemma adp_step_has_preferred_application:
  assumes step: "(s,t) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "\<exists>application.
    relative_adp_preferred_application_valid P A s t application"
proof (cases "(s,t) \<in> adp_step_case_rel P True")
  case True
  then have case_step: "adp_step_case P True s t"
    unfolding adp_step_case_rel_def by simp
  from adp_step_case_has_applied_witness[OF case_step]
  obtain pair redex where applied_P:
    "relative_adp_applied_at P True s t pair redex" .
  have applied_A: "relative_adp_applied_at A True s t pair redex"
    by (rule relative_adp_applied_at_mono[OF applied_P subset])
  have pair: "pair \<in> P"
    using applied_P unfolding relative_adp_applied_at_def by blast
  show ?thesis
    by (rule exI[of _ "(True,(pair,redex))"])
       (use True applied_A pair in
        \<open>simp add: relative_adp_preferred_application_valid_def
          relative_adp_application_valid_def\<close>)
next
  case False
  from adp_step_has_valid_application[OF step]
  obtain application where valid:
    "relative_adp_application_valid A s t application" by blast
  show ?thesis
    by (rule exI[of _ application])
       (use False valid in
        \<open>simp add: relative_adp_preferred_application_valid_def\<close>)
qed

lemma adp_step_case_has_valid_step_witness:
  assumes step: "adp_step_case A at_sharp s t"
  obtains witness where
    "relative_adp_step_witness_valid A s t witness"
    "radp_witness_at_sharp witness = at_sharp"
proof -
  from step show thesis
  proof cases
    case (adp_stepI l r phi p sigma annotations)
    let ?witness = "\<lparr>
      radp_witness_at_sharp = at_sharp,
      radp_witness_pair = (l,r),
      radp_witness_redex = p,
      radp_witness_vrf = phi,
      radp_witness_subst = sigma,
      radp_witness_annotations = annotations \<rparr>"
    show thesis
      by (rule that[of ?witness])
         (use adp_stepI in
          \<open>auto simp: relative_adp_step_witness_valid_def\<close>)
  qed
qed

lemma relative_adp_step_witness_valid_mono:
  assumes valid: "relative_adp_step_witness_valid P s t witness"
    and subset: "P \<subseteq> A"
  shows "relative_adp_step_witness_valid A s t witness"
  using valid subset unfolding relative_adp_step_witness_valid_def by blast

lemma adp_step_has_valid_step_witness:
  assumes step: "(s,t) \<in> adp_step A"
  shows "\<exists>witness. relative_adp_step_witness_valid A s t witness"
proof -
  from step obtain at_sharp where case_step: "adp_step_case A at_sharp s t"
    unfolding adp_step_def adp_step_case_rel_def by blast
  from adp_step_case_has_valid_step_witness[OF case_step]
  obtain witness where "relative_adp_step_witness_valid A s t witness" .
  then show ?thesis by blast
qed

lemma adp_step_has_preferred_step_witness:
  assumes step: "(s,t) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "\<exists>witness.
    relative_adp_preferred_step_witness_valid P A s t witness"
proof (cases "(s,t) \<in> adp_step_case_rel P True")
  case True
  then have case_step: "adp_step_case P True s t"
    unfolding adp_step_case_rel_def by simp
  from adp_step_case_has_valid_step_witness[OF case_step]
  obtain witness where valid_P:
      "relative_adp_step_witness_valid P s t witness"
    and sharp: "radp_witness_at_sharp witness = True" .
  from valid_P have pair: "radp_witness_pair witness \<in> P"
    unfolding relative_adp_step_witness_valid_def by auto
  have valid_A: "relative_adp_step_witness_valid A s t witness"
    by (rule relative_adp_step_witness_valid_mono[OF valid_P subset])
  show ?thesis
    by (rule exI[of _ witness])
       (use True valid_A sharp pair in
        \<open>simp add: relative_adp_preferred_step_witness_valid_def\<close>)
next
  case False
  from adp_step_has_valid_step_witness[OF step]
  obtain witness where valid:
      "relative_adp_step_witness_valid A s t witness" by blast
  show ?thesis
    by (rule exI[of _ witness])
       (use False valid in
        \<open>simp add: relative_adp_preferred_step_witness_valid_def\<close>)
qed

lemma relative_adp_selected_step_witness_valid:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "relative_adp_preferred_step_witness_valid P A
    (terms i) (terms (Suc i))
    (relative_adp_selected_step_witness P A terms i)"
  unfolding relative_adp_selected_step_witness_def
  by (rule someI_ex,
      rule adp_step_has_preferred_step_witness[OF step subset])

lemma relative_adp_selected_application_valid:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "relative_adp_preferred_application_valid P A
    (terms i) (terms (Suc i))
    (relative_adp_selected_application P A terms i)"
proof -
  let ?witness = "relative_adp_selected_step_witness P A terms i"
  have preferred: "relative_adp_preferred_step_witness_valid P A
      (terms i) (terms (Suc i)) ?witness"
    by (rule relative_adp_selected_step_witness_valid[OF step subset])
  then have valid: "relative_adp_step_witness_valid A
      (terms i) (terms (Suc i)) ?witness"
    and strict: "(terms i, terms (Suc i)) \<in> adp_step_case_rel P True \<longrightarrow>
      radp_witness_at_sharp ?witness \<and> radp_witness_pair ?witness \<in> P"
    unfolding relative_adp_preferred_step_witness_valid_def by auto
  from valid have applied:
      "relative_adp_applied_at A (radp_witness_at_sharp ?witness)
        (terms i) (terms (Suc i)) (radp_witness_pair ?witness)
        (radp_witness_redex ?witness)"
    unfolding relative_adp_step_witness_valid_def
      relative_adp_applied_at_def by blast
  show ?thesis
    unfolding relative_adp_preferred_application_valid_def
      relative_adp_application_valid_def
      relative_adp_selected_application_def Let_def
    using applied strict by simp
qed

definition relative_adp_step_witness_origin_edge ::
  "('f, 'v) relative_adp_step_witness \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool" where
  "relative_adp_step_witness_origin_edge witness q q' \<longleftrightarrow>
    (\<exists>l r. radp_witness_pair witness = (l,r) \<and>
      origin_edge (erase_adp_term l) (erase_adp_term r)
        (radp_witness_redex witness) (radp_witness_subst witness)
        (if radp_witness_at_sharp witness then sharp_positions r else {})
        (radp_witness_vrf witness) q q')"

lemma relative_adp_step_witness_origin_is_canonical:
  assumes valid: "relative_adp_step_witness_valid A s t witness"
    and origin: "relative_adp_step_witness_origin_edge witness q q'"
  shows "relative_adp_canonical_origin_edge A
    (radp_witness_at_sharp witness) s t (radp_witness_pair witness)
    (radp_witness_redex witness) q q'"
proof -
  from valid obtain l r where
      pair: "radp_witness_pair witness = (l,r)"
    and rule: "(l,r) \<in> A"
    and plain: "plain_adp_term_pred l"
    and vrf: "valid_vrf (l,r) (radp_witness_vrf witness)"
    and redex: "radp_witness_redex witness \<in> fun_poss s"
    and sharp: "radp_witness_at_sharp witness =
      (radp_witness_redex witness \<in> sharp_positions s)"
    and lhs: "erase_adp_term (s |_ radp_witness_redex witness) =
      erase_adp_term l \<cdot> radp_witness_subst witness"
    and annotations: "radp_witness_annotations witness =
      (if radp_witness_at_sharp witness then sharp_positions r else {}) \<union>
        transported_annotations (radp_witness_vrf witness) l
          (s |_ radp_witness_redex witness)"
    and target: "t = replace_at s (radp_witness_redex witness)
      (annotate_term (radp_witness_annotations witness)
        (erase_adp_term r \<cdot> radp_witness_subst witness))"
    unfolding relative_adp_step_witness_valid_def by blast
  from origin pair have edge:
      "origin_edge (erase_adp_term l) (erase_adp_term r)
        (radp_witness_redex witness) (radp_witness_subst witness)
        (if radp_witness_at_sharp witness then sharp_positions r else {})
        (radp_witness_vrf witness) q q'"
    unfolding relative_adp_step_witness_origin_edge_def by auto
  show ?thesis
    unfolding relative_adp_canonical_origin_edge_def
    by (rule exI[of _ l], rule exI[of _ r],
        rule exI[of _ "radp_witness_vrf witness"],
        rule exI[of _ "radp_witness_subst witness"],
        rule exI[of _ "radp_witness_annotations witness"])
       (use pair rule plain vrf redex sharp lhs annotations target edge in auto)
qed

lemma relative_adp_step_witness_sharp_position_has_predecessor:
  assumes valid: "relative_adp_step_witness_valid A s t witness"
    and target: "q' \<in> sharp_positions t"
  obtains q where
    "q \<in> sharp_positions s"
    "relative_adp_step_witness_origin_edge witness q q'"
proof -
  from valid obtain l r where
      pair: "radp_witness_pair witness = (l,r)"
    and redex_fun: "radp_witness_redex witness \<in> fun_poss s"
    and at: "radp_witness_at_sharp witness =
      (radp_witness_redex witness \<in> sharp_positions s)"
    and annotations: "radp_witness_annotations witness =
      (if radp_witness_at_sharp witness then sharp_positions r else {}) \<union>
        transported_annotations (radp_witness_vrf witness) l
          (s |_ radp_witness_redex witness)"
    and target_term: "t = replace_at s (radp_witness_redex witness)
      (annotate_term (radp_witness_annotations witness)
        (erase_adp_term r \<cdot> radp_witness_subst witness))"
    unfolding relative_adp_step_witness_valid_def by blast
  let ?p = "radp_witness_redex witness"
  let ?at = "radp_witness_at_sharp witness"
  let ?phi = "radp_witness_vrf witness"
  let ?sigma = "radp_witness_subst witness"
  let ?annotations = "radp_witness_annotations witness"
  have p_poss: "?p \<in> poss s" by (rule fun_poss_imp_poss[OF redex_fun])
  have exact:
    "\<And>q. origin_edge (erase_adp_term l) (erase_adp_term r) ?p ?sigma
        (if ?at then sharp_positions r else {}) ?phi q q' \<Longrightarrow>
      relative_adp_step_witness_origin_edge witness q q'"
    unfolding relative_adp_step_witness_origin_edge_def
    using pair by auto
  from pos_cases[of ?p q']
  consider (below) "?p \<le>\<^sub>p q'"
    | (above) "q' <\<^sub>p ?p"
    | (parallel) "?p \<bottom> q'"
    by blast
  then show thesis
  proof cases
    case below
    from prefixE[OF below] obtain a where q': "q' = ?p @ a" by blast
    have p_after: "?p \<in> poss t"
      unfolding target_term
      by (rule replace_at_below_poss[OF p_poss]) simp
    have local_target:
      "a \<in> sharp_positions
        (annotate_term ?annotations (erase_adp_term r \<cdot> ?sigma))"
      using target sharp_positions_below_iff[OF p_after, of a]
        replace_at_subt_at[OF p_poss]
      unfolding target_term q' by simp
    from local_target have a_poss:
      "a \<in> poss (annotate_term ?annotations
        (erase_adp_term r \<cdot> ?sigma))"
      unfolding sharp_positions_def by auto
    have a_erased_poss: "a \<in> poss (erase_adp_term r \<cdot> ?sigma)"
      using a_poss poss_annotate_term_at[of ?annotations "[]"
        "erase_adp_term r \<cdot> ?sigma"]
      unfolding annotate_term_def by simp
    from local_target obtain f n where a_root:
      "root (annotate_term ?annotations
        (erase_adp_term r \<cdot> ?sigma) |_ a) = Some (f,n)"
      unfolding sharp_positions_def
      by (auto split: option.splits prod.splits)
    have a_fun: "a \<in> fun_poss (erase_adp_term r \<cdot> ?sigma)"
    proof (rule poss_is_Fun_fun_poss[OF a_erased_poss])
      from a_root show "is_Fun (erase_adp_term r \<cdot> ?sigma |_ a)"
        using erase_annotate_term[of ?annotations
          "erase_adp_term r \<cdot> ?sigma"]
          erase_adp_term_subt_at[OF a_poss]
        by (cases "annotate_term ?annotations
          (erase_adp_term r \<cdot> ?sigma) |_ a") auto
    qed
    have a_annotations: "a \<in> ?annotations"
      using local_target sharp_positions_annotate_term[OF a_fun] by simp
    from a_annotations show thesis
      unfolding annotations
    proof
      assume root: "a \<in> (if ?at then sharp_positions r else {})"
      have sharp: ?at by (cases ?at) (use root in auto)
      have p_sharp: "?p \<in> sharp_positions s" using at sharp by simp
      have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
          ?p ?sigma (if ?at then sharp_positions r else {}) ?phi ?p q'"
        unfolding q' by (rule origin_edge.root_target[OF root])
      show thesis by (rule that[OF p_sharp exact[OF edge]])
    next
      assume transported: "a \<in>
        transported_annotations ?phi l (s |_ ?p)"
      then obtain rho alpha beta where
          a: "a = alpha @ beta"
        and rho: "rho \<in> var_poss l"
        and phi: "?phi rho = Some alpha"
        and source_local: "rho @ beta \<in> sharp_positions (s |_ ?p)"
        unfolding transported_annotations_def by blast
      have source: "?p @ rho @ beta \<in> sharp_positions s"
        using source_local sharp_positions_below_iff[OF p_poss, of "rho @ beta"]
        by simp
      have target_fun:
        "alpha @ beta \<in> fun_poss (erase_adp_term r \<cdot> ?sigma)"
        using a_fun a by simp
      have rho_erased: "rho \<in> var_poss (erase_adp_term l)"
        using rho var_poss_erase_adp_term by simp
      have edge0: "origin_edge (erase_adp_term l) (erase_adp_term r)
          ?p ?sigma (if ?at then sharp_positions r else {}) ?phi
          (?p @ rho @ beta) (?p @ alpha @ beta)"
        by (rule origin_edge.variable_transport[
              where rho = rho and l = "erase_adp_term l" and phi = ?phi
                and alpha = alpha and beta = beta
                and r = "erase_adp_term r" and sigma = ?sigma and p = ?p
                and A = "if ?at then sharp_positions r else {}"])
           (rule rho_erased, rule phi, rule target_fun)
      have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
          ?p ?sigma (if ?at then sharp_positions r else {}) ?phi
          (?p @ rho @ beta) q'"
        using edge0 unfolding q' a .
      show thesis by (rule that[OF source exact[OF edge]])
    qed
  next
    case above
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF p_poss]
      unfolding target_term by (simp add: above)
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        ?p ?sigma (if ?at then sharp_positions r else {}) ?phi q' q'"
      by (rule origin_edge.preserved) (rule disjI1[OF above])
    show thesis by (rule that[OF source exact[OF edge]])
  next
    case parallel
    have outside: "q' \<bottom> ?p" by (rule parallel_pos_sym[OF parallel])
    have source: "q' \<in> sharp_positions s"
      using target sharp_positions_replace_outside_iff[OF p_poss]
      unfolding target_term by (simp add: outside)
    have edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
        ?p ?sigma (if ?at then sharp_positions r else {}) ?phi q' q'"
      by (rule origin_edge.preserved) (rule disjI2[OF outside])
    show thesis by (rule that[OF source exact[OF edge]])
  qed
qed

definition relative_adp_selected_chain_origin_edge ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow> (nat \<times> pos) rel" where
  "relative_adp_selected_chain_origin_edge P A terms =
    {((i,q),(j,q')). j = Suc i \<and> q \<in> sharp_positions (terms i) \<and>
      (let witness = relative_adp_selected_step_witness P A terms i;
           application = relative_adp_selected_application P A terms i in
       relative_adp_canonical_origin_edge A (fst application)
        (terms i) (terms j) (fst (snd application))
        (snd (snd application)) q q' \<and>
       relative_adp_step_witness_origin_edge witness q q')}"

definition relative_adp_selected_chain_main_event ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow> nat \<times> pos \<Rightarrow> bool" where
  "relative_adp_selected_chain_main_event P A terms node \<longleftrightarrow>
    (case node of (i,q) \<Rightarrow>
      let application = relative_adp_selected_application P A terms i in
      fst application \<and> fst (snd application) \<in> P \<and>
      snd (snd application) = q)"

definition relative_adp_selected_chain_label ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    nat \<times> pos \<Rightarrow> ('f, 'v) adp \<Rightarrow> bool" where
  "relative_adp_selected_chain_label P A terms node pair \<longleftrightarrow>
    (case node of (i,q) \<Rightarrow>
      let application = relative_adp_selected_application P A terms i in
      fst application \<and> fst (snd application) = pair \<and>
      snd (snd application) = q)"

definition relative_adp_selected_chain_labeled ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    nat \<times> pos \<Rightarrow> bool" where
  "relative_adp_selected_chain_labeled P A terms node \<longleftrightarrow>
    (\<exists>pair. relative_adp_selected_chain_label P A terms node pair)"

definition relative_adp_selected_chain_node_label ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    nat \<times> pos \<Rightarrow> ('f, 'v) adp" where
  "relative_adp_selected_chain_node_label P A terms node =
    (case node of (i,_) \<Rightarrow>
      fst (snd (relative_adp_selected_application P A terms i)))"

definition relative_adp_selected_label_indices ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat set" where
  "relative_adp_selected_label_indices P A terms path =
    {n. relative_adp_selected_chain_labeled P A terms (path n)}"

definition relative_adp_selected_label_stream ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow>
    (nat \<Rightarrow> nat \<times> pos) \<Rightarrow> nat \<Rightarrow> ('f, 'v) adp" where
  "relative_adp_selected_label_stream P A terms path n =
    relative_adp_selected_chain_node_label P A terms
      (path (enumerate (relative_adp_selected_label_indices P A terms path) n))"

lemma relative_adp_selected_chain_labeled_iff:
  "relative_adp_selected_chain_labeled P A terms (i,q) \<longleftrightarrow>
    (let application = relative_adp_selected_application P A terms i in
      fst application \<and> snd (snd application) = q)"
  unfolding relative_adp_selected_chain_labeled_def
    relative_adp_selected_chain_label_def
  by (auto simp: Let_def)

lemma relative_adp_selected_chain_labeled_has_node_label:
  assumes "relative_adp_selected_chain_labeled P A terms node"
  shows "relative_adp_selected_chain_label P A terms node
    (relative_adp_selected_chain_node_label P A terms node)"
  using assms
  unfolding relative_adp_selected_chain_labeled_def
    relative_adp_selected_chain_label_def
    relative_adp_selected_chain_node_label_def
  by (cases node) (auto simp: Let_def)

lemma relative_adp_selected_chain_main_event_iff_node_label:
  "relative_adp_selected_chain_main_event P A terms node \<longleftrightarrow>
    relative_adp_selected_chain_labeled P A terms node \<and>
    relative_adp_selected_chain_node_label P A terms node \<in> P"
  unfolding relative_adp_selected_chain_main_event_def
    relative_adp_selected_chain_labeled_def
    relative_adp_selected_chain_label_def
    relative_adp_selected_chain_node_label_def
  by (cases node) (auto simp: Let_def)

lemma relative_adp_selected_main_event_has_label:
  assumes "relative_adp_selected_chain_main_event P A terms node"
  shows "\<exists>pair \<in> P.
    relative_adp_selected_chain_label P A terms node pair"
  using assms unfolding relative_adp_selected_chain_main_event_def
    relative_adp_selected_chain_label_def
  by (cases node) (auto simp: Let_def)

lemma relative_adp_selected_unlabeled_edge_not_at_redex:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and unlabeled: "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
  shows "snd (snd (relative_adp_selected_application P A terms i)) \<noteq> q"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  from edge have marked: "q \<in> sharp_positions (terms i)"
    unfolding relative_adp_selected_chain_origin_edge_def by auto
  have preferred: "relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i)) ?application"
    by (rule relative_adp_selected_application_valid[OF step subset])
  then have applied: "relative_adp_applied_at A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application))"
    unfolding relative_adp_preferred_application_valid_def
      relative_adp_application_valid_def by simp
  from applied have at:
      "fst ?application =
        (snd (snd ?application) \<in> sharp_positions (terms i))"
    unfolding relative_adp_applied_at_def by blast
  show ?thesis
  proof
    assume "snd (snd ?application) = q"
    with marked at have "fst ?application" by simp
    with `snd (snd ?application) = q` have
      "relative_adp_selected_chain_labeled P A terms (i,q)"
      unfolding relative_adp_selected_chain_labeled_iff by (simp add: Let_def)
    with unlabeled show False by contradiction
  qed
qed

lemma relative_adp_selected_unlabeled_edge_shape:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and unlabeled: "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
  shows "q' = q \<or>
    (\<exists>redex rho alpha beta.
      q = redex @ rho @ beta \<and> q' = redex @ alpha @ beta)"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  from edge have origin: "relative_adp_canonical_origin_edge A
      (fst ?application) (terms i) (terms (Suc i))
      (fst (snd ?application)) (snd (snd ?application)) q q'"
    unfolding relative_adp_selected_chain_origin_edge_def by (auto simp: Let_def)
  from origin obtain l r phi sigma annotations where
    pair: "fst (snd ?application) = (l,r)"
    and origin_edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
      (snd (snd ?application)) sigma
      (if fst ?application then sharp_positions r else {}) phi q q'"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have not_redex: "snd (snd ?application) \<noteq> q"
    by (rule relative_adp_selected_unlabeled_edge_not_at_redex[
        OF edge step subset unlabeled])
  from origin_edge show ?thesis
  proof cases
    case preserved
    then show ?thesis by simp
  next
    case (root_target alpha)
    then have "snd (snd ?application) = q" by simp
    with not_redex show ?thesis by contradiction
  next
    case (variable_transport rho alpha beta)
    then show ?thesis by blast
  qed
qed

lemma relative_adp_canonical_origin_projection:
  assumes origin: "relative_adp_canonical_origin_edge A at_sharp s t
      pair redex q q'"
    and not_redex: "redex \<noteq> q"
  shows "(q' = q \<and> (q <\<^sub>p redex \<or> q \<bottom> redex)) \<or>
    erase_adp_term (s |_ q) = erase_adp_term (t |_ q')"
proof -
  from origin obtain l r phi sigma annotations where
      valid: "valid_vrf (l,r) phi"
    and redex_fun: "redex \<in> fun_poss s"
    and lhs: "erase_adp_term (s |_ redex) =
      erase_adp_term l \<cdot> sigma"
    and target: "t = replace_at s redex
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    and edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
      redex sigma (if at_sharp then sharp_positions r else {}) phi q q'"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have redex_poss: "redex \<in> poss s"
    by (rule fun_poss_imp_poss[OF redex_fun])
  from edge show ?thesis
  proof cases
    case preserved
    then show ?thesis by simp
  next
    case (root_target alpha)
    then have "redex = q" by simp
    with not_redex show ?thesis by contradiction
  next
    case (variable_transport rho alpha beta)
    show ?thesis
    proof (rule disjI2)
    have rho_var_erased: "rho \<in> var_poss (erase_adp_term l)"
      using variable_transport by auto
    have rho_var: "rho \<in> var_poss l"
      using rho_var_erased var_poss_erase_adp_term by simp
    have selected: "alpha \<in> var_poss r \<and> l |_ rho = r |_ alpha"
      using valid rho_var variable_transport
      unfolding valid_vrf_def by force
    from rho_var obtain x where rho_at: "l |_ rho = Var x"
      unfolding var_poss_iff by blast
    have alpha_at: "r |_ alpha = Var x" using selected rho_at by simp
    have rho_erased_at: "erase_adp_term l |_ rho = Var x"
      using erase_adp_term_subt_at[OF var_poss_imp_poss[OF rho_var]] rho_at
      by simp
    have alpha_erased_at: "erase_adp_term r |_ alpha = Var x"
      using erase_adp_term_subt_at[
          OF var_poss_imp_poss[OF selected[THEN conjunct1]]] alpha_at
      by simp
    have alpha_poss: "alpha \<in> poss (erase_adp_term r)"
      using selected[THEN conjunct1] var_poss_imp_poss
        poss_erase_adp_term by metis
    have target_fun: "alpha @ beta \<in>
        fun_poss (erase_adp_term r \<cdot> sigma)"
      using variable_transport by auto
    have target_poss: "alpha @ beta \<in>
        poss (erase_adp_term r \<cdot> sigma)"
      by (rule fun_poss_imp_poss[OF target_fun])
    have beta_poss: "beta \<in> poss (sigma x)"
    proof -
      have alpha_subst: "alpha \<in> poss (erase_adp_term r \<cdot> sigma)"
        using alpha_poss by simp
      have at_alpha: "(erase_adp_term r \<cdot> sigma) |_ alpha = sigma x"
        using subt_at_subst[OF alpha_poss, of sigma] alpha_erased_at by simp
      show ?thesis using target_poss alpha_subst at_alpha
        by (simp add: poss_append_poss)
    qed
    have erased_redex: "erase_adp_term s |_ redex =
        erase_adp_term l \<cdot> sigma"
      using erase_adp_term_subt_at[OF redex_poss] lhs by simp
    have redex_erased_poss: "redex \<in> poss (erase_adp_term s)"
      using redex_poss by simp
    have source_local: "erase_adp_term s |_
        (redex @ rho @ beta) = sigma x |_ beta"
      by (rule lhs_variable_subterm[
          OF redex_erased_poss
            erased_redex var_poss_imp_poss[OF rho_var_erased]
            rho_erased_at beta_poss])
    have target_local: "replace_at (erase_adp_term s) redex
      (erase_adp_term r \<cdot> sigma) |_
        (redex @ alpha @ beta) = sigma x |_ beta"
      by (rule replacement_variable_subterm[
            where p = redex and s = "erase_adp_term s"
              and r = "erase_adp_term r" and sigma = sigma
              and alpha = alpha and x = x and beta = beta])
         (rule redex_erased_poss, rule alpha_poss,
          rule alpha_erased_at, rule beta_poss)
    have erased_target: "erase_adp_term t =
        replace_at (erase_adp_term s) redex
          (erase_adp_term r \<cdot> sigma)"
      using redex_poss unfolding target by simp
    have source_q: "q = redex @ rho @ beta"
      using variable_transport by simp
    have target_q: "q' = redex @ alpha @ beta"
      using variable_transport by simp
    have source_suffix_poss:
        "rho @ beta \<in> poss (erase_adp_term l \<cdot> sigma)"
    proof -
      have rho_poss: "rho \<in> poss (erase_adp_term l \<cdot> sigma)"
        using var_poss_imp_poss[OF rho_var_erased] by simp
      have at_rho: "(erase_adp_term l \<cdot> sigma) |_ rho = sigma x"
        using subt_at_subst[
          OF var_poss_imp_poss[OF rho_var_erased], of sigma]
          rho_erased_at by simp
      show ?thesis using rho_poss beta_poss at_rho
        by (simp add: poss_append_poss)
    qed
    have source_suffix_local: "rho @ beta \<in> poss (s |_ redex)"
      using source_suffix_poss lhs poss_erase_adp_term by metis
    have source_full_poss: "redex @ rho @ beta \<in> poss s"
      using redex_poss source_suffix_local
        by (simp add: poss_append_poss)
    have target_full_erased_poss:
        "redex @ alpha @ beta \<in>
          poss (replace_at (erase_adp_term s) redex
            (erase_adp_term r \<cdot> sigma))"
    proof -
      have redex_after: "redex \<in>
          poss (replace_at (erase_adp_term s) redex
            (erase_adp_term r \<cdot> sigma))"
        by (rule replace_at_below_poss[OF redex_erased_poss]) simp
      have redex_value: "replace_at (erase_adp_term s) redex
          (erase_adp_term r \<cdot> sigma) |_ redex =
          erase_adp_term r \<cdot> sigma"
        by (rule replace_at_subt_at[OF redex_erased_poss])
      have target_suffix_local: "alpha @ beta \<in>
          poss (replace_at (erase_adp_term s) redex
            (erase_adp_term r \<cdot> sigma) |_ redex)"
        using target_poss redex_value by simp
      show ?thesis using redex_after target_suffix_local
        by (simp add: poss_append_poss)
    qed
    have target_full_erased_term_poss:
        "redex @ alpha @ beta \<in> poss (erase_adp_term t)"
      using target_full_erased_poss erased_target by simp
    have target_full_poss: "redex @ alpha @ beta \<in> poss t"
      using target_full_erased_term_poss poss_erase_adp_term by metis
    have source_projection:
        "erase_adp_term (s |_ (redex @ rho @ beta)) =
          erase_adp_term s |_ (redex @ rho @ beta)"
      by (rule erase_adp_term_subt_at[OF source_full_poss])
    have target_projection:
        "erase_adp_term (t |_ (redex @ alpha @ beta)) =
          erase_adp_term t |_ (redex @ alpha @ beta)"
      by (rule erase_adp_term_subt_at[OF target_full_poss])
    show "erase_adp_term (s |_ q) = erase_adp_term (t |_ q')"
      using source_local target_local erased_target
        source_q target_q source_projection target_projection by simp
    qed
  qed
qed

lemma position_prefix_not_parallel:
  assumes "p \<le>\<^sub>p q"
  shows "\<not> Position.parallel_pos p q"
proof -
  have "p \<le>\<^sub>p q @ []" using assms by simp
  then show ?thesis by (rule pos_less_eq_append_not_parallel)
qed

lemma origin_edge_nonroot_unique:
  assumes first: "origin_edge l r p sigma roots phi q q1"
    and second: "origin_edge l r p sigma roots phi q q2"
    and nonroot: "q \<noteq> p"
  shows "q1 = q2"
  using first
proof cases
  case preserved
  from second show ?thesis
  proof cases
    case preserved
    then show ?thesis using `q1 = q` by simp
  next
    case root_target
    then show ?thesis using nonroot by simp
  next
    case (variable_transport rho alpha beta)
    have p_le_q: "p \<le>\<^sub>p q" using variable_transport by simp
    have not_above: "\<not> q <\<^sub>p p"
    proof
      assume above: "q <\<^sub>p p"
      then have q_le_p: "q \<le>\<^sub>p p"
        by (rule prefix_order.less_imp_le)
      have "q = p" by (rule prefix_order.antisym[OF q_le_p p_le_q])
      with above show False by simp
    qed
    have not_parallel: "\<not> Position.parallel_pos q p"
    proof
      assume "q \<bottom> p"
      then have "p \<bottom> q" by (rule parallel_pos_sym)
      moreover have "\<not> Position.parallel_pos p q"
        by (rule position_prefix_not_parallel[OF p_le_q])
      ultimately show False by contradiction
    qed
    from preserved not_above not_parallel show ?thesis by simp
  qed
next
  case root_target
  then show ?thesis using nonroot by simp
next
  case (variable_transport rho1 alpha1 beta1)
  have rho1_var: "rho1 \<in> var_poss l" using variable_transport by simp
  have phi1: "phi rho1 = Some alpha1" using variable_transport by simp
  have source1: "q = p @ rho1 @ beta1" using variable_transport by simp
  have target1: "q1 = p @ alpha1 @ beta1" using variable_transport by simp
  from second show ?thesis
  proof cases
    case preserved
    have p_le_q: "p \<le>\<^sub>p q" using variable_transport by simp
    have not_above: "\<not> q <\<^sub>p p"
    proof
      assume above: "q <\<^sub>p p"
      then have q_le_p: "q \<le>\<^sub>p p"
        by (rule prefix_order.less_imp_le)
      have "q = p" by (rule prefix_order.antisym[OF q_le_p p_le_q])
      with above show False by simp
    qed
    have not_parallel: "\<not> Position.parallel_pos q p"
    proof
      assume "q \<bottom> p"
      then have "p \<bottom> q" by (rule parallel_pos_sym)
      moreover have "\<not> Position.parallel_pos p q"
        by (rule position_prefix_not_parallel[OF p_le_q])
      ultimately show False by contradiction
    qed
    from preserved not_above not_parallel show ?thesis by simp
  next
    case root_target
    then show ?thesis using nonroot by simp
  next
    case (variable_transport rho2 alpha2 beta2)
    have rho2_var: "rho2 \<in> var_poss l" using variable_transport by simp
    have phi2: "phi rho2 = Some alpha2" using variable_transport by simp
    have source2: "q = p @ rho2 @ beta2" using variable_transport by simp
    have target2: "q2 = p @ alpha2 @ beta2" using variable_transport by simp
    have tails: "rho1 @ beta1 = rho2 @ beta2"
      using source1 source2 by simp
    have rho_beta: "rho1 = rho2 \<and> beta1 = beta2"
      using tails rho1_var rho2_var
      by (metis append_eq_append_conv less_eq_pos_simps(1)
          pos_less_eq_append_not_parallel var_poss_parallel)
    then have rho: "rho1 = rho2" and beta: "beta1 = beta2" by auto
    have alpha: "alpha1 = alpha2"
      using phi1 phi2 rho by simp
    show ?thesis using target1 target2 alpha beta by simp
  qed
qed

lemma origin_edge_from_redex_is_root_target:
  assumes edge: "origin_edge l r p sigma roots phi p q'"
    and lhs_fun: "is_Fun l"
  obtains alpha where "alpha \<in> roots" "q' = p @ alpha"
  using edge
proof cases
  case preserved
  then show thesis by auto
next
  case (root_target alpha)
  show thesis by (rule that[of alpha]) (use root_target in auto)
next
  case (variable_transport rho alpha beta)
  from variable_transport have "rho @ beta = []" by simp
  then have "rho = []" by simp
  with variable_transport lhs_fun show thesis by (cases l) auto
qed

lemma distinct_origin_edges_from_redex_have_distinct_roots:
  assumes first: "origin_edge l r p sigma roots phi p q1"
    and second: "origin_edge l r p sigma roots phi p q2"
    and distinct: "q1 \<noteq> q2"
    and lhs_fun: "is_Fun l"
  obtains alpha1 alpha2 where
    "alpha1 \<in> roots" "alpha2 \<in> roots" "alpha1 \<noteq> alpha2"
proof -
  from origin_edge_from_redex_is_root_target[OF first lhs_fun]
  obtain alpha1 where alpha1: "alpha1 \<in> roots"
    and q1: "q1 = p @ alpha1" .
  from origin_edge_from_redex_is_root_target[OF second lhs_fun]
  obtain alpha2 where alpha2: "alpha2 \<in> roots"
    and q2: "q2 = p @ alpha2" .
  have "alpha1 \<noteq> alpha2" using distinct q1 q2 by auto
  show thesis by (rule that[OF alpha1 alpha2 `alpha1 \<noteq> alpha2`])
qed

lemma relative_adp_selected_chain_origin_edge_time:
  assumes "((i,q),(j,q')) \<in>
    relative_adp_selected_chain_origin_edge P A terms"
  shows "j = Suc i"
  using assms unfolding relative_adp_selected_chain_origin_edge_def by auto

lemma relative_adp_selected_unlabeled_successor_unique:
  assumes first: "((i,q),(Suc i,q1)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and second: "((i,q),(Suc i,q2)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and unlabeled:
      "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
  shows "q1 = q2"
proof -
  let ?witness = "relative_adp_selected_step_witness P A terms i"
  from first have first_origin:
      "relative_adp_step_witness_origin_edge ?witness q q1"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  from second have second_origin:
      "relative_adp_step_witness_origin_edge ?witness q q2"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  from first_origin obtain l1 r1 where
      pair1: "radp_witness_pair ?witness = (l1,r1)"
    and edge1: "origin_edge (erase_adp_term l1) (erase_adp_term r1)
      (radp_witness_redex ?witness) (radp_witness_subst ?witness)
      (if radp_witness_at_sharp ?witness then sharp_positions r1 else {})
      (radp_witness_vrf ?witness) q q1"
    unfolding relative_adp_step_witness_origin_edge_def by blast
  from second_origin obtain l2 r2 where
      pair2: "radp_witness_pair ?witness = (l2,r2)"
    and edge2: "origin_edge (erase_adp_term l2) (erase_adp_term r2)
      (radp_witness_redex ?witness) (radp_witness_subst ?witness)
      (if radp_witness_at_sharp ?witness then sharp_positions r2 else {})
      (radp_witness_vrf ?witness) q q2"
    unfolding relative_adp_step_witness_origin_edge_def by blast
  have pairs: "l1 = l2 \<and> r1 = r2" using pair1 pair2 by simp
  have not_redex:
      "snd (snd (relative_adp_selected_application P A terms i)) \<noteq> q"
    by (rule relative_adp_selected_unlabeled_edge_not_at_redex[
        OF first step subset unlabeled])
  then have witness_not_redex: "radp_witness_redex ?witness \<noteq> q"
    unfolding relative_adp_selected_application_def by (simp add: Let_def)
  then have q_not_witness_redex: "q \<noteq> radp_witness_redex ?witness"
    by simp
  from edge2 pairs have edge2':
      "origin_edge (erase_adp_term l1) (erase_adp_term r1)
        (radp_witness_redex ?witness) (radp_witness_subst ?witness)
        (if radp_witness_at_sharp ?witness then sharp_positions r1 else {})
        (radp_witness_vrf ?witness) q q2"
    using edge2 pairs
    by (cases "radp_witness_at_sharp ?witness") auto
  show ?thesis
    by (rule origin_edge_nonroot_unique[
        OF edge1 edge2' q_not_witness_redex])
qed

lemma relative_adp_selected_unlabeled_node_successor_unique:
  assumes first: "(source,target1) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and second: "(source,target2) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and unlabeled:
      "\<not> relative_adp_selected_chain_labeled P A terms source"
  shows "target1 = target2"
proof (cases source, cases target1, cases target2)
  fix i q j1 q1 j2 q2
  assume source: "source = (i,q)"
    and target1: "target1 = (j1,q1)"
    and target2: "target2 = (j2,q2)"
  from first have j1: "j1 = Suc i"
    unfolding source target1 relative_adp_selected_chain_origin_edge_def
    by auto
  from second have j2: "j2 = Suc i"
    unfolding source target2 relative_adp_selected_chain_origin_edge_def
    by auto
  have first': "((i,q),(Suc i,q1)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using first unfolding source target1 j1 .
  have second': "((i,q),(Suc i,q2)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using second unfolding source target2 j2 .
  have unlabeled':
      "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
    using unlabeled unfolding source .
  have q: "q1 = q2"
    by (rule relative_adp_selected_unlabeled_successor_unique[
        OF first' second' steps subset unlabeled'])
  show ?thesis using target1 target2 j1 j2 q by simp
qed

lemma relative_adp_selected_event_offshoot_is_labeled:
  assumes offshoot: "event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n"
    and path_edge: "(path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "relative_adp_selected_chain_labeled P A terms (path n)"
proof (rule ccontr)
  assume unlabeled:
    "\<not> relative_adp_selected_chain_labeled P A terms (path n)"
  from offshoot obtain target where edge:
      "(path n,target) \<in>
        relative_adp_selected_chain_origin_edge P A terms"
    and distinct: "target \<noteq> path (Suc n)"
    unfolding event_offshoot_def by blast
  have "target = path (Suc n)"
    by (rule relative_adp_selected_unlabeled_node_successor_unique[
        OF edge path_edge steps subset unlabeled])
  with distinct show False by contradiction
qed

lemma relative_adp_selected_labeled_distinct_successors_have_multiple_rhs_marks:
  assumes label:
      "relative_adp_selected_chain_label P A terms (i,q) pair"
    and first: "((i,q),(Suc i,q1)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and second: "((i,q),(Suc i,q2)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and distinct: "q1 \<noteq> q2"
    and lhs_fun: "is_Fun (fst pair)"
  obtains alpha1 alpha2 where
    "alpha1 \<in> sharp_positions (snd pair)"
    "alpha2 \<in> sharp_positions (snd pair)"
    "alpha1 \<noteq> alpha2"
proof -
  let ?witness = "relative_adp_selected_step_witness P A terms i"
  obtain l r where pair: "pair = (l,r)" by (cases pair) auto
  from label have at: "radp_witness_at_sharp ?witness"
    and witness_pair: "radp_witness_pair ?witness = (l,r)"
    and redex: "radp_witness_redex ?witness = q"
    unfolding relative_adp_selected_chain_label_def
      relative_adp_selected_application_def pair Let_def
    by auto
  from first have first_exact:
      "relative_adp_step_witness_origin_edge ?witness q q1"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  from second have second_exact:
      "relative_adp_step_witness_origin_edge ?witness q q2"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  from first_exact witness_pair at redex have edge1:
      "origin_edge (erase_adp_term l) (erase_adp_term r) q
        (radp_witness_subst ?witness) (sharp_positions r)
        (radp_witness_vrf ?witness) q q1"
    unfolding relative_adp_step_witness_origin_edge_def by auto
  from second_exact witness_pair at redex have edge2:
      "origin_edge (erase_adp_term l) (erase_adp_term r) q
        (radp_witness_subst ?witness) (sharp_positions r)
        (radp_witness_vrf ?witness) q q2"
    unfolding relative_adp_step_witness_origin_edge_def by auto
  have erased_lhs_fun: "is_Fun (erase_adp_term l)"
    using lhs_fun unfolding pair by (cases l) auto
  from distinct_origin_edges_from_redex_have_distinct_roots[
      OF edge1 edge2 distinct erased_lhs_fun]
  obtain alpha1 alpha2 where alpha1: "alpha1 \<in> sharp_positions r"
    and alpha2: "alpha2 \<in> sharp_positions r"
    and different: "alpha1 \<noteq> alpha2" .
  show thesis
    by (rule that[of alpha1 alpha2])
       (use alpha1 alpha2 different pair in auto)
qed

lemma relative_adp_selected_label_in_problem:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and label: "relative_adp_selected_chain_label P A terms (i,q) pair"
  shows "pair \<in> A"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  have preferred: "relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i)) ?application"
    by (rule relative_adp_selected_application_valid[OF step subset])
  then have applied: "relative_adp_applied_at A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application))"
    unfolding relative_adp_preferred_application_valid_def
      relative_adp_application_valid_def by simp
  from label have "fst (snd ?application) = pair"
    unfolding relative_adp_selected_chain_label_def Let_def by simp
  with applied show ?thesis unfolding relative_adp_applied_at_def by auto
qed

lemma relative_adp_selected_label_in_main_is_main_event:
  assumes label: "relative_adp_selected_chain_label P A terms node pair"
    and main: "pair \<in> P"
  shows "relative_adp_selected_chain_main_event P A terms node"
  using label main unfolding relative_adp_selected_chain_label_def
    relative_adp_selected_chain_main_event_def
  by (cases node) (auto simp: Let_def)

lemma relative_adp_selected_nonmain_offshoot_has_branching_base_label:
  assumes offshoot: "event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n"
    and path_edge: "(path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
    and nonmain:
      "\<not> relative_adp_selected_chain_main_event P A terms (path n)"
  obtains pair alpha1 alpha2 where
    "pair \<in> A - P"
    "relative_adp_selected_chain_label P A terms (path n) pair"
    "alpha1 \<in> sharp_positions (snd pair)"
    "alpha2 \<in> sharp_positions (snd pair)"
    "alpha1 \<noteq> alpha2"
proof -
  have labeled:
      "relative_adp_selected_chain_labeled P A terms (path n)"
    by (rule relative_adp_selected_event_offshoot_is_labeled[
        OF offshoot path_edge steps subset])
  from labeled
  obtain pair where label:
      "relative_adp_selected_chain_label P A terms (path n) pair"
    unfolding relative_adp_selected_chain_labeled_def by blast
  obtain i q where source: "path n = (i,q)" by (cases "path n") auto
  obtain j q1 where next_node: "path (Suc n) = (j,q1)"
    by (cases "path (Suc n)") auto
  have path_edge': "((i,q),(j,q1)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using path_edge unfolding source next_node .
  have j: "j = Suc i"
    by (rule relative_adp_selected_chain_origin_edge_time[OF path_edge'])
  have step: "(terms i, terms (Suc i)) \<in> adp_step A" by (rule steps)
  have in_A: "pair \<in> A"
    by (rule relative_adp_selected_label_in_problem[OF step subset])
       (use label in \<open>simp only: source\<close>)
  have not_P: "pair \<notin> P"
  proof
    assume "pair \<in> P"
    then have "relative_adp_selected_chain_main_event P A terms (path n)"
      by (rule relative_adp_selected_label_in_main_is_main_event[OF label])
    with nonmain show False by contradiction
  qed
  from offshoot obtain branch where branch_edge:
      "(path n,branch) \<in>
        relative_adp_selected_chain_origin_edge P A terms"
    and distinct: "branch \<noteq> path (Suc n)"
    unfolding event_offshoot_def by blast
  obtain k q2 where branch: "branch = (k,q2)" by (cases branch) auto
  have branch_edge': "((i,q),(k,q2)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using branch_edge unfolding source branch .
  have k: "k = Suc i"
    by (rule relative_adp_selected_chain_origin_edge_time[OF branch_edge'])
  have position_distinct: "q1 \<noteq> q2"
    using distinct unfolding next_node branch j k by auto
  have first: "((i,q),(Suc i,q1)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using path_edge' unfolding j .
  have second: "((i,q),(Suc i,q2)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using branch_edge' unfolding k .
  have label_at:
      "relative_adp_selected_chain_label P A terms (i,q) pair"
    using label unfolding source .
  from relative_adp_selected_labeled_distinct_successors_have_multiple_rhs_marks[
      OF label_at first second position_distinct lhs_fun[OF in_A]]
  obtain alpha1 alpha2 where alpha1: "alpha1 \<in> sharp_positions (snd pair)"
    and alpha2: "alpha2 \<in> sharp_positions (snd pair)"
    and different: "alpha1 \<noteq> alpha2" .
  show thesis
    by (rule that[of pair alpha1 alpha2])
       (use in_A not_P label alpha1 alpha2 different in auto)
qed

lemma relative_adp_selected_unlabeled_moving_projection:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and unlabeled: "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
    and moving: "q' \<noteq> q"
  shows "mark_adp_root (terms i |_ q) =
    mark_adp_root (terms (Suc i) |_ q')"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  from edge have origin: "relative_adp_canonical_origin_edge A
      (fst ?application) (terms i) (terms (Suc i))
      (fst (snd ?application)) (snd (snd ?application)) q q'"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  have not_redex: "snd (snd ?application) \<noteq> q"
    by (rule relative_adp_selected_unlabeled_edge_not_at_redex[
        OF edge step subset unlabeled])
  have alternative: "(q' = q \<and>
      (q <\<^sub>p snd (snd ?application) \<or>
       q \<bottom> snd (snd ?application))) \<or>
      erase_adp_term (terms i |_ q) =
        erase_adp_term (terms (Suc i) |_ q')"
    by (rule relative_adp_canonical_origin_projection[OF origin not_redex])
  then have projection: "erase_adp_term (terms i |_ q) =
      erase_adp_term (terms (Suc i) |_ q')"
    using moving by blast
  show ?thesis using projection unfolding mark_adp_root_def by simp
qed

lemma relative_adp_selected_unlabeled_projection:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and unlabeled:
      "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
  shows "(mark_adp_root (terms i |_ q),
      mark_adp_root (terms (Suc i) |_ q')) \<in>
    (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  from edge have source_sharp: "q \<in> sharp_positions (terms i)"
    and origin: "relative_adp_canonical_origin_edge A
      (fst ?application) (terms i) (terms (Suc i))
      (fst (snd ?application)) (snd (snd ?application)) q q'"
    unfolding relative_adp_selected_chain_origin_edge_def
    by (auto simp: Let_def)
  have q_poss: "q \<in> poss (terms i)"
    using source_sharp unfolding sharp_positions_def by auto
  have not_redex: "snd (snd ?application) \<noteq> q"
    by (rule relative_adp_selected_unlabeled_edge_not_at_redex[
        OF edge step subset unlabeled])
  have alternative:
      "(q' = q \<and> (q <\<^sub>p snd (snd ?application) \<or>
        q \<bottom> snd (snd ?application))) \<or>
       erase_adp_term (terms i |_ q) =
         erase_adp_term (terms (Suc i) |_ q')"
    by (rule relative_adp_canonical_origin_projection[OF origin not_redex])
  from origin obtain l r phi sigma annotations where
      rule: "(l,r) \<in> A"
    and valid: "valid_vrf (l,r) phi"
    and redex_fun: "snd (snd ?application) \<in> fun_poss (terms i)"
    and lhs: "erase_adp_term (terms i |_ snd (snd ?application)) =
      erase_adp_term l \<cdot> sigma"
    and target: "terms (Suc i) = replace_at (terms i)
      (snd (snd ?application))
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_canonical_origin_edge_def by blast
  from alternative show ?thesis
  proof
    assume preserved:
        "q' = q \<and> (q <\<^sub>p snd (snd ?application) \<or>
          q \<bottom> snd (snd ?application))"
    then have q': "q' = q" and outside:
        "q <\<^sub>p snd (snd ?application) \<or>
          q \<bottom> snd (snd ?application)"
      by auto
    from outside show ?thesis
    proof
      assume above: "q <\<^sub>p snd (snd ?application)"
      from prefixE[OF prefix_order.less_imp_le[OF above]]
      obtain delta where redex: "snd (snd ?application) = q @ delta"
        by blast
      have nonroot: "delta \<noteq> []" using above redex by auto
      have delta_fun: "delta \<in> fun_poss (terms i |_ q)"
      proof -
        have delta_poss: "delta \<in> poss (terms i |_ q)"
          using fun_poss_imp_poss[OF redex_fun] q_poss redex by simp
        from fun_poss_fun_conv[OF redex_fun]
        obtain f ts where at:
            "terms i |_ snd (snd ?application) = Fun f ts" by blast
        have local_at: "terms i |_ q |_ delta = Fun f ts"
          using at redex q_poss by simp
        show ?thesis
          by (rule poss_is_Fun_fun_poss[OF delta_poss])
             (use local_at in simp)
      qed
      have delta_fun_erased:
          "delta \<in> fun_poss (erase_adp_term (terms i |_ q))"
        using delta_fun fun_poss_erase_adp_term[of "terms i |_ q"] by simp
      have delta_poss: "delta \<in> poss (terms i |_ q)"
        by (rule fun_poss_imp_poss[OF delta_fun])
      have local_redex:
          "erase_adp_term (terms i |_ q) |_ delta =
            erase_adp_term l \<cdot> sigma"
        using lhs redex q_poss delta_poss
          erase_adp_term_subt_at[OF q_poss]
          erase_adp_term_subt_at[OF delta_poss] by simp
      have weak_step:
          "(mark_adp_root (terms i |_ q),
            annotate_term {[]} (replace_at
              (erase_adp_term (terms i |_ q)) delta
              (erase_adp_term r \<cdot> sigma))) \<in>
            adp_step_case_rel (erase_annotations_adp ` A) False"
        unfolding mark_adp_root_def
        by (rule annotate_single_root_below_adp_step[
            OF rule valid delta_fun_erased nonroot local_redex])
      have target_nested:
          "terms (Suc i) = replace_at (terms i) q
            (replace_at (terms i |_ q) delta
              (annotate_term annotations (erase_adp_term r \<cdot> sigma)))"
        using target redex replace_at_append_context[OF q_poss,
            of delta "annotate_term annotations
              (erase_adp_term r \<cdot> sigma)"]
        by simp
      have target_q_annotated:
          "terms (Suc i) |_ q = replace_at (terms i |_ q) delta
            (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
        unfolding target_nested
        by (rule replace_at_subt_at[OF q_poss])
      have target_q_erased:
          "erase_adp_term (terms (Suc i) |_ q) =
            replace_at (erase_adp_term (terms i |_ q)) delta
              (erase_adp_term r \<cdot> sigma)"
        using arg_cong[OF target_q_annotated,
            of erase_adp_term] delta_poss
        by (simp add: erase_adp_term_replace_at)
      have target_mark:
          "mark_adp_root (terms (Suc i) |_ q) =
            annotate_term {[]} (replace_at
              (erase_adp_term (terms i |_ q)) delta
              (erase_adp_term r \<cdot> sigma))"
        unfolding mark_adp_root_def target_q_erased by simp
      show ?thesis unfolding q' target_mark
        by (rule r_into_rtrancl[OF weak_step])
    next
      assume parallel: "q \<bottom> snd (snd ?application)"
      have same: "terms (Suc i) |_ q = terms i |_ q"
        unfolding target
        by (rule parallel_replace_at_subt_at[
            OF parallel_pos_sym[OF parallel]
              fun_poss_imp_poss[OF redex_fun] q_poss])
      show ?thesis unfolding q' same by simp
    qed
  next
    assume projection: "erase_adp_term (terms i |_ q) =
        erase_adp_term (terms (Suc i) |_ q')"
    then have "mark_adp_root (terms i |_ q) =
        mark_adp_root (terms (Suc i) |_ q')"
      unfolding mark_adp_root_def by simp
    then show ?thesis by simp
  qed
qed

lemma relative_adp_selected_unlabeled_rtrancl_projection:
  assumes path: "(source,target) \<in>
      {(source,target). (source,target) \<in>
          relative_adp_selected_chain_origin_edge P A terms \<and>
        \<not> relative_adp_selected_chain_labeled P A terms source}\<^sup>*"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "(mark_adp_root (terms (fst source) |_ snd source),
      mark_adp_root (terms (fst target) |_ snd target)) \<in>
    (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step middle target)
  from step.hyps(2) have edge: "(middle,target) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and unlabeled:
      "\<not> relative_adp_selected_chain_labeled P A terms middle"
    by auto
  obtain i q where middle: "middle = (i,q)" by (cases middle) auto
  from edge obtain q' where target: "target = (Suc i,q')"
    unfolding middle relative_adp_selected_chain_origin_edge_def by auto
  have edge': "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using edge unfolding middle target .
  have unlabeled':
      "\<not> relative_adp_selected_chain_labeled P A terms (i,q)"
    using unlabeled unfolding middle .
  have projection':
      "(mark_adp_root (terms i |_ q),
        mark_adp_root (terms (Suc i) |_ q')) \<in>
      (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
    by (rule relative_adp_selected_unlabeled_projection[
        OF edge' steps subset unlabeled'])
  have projection:
      "(mark_adp_root (terms (fst middle) |_ snd middle),
        mark_adp_root (terms (fst target) |_ snd target)) \<in>
      (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
    using projection' unfolding middle target by simp
  show ?case
    by (rule rtrancl_trans[OF step.hyps(3) projection])
qed

lemma relative_adp_selected_labeled_source_instance:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and label: "relative_adp_selected_chain_label P A terms (i,q) pair"
    and lhs_fun: "is_Fun (fst pair)"
  obtains tau where
    "mark_adp_root (terms i |_ q) = mark_adp_root (fst pair) \<cdot> tau"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  have preferred: "relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i)) ?application"
    by (rule relative_adp_selected_application_valid[OF step subset])
  then have applied: "relative_adp_applied_at A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application))"
    unfolding relative_adp_preferred_application_valid_def
      relative_adp_application_valid_def by simp
  from label have pair: "fst (snd ?application) = pair"
    and redex: "snd (snd ?application) = q"
    unfolding relative_adp_selected_chain_label_def by (auto simp: Let_def)
  from applied obtain l r phi sigma annotations where
      pair_lr: "fst (snd ?application) = (l,r)"
    and lhs: "erase_adp_term (terms i |_
        snd (snd ?application)) = erase_adp_term l \<cdot> sigma"
    unfolding relative_adp_applied_at_def by blast
  have pair_eq: "pair = (l,r)" using pair pair_lr by simp
  have erased_instance: "erase_adp_term (terms i |_ q) =
      erase_adp_term (fst pair) \<cdot> sigma"
    using lhs redex pair_eq by simp
  have marked: "mark_adp_root (terms i |_ q) =
      mark_adp_root (fst pair) \<cdot> (plain_adp_term \<circ> sigma)"
    by (rule mark_adp_root_erased_instance[OF lhs_fun erased_instance])
  show thesis by (rule that[OF marked])
qed

lemma relative_adp_selected_labeled_edge_enters_rhs:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and label: "relative_adp_selected_chain_label P A terms (i,q) pair"
    and lhs_fun: "is_Fun (fst pair)"
  obtains alpha where
    "alpha \<in> sharp_positions (snd pair)"
    "q' = q @ alpha"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  from edge have source: "q \<in> sharp_positions (terms i)"
    and origin: "relative_adp_canonical_origin_edge A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application)) q q'"
    unfolding relative_adp_selected_chain_origin_edge_def by (auto simp: Let_def)
  from label have at: "fst ?application"
    and pair: "fst (snd ?application) = pair"
    and redex: "snd (snd ?application) = q"
    using label unfolding relative_adp_selected_chain_label_def
    by (auto simp: Let_def)
  have fixed: "relative_adp_canonical_origin_edge A True
      (terms i) (terms (Suc i)) pair q q q'"
    using origin at pair redex by simp
  from fixed obtain l r phi sigma annotations where
      pair_lr: "pair = (l,r)"
    and origin_raw: "origin_edge (erase_adp_term l) (erase_adp_term r)
      q sigma (if True then sharp_positions r else {}) phi q q'"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have origin_edge: "origin_edge (erase_adp_term l) (erase_adp_term r)
      q sigma (sharp_positions r) phi q q'"
    using origin_raw by simp
  from origin_edge show thesis
  proof cases
    case preserved
    then show thesis by simp
  next
    case (root_target alpha)
    have alpha: "alpha \<in> sharp_positions (snd pair)"
      using root_target pair_lr by simp
    have q': "q' = q @ alpha" using root_target by simp
    show thesis by (rule that[OF alpha q'])
  next
    case (variable_transport rho alpha beta)
    have l_fun: "is_Fun l" using lhs_fun pair_lr by simp
    have rho_var: "rho \<in> var_poss l"
      using variable_transport var_poss_erase_adp_term by auto
    have rho_nonempty: "rho \<noteq> []"
    proof
      assume "rho = []"
      with rho_var have "is_Var l"
        unfolding var_poss_iff by auto
      with l_fun show False by (cases l) auto
    qed
    have "length q < length (q @ rho @ beta)"
      using rho_nonempty by simp
    moreover have "q = q @ rho @ beta" using variable_transport by simp
    ultimately show thesis by simp
  qed
qed

lemma relative_adp_selected_labeled_edge_rhs_instance:
  assumes edge: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and label: "relative_adp_selected_chain_label P A terms (i,q) pair"
    and lhs_fun: "is_Fun (fst pair)"
  obtains alpha tau where
    "alpha \<in> sharp_positions (snd pair)"
    "mark_adp_root (terms (Suc i) |_ q') =
      mark_adp_root (snd pair |_ alpha) \<cdot> tau"
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
    unfolding relative_adp_selected_chain_origin_edge_def by (auto simp: Let_def)
  from label have at: "fst ?application"
    and pair: "fst (snd ?application) = pair"
    and redex: "snd (snd ?application) = q"
    unfolding relative_adp_selected_chain_label_def by (auto simp: Let_def)
  from origin obtain l r phi sigma annotations where
      pair_lr: "fst (snd ?application) = (l,r)"
    and target: "terms (Suc i) = replace_at (terms i)
      (snd (snd ?application))
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have pair_eq: "pair = (l,r)" using pair pair_lr by simp
  have q_poss: "q \<in> poss (terms i)"
    using source_sharp unfolding sharp_positions_def by auto
  have q_after: "q \<in> poss (terms (Suc i))"
    unfolding target redex
    by (rule replace_at_below_poss[OF q_poss]) simp
  have local_target: "terms (Suc i) |_ q =
      annotate_term annotations (erase_adp_term r \<cdot> sigma)"
    unfolding target redex
    by (rule replace_at_subt_at[OF q_poss])
  have alpha_poss: "alpha \<in> poss r"
    using alpha pair_eq unfolding sharp_positions_def by auto
  have alpha_erased_poss: "alpha \<in> poss (erase_adp_term r)"
    using alpha_poss by simp
  have alpha_subst_poss:
      "alpha \<in> poss (erase_adp_term r \<cdot> sigma)"
    using alpha_erased_poss by simp
  have alpha_annotated_poss:
      "alpha \<in> poss
        (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    using alpha_subst_poss poss_annotate_term_at[
        of annotations "[]" "erase_adp_term r \<cdot> sigma"]
    unfolding annotate_term_def by simp
  have erased_instance:
      "erase_adp_term (terms (Suc i) |_ q') =
        erase_adp_term (snd pair |_ alpha) \<cdot> sigma"
    using subt_at_append[OF q_after, of alpha] local_target
      subt_at_subst[OF alpha_erased_poss, of sigma]
      erase_adp_term_subt_at[OF alpha_poss]
      erase_adp_term_subt_at[OF alpha_annotated_poss]
    unfolding q' pair_eq by simp
  have rhs_fun: "is_Fun (snd pair |_ alpha)"
    using alpha unfolding sharp_positions_def by (auto split: option.splits)
  have marked: "mark_adp_root (terms (Suc i) |_ q') =
      mark_adp_root (snd pair |_ alpha) \<cdot> (plain_adp_term \<circ> sigma)"
    by (rule mark_adp_root_erased_instance[OF rhs_fun erased_instance])
  show thesis by (rule that[OF alpha marked])
qed

lemma relative_adp_selected_labeled_segment_dependency_edge:
  assumes entry: "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and source_label:
      "relative_adp_selected_chain_label P A terms (i,q) pair"
    and path: "((Suc i,q'),(j,rho)) \<in>
      {(source,target). (source,target) \<in>
          relative_adp_selected_chain_origin_edge P A terms \<and>
        \<not> relative_adp_selected_chain_labeled P A terms source}\<^sup>*"
    and target_label:
      "relative_adp_selected_chain_label P A terms (j,rho) next_pair"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and source_lhs_fun: "is_Fun (fst pair)"
    and target_lhs_fun: "is_Fun (fst next_pair)"
  shows "relative_adp_dependency_edge A pair next_pair"
proof -
  from relative_adp_selected_labeled_edge_rhs_instance[
      OF entry source_label source_lhs_fun]
  obtain alpha sigma where
      alpha: "alpha \<in> sharp_positions (snd pair)"
    and source_instance:
      "mark_adp_root (terms (Suc i) |_ q') =
        mark_adp_root (snd pair |_ alpha) \<cdot> sigma" .
  have projected_raw:
      "(mark_adp_root (terms (fst (Suc i,q')) |_ snd (Suc i,q')),
        mark_adp_root (terms (fst (j,rho)) |_ snd (j,rho))) \<in>
      (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
    by (rule relative_adp_selected_unlabeled_rtrancl_projection[
        where source="(Suc i,q')" and target="(j,rho)"
          and P=P and A=A and terms=terms,
        OF path steps subset])
  have projected:
      "(mark_adp_root (terms (Suc i) |_ q'),
        mark_adp_root (terms j |_ rho)) \<in>
      (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*"
    using projected_raw by simp
  from relative_adp_selected_labeled_source_instance[
      OF steps subset target_label target_lhs_fun]
  obtain tau where target_instance:
      "mark_adp_root (terms j |_ rho) =
        mark_adp_root (fst next_pair) \<cdot> tau" .
  have witness: "snd pair |_ alpha \<in> annotated_rhs_subterms pair"
    using alpha unfolding annotated_rhs_subterms_def by blast
  show ?thesis
    unfolding relative_adp_dependency_edge_def
    by (rule bexI[OF _ witness], rule exI[of _ sigma],
        rule exI[of _ tau])
       (use projected source_instance target_instance in simp)
qed

lemma relative_adp_selected_labeled_path_dependency_edge:
  assumes infinite: "infinite
      {n. relative_adp_selected_chain_labeled P A terms (path n)}"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "relative_adp_dependency_edge A
    (relative_adp_selected_chain_node_label P A terms
      (path (enumerate
        {n. relative_adp_selected_chain_labeled P A terms (path n)} n)))
    (relative_adp_selected_chain_node_label P A terms
      (path (enumerate
        {n. relative_adp_selected_chain_labeled P A terms (path n)} (Suc n))))"
proof -
  let ?I = "{n. relative_adp_selected_chain_labeled P A terms (path n)}"
  let ?labels = "\<lambda>n. relative_adp_selected_chain_node_label P A terms
      (path (enumerate ?I n))"
  let ?i = "enumerate ?I n"
  let ?j = "enumerate ?I (Suc n)"
  have iI: "?i \<in> ?I" by (rule enumerate_in_set[OF infinite])
  have jI: "?j \<in> ?I" by (rule enumerate_in_set[OF infinite])
  have ij: "?i < ?j"
    by (rule enumerate_mono[OF _ infinite]) simp
  have source_labeled:
      "relative_adp_selected_chain_labeled P A terms (path ?i)"
    using iI by simp
  have target_labeled:
      "relative_adp_selected_chain_labeled P A terms (path ?j)"
    using jI by simp
  have source_label:
      "relative_adp_selected_chain_label P A terms (path ?i) (?labels n)"
    using relative_adp_selected_chain_labeled_has_node_label[OF source_labeled]
    by simp
  have target_label:
      "relative_adp_selected_chain_label P A terms (path ?j) (?labels (Suc n))"
    using relative_adp_selected_chain_labeled_has_node_label[OF target_labeled]
    by simp
  obtain time q where source: "path ?i = (time,q)" by (cases "path ?i") auto
  obtain next_time q' where next_node: "path (Suc ?i) = (next_time,q')"
    by (cases "path (Suc ?i)") auto
  obtain target_time rho where target: "path ?j = (target_time,rho)"
    by (cases "path ?j") auto
  have first_raw: "((time,q),(next_time,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using path_edge[of ?i] unfolding source next_node .
  have next_time: "next_time = Suc time"
    by (rule relative_adp_selected_chain_origin_edge_time[OF first_raw])
  have first: "((time,q),(Suc time,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    using first_raw unfolding next_time .
  have no_labels: "\<And>k. Suc ?i \<le> k \<Longrightarrow> k < ?j \<Longrightarrow>
      \<not> relative_adp_selected_chain_labeled P A terms (path k)"
  proof -
    fix k
    assume lower: "Suc ?i \<le> k" and upper: "k < ?j"
    have strict_lower: "?i < k" using lower by simp
    show "\<not> relative_adp_selected_chain_labeled P A terms (path k)"
      by (rule between_consecutive_enumerated_events[
          of "relative_adp_selected_chain_labeled P A terms" path n k,
          OF infinite strict_lower upper])
  qed
  have segment_raw: "(path (Suc ?i), path ?j) \<in>
      {(source,target). (source,target) \<in>
          relative_adp_selected_chain_origin_edge P A terms \<and>
        \<not> relative_adp_selected_chain_labeled P A terms source}\<^sup>*"
    by (rule ipath_interval_restricted_rtrancl[
        where p=path
          and E="relative_adp_selected_chain_origin_edge P A terms"
          and i="Suc ?i" and j="?j"
          and allowed="\<lambda>source.
            \<not> relative_adp_selected_chain_labeled P A terms source"])
       (use path_edge ij no_labels in auto)
  have segment: "((Suc time,q'),(target_time,rho)) \<in>
      {(source,target). (source,target) \<in>
          relative_adp_selected_chain_origin_edge P A terms \<and>
        \<not> relative_adp_selected_chain_labeled P A terms source}\<^sup>*"
    using segment_raw unfolding next_node target next_time .
  have source_in_A: "?labels n \<in> A"
    by (rule relative_adp_selected_label_in_problem[
        where i=time and q=q, OF steps[of time] subset])
       (use source_label in \<open>simp only: source\<close>)
  have target_in_A: "?labels (Suc n) \<in> A"
    by (rule relative_adp_selected_label_in_problem[
        where i=target_time and q=rho, OF steps[of target_time] subset])
       (use target_label in \<open>simp only: target\<close>)
  show ?thesis
    by (rule relative_adp_selected_labeled_segment_dependency_edge[
        OF first _ segment _ steps subset lhs_fun[OF source_in_A]
          lhs_fun[OF target_in_A]])
       (use source_label target_label in
        \<open>simp only: source target\<close>)+
qed

lemma relative_adp_selected_label_stream_in_problem:
  assumes infinite: "infinite (relative_adp_selected_label_indices P A terms path)"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "relative_adp_selected_label_stream P A terms path n \<in> A"
proof -
  let ?index = "enumerate (relative_adp_selected_label_indices P A terms path) n"
  have index: "?index \<in> relative_adp_selected_label_indices P A terms path"
    by (rule enumerate_in_set[OF infinite])
  then have labeled:
      "relative_adp_selected_chain_labeled P A terms (path ?index)"
    unfolding relative_adp_selected_label_indices_def by simp
  have label: "relative_adp_selected_chain_label P A terms (path ?index)
      (relative_adp_selected_label_stream P A terms path n)"
    using relative_adp_selected_chain_labeled_has_node_label[OF labeled]
    unfolding relative_adp_selected_label_stream_def by simp
  obtain i q where node: "path ?index = (i,q)" by (cases "path ?index") auto
  show ?thesis
    by (rule relative_adp_selected_label_in_problem[
        where i=i and q=q, OF steps[of i] subset])
       (use label in \<open>simp only: node\<close>)
qed

lemma relative_adp_selected_label_stream_dependency_edge:
  assumes infinite: "infinite (relative_adp_selected_label_indices P A terms path)"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "relative_adp_dependency_edge A
    (relative_adp_selected_label_stream P A terms path n)
    (relative_adp_selected_label_stream P A terms path (Suc n))"
proof -
  have raw: "relative_adp_dependency_edge A
      (relative_adp_selected_chain_node_label P A terms
        (path (enumerate
          {n. relative_adp_selected_chain_labeled P A terms (path n)} n)))
      (relative_adp_selected_chain_node_label P A terms
        (path (enumerate
          {n. relative_adp_selected_chain_labeled P A terms (path n)} (Suc n))))"
    by (rule relative_adp_selected_labeled_path_dependency_edge[
        where P=P and A=A and terms=terms and path=path and n=n,
        OF _ path_edge steps subset lhs_fun])
       (use infinite in
        \<open>simp add: relative_adp_selected_label_indices_def\<close>)
  show ?thesis using raw
    unfolding relative_adp_selected_label_stream_def
      relative_adp_selected_label_indices_def .
qed

lemma relative_adp_selected_main_events_give_main_label_stream:
  assumes main: "INFM n.
      relative_adp_selected_chain_main_event P A terms (path n)"
  shows "INFM n. relative_adp_selected_label_stream P A terms path n \<in> P"
proof -
  let ?I = "relative_adp_selected_label_indices P A terms path"
  have infinite: "infinite ?I"
  proof -
    have main_infinite:
        "infinite {n. relative_adp_selected_chain_main_event P A terms (path n)}"
      using main unfolding INFM_iff_infinite .
    have inclusion:
        "{n. relative_adp_selected_chain_main_event P A terms (path n)}
        \<subseteq> ?I"
      unfolding relative_adp_selected_label_indices_def
        relative_adp_selected_chain_main_event_iff_node_label by blast
    show ?thesis by (rule infinite_super[OF inclusion main_infinite])
  qed
  show ?thesis unfolding INFM_nat
  proof
    fix N
    from main[unfolded INFM_nat]
    obtain k where large: "enumerate ?I N < k"
      and main_k: "relative_adp_selected_chain_main_event P A terms (path k)"
      by blast
    from main_k have kI: "k \<in> ?I"
      unfolding relative_adp_selected_chain_main_event_iff_node_label
        relative_adp_selected_label_indices_def by blast
    from range_enumerate[OF infinite] kI obtain m where k: "k = enumerate ?I m"
      by blast
    have mono: "strict_mono (enumerate ?I)" by (rule strict_mono_enumerate[OF infinite])
    have Nm: "N < m"
    proof (rule ccontr)
      assume "\<not> N < m"
      then have "m \<le> N" by simp
      then have "enumerate ?I m \<le> enumerate ?I N"
        by (rule monoD[OF strict_mono_mono[OF mono]])
      with large k show False by simp
    qed
    have stream_main:
        "relative_adp_selected_label_stream P A terms path m \<in> P"
      using main_k unfolding k
        relative_adp_selected_chain_main_event_iff_node_label
        relative_adp_selected_label_stream_def by simp
    show "\<exists>n>N. relative_adp_selected_label_stream P A terms path n \<in> P"
      by (rule exI[of _ m]) (use Nm stream_main in simp)
  qed
qed

lemma relative_adp_selected_offshoots_give_labeled_stream:
  assumes offshoots: "INFM n. event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "infinite (relative_adp_selected_label_indices P A terms path)"
proof -
  have inclusion: "{n. event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n} \<subseteq>
      relative_adp_selected_label_indices P A terms path"
  proof
    fix n
    assume n: "n \<in> {n. event_offshoot
        (relative_adp_selected_chain_origin_edge P A terms)
        (relative_adp_selected_chain_main_event P A terms) path n}"
    have labeled: "relative_adp_selected_chain_labeled P A terms (path n)"
      by (rule relative_adp_selected_event_offshoot_is_labeled[
          where P=P and A=A and terms=terms and path=path and n=n,
          OF _ path_edge[of n] steps subset])
         (use n in simp)
    show "n \<in> relative_adp_selected_label_indices P A terms path"
      using labeled unfolding relative_adp_selected_label_indices_def by simp
  qed
  have infinite_offshoots: "infinite {n. event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n}"
    using offshoots unfolding INFM_iff_infinite .
  show ?thesis by (rule infinite_super[OF inclusion infinite_offshoots])
qed

lemma relative_adp_selected_offshoots_give_branching_base_stream:
  assumes offshoots: "INFM n. event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n"
    and no_main: "\<not> (INFM n.
      relative_adp_selected_chain_main_event P A terms (path n))"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  shows "INFM n. relative_adp_selected_label_stream P A terms path n \<in> A - P \<and>
    relative_adp_branching_pair
      (relative_adp_selected_label_stream P A terms path n)"
proof -
  let ?I = "relative_adp_selected_label_indices P A terms path"
  have infinite: "infinite ?I"
    by (rule relative_adp_selected_offshoots_give_labeled_stream[
        OF offshoots path_edge steps subset])
  from no_main[unfolded not_INFM MOST_nat_le]
  obtain K where late_nonmain: "\<And>k. K \<le> k \<Longrightarrow>
      \<not> relative_adp_selected_chain_main_event P A terms (path k)"
    by blast
  show ?thesis unfolding INFM_nat
  proof
    fix N
    from offshoots[unfolded INFM_nat]
    obtain k where large: "max K (enumerate ?I N) < k"
      and offshoot: "event_offshoot
        (relative_adp_selected_chain_origin_edge P A terms)
        (relative_adp_selected_chain_main_event P A terms) path k"
      by blast
    have labeled: "relative_adp_selected_chain_labeled P A terms (path k)"
      by (rule relative_adp_selected_event_offshoot_is_labeled[
          where P=P and A=A and terms=terms and path=path and n=k,
          OF offshoot path_edge[of k] steps subset])
    then have kI: "k \<in> ?I"
      unfolding relative_adp_selected_label_indices_def by simp
    from range_enumerate[OF infinite] kI obtain m where k: "k = enumerate ?I m"
      by blast
    have mono: "strict_mono (enumerate ?I)" by (rule strict_mono_enumerate[OF infinite])
    have Nm: "N < m"
    proof (rule ccontr)
      assume "\<not> N < m"
      then have "m \<le> N" by simp
      then have "enumerate ?I m \<le> enumerate ?I N"
        by (rule monoD[OF strict_mono_mono[OF mono]])
      with large k show False by simp
    qed
    have nonmain: "\<not> relative_adp_selected_chain_main_event P A terms (path k)"
      by (rule late_nonmain) (use large in simp)
    from relative_adp_selected_nonmain_offshoot_has_branching_base_label[
        where P=P and A=A and terms=terms and path=path and n=k,
        OF offshoot path_edge[of k] steps subset lhs_fun nonmain]
    obtain pair alpha beta where pair: "pair \<in> A - P"
      and label: "relative_adp_selected_chain_label P A terms (path k) pair"
      and alpha: "alpha \<in> sharp_positions (snd pair)"
      and beta: "beta \<in> sharp_positions (snd pair)"
      and distinct: "alpha \<noteq> beta" .
    have pair_eq: "relative_adp_selected_label_stream P A terms path m = pair"
      using label unfolding k relative_adp_selected_chain_label_def
        relative_adp_selected_label_stream_def
        relative_adp_selected_chain_node_label_def
      by (cases "path (enumerate ?I m)") (auto simp: Let_def)
    have branching: "relative_adp_branching_pair pair"
      using alpha beta distinct unfolding relative_adp_branching_pair_def by blast
    show "\<exists>n>N. relative_adp_selected_label_stream P A terms path n \<in> A - P \<and>
        relative_adp_branching_pair
          (relative_adp_selected_label_stream P A terms path n)"
      by (rule exI[of _ m]) (use Nm pair branching pair_eq in simp)
  qed
qed

lemma relative_adp_selected_no_main_eventual_base_stream:
  assumes infinite: "infinite (relative_adp_selected_label_indices P A terms path)"
    and no_main: "\<not> (INFM n.
      relative_adp_selected_chain_main_event P A terms (path n))"
    and steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  obtains N where "\<And>n. N \<le> n \<Longrightarrow>
    relative_adp_selected_label_stream P A terms path n \<in> A - P"
proof -
  from no_main[unfolded not_INFM MOST_nat_le]
  obtain K where nonmain: "\<And>k. K \<le> k \<Longrightarrow>
      \<not> relative_adp_selected_chain_main_event P A terms (path k)"
    by blast
  have base: "\<And>n. K \<le> n \<Longrightarrow>
      relative_adp_selected_label_stream P A terms path n \<in> A - P"
  proof -
    fix n
    assume Kn: "K \<le> n"
    let ?k = "enumerate (relative_adp_selected_label_indices P A terms path) n"
    have nk: "n \<le> ?k" by (rule enumerate_nat_lower_bound[OF infinite])
    have not_main_at: "\<not> relative_adp_selected_chain_main_event P A terms (path ?k)"
      by (rule nonmain) (use Kn nk in simp)
    have in_A: "relative_adp_selected_label_stream P A terms path n \<in> A"
      by (rule relative_adp_selected_label_stream_in_problem[OF infinite steps subset])
    have labeled: "relative_adp_selected_chain_labeled P A terms (path ?k)"
      using enumerate_in_set[OF infinite, of n]
      unfolding relative_adp_selected_label_indices_def by simp
    have not_P: "relative_adp_selected_label_stream P A terms path n \<notin> P"
      using not_main_at labeled
      unfolding relative_adp_selected_chain_main_event_iff_node_label
        relative_adp_selected_label_stream_def by simp
    show "relative_adp_selected_label_stream P A terms path n \<in> A - P"
      using in_A not_P by simp
  qed
  show thesis by (rule that[OF base])
qed

lemma relative_adp_selected_label_stream_eventual_component:
  assumes finite: "finite A"
    and infinite: "infinite (relative_adp_selected_label_indices P A terms path)"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains anchor N where
    "anchor \<in> A"
    "\<And>n. N \<le> n \<Longrightarrow>
      relative_adp_selected_label_stream P A terms path n \<in>
        relative_adp_dependency_component A anchor"
proof -
  let ?labels = "relative_adp_selected_label_stream P A terms path"
  let ?E = "relative_adp_dependency_graph A"
  have range: "range ?labels \<subseteq> A"
    using relative_adp_selected_label_stream_in_problem[OF infinite steps subset]
    by blast
  have edge: "\<And>n. (?labels n, ?labels (Suc n)) \<in> ?E"
  proof -
    fix n
    have source: "?labels n \<in> A" using range by blast
    have target: "?labels (Suc n) \<in> A" using range by blast
    have dependency: "relative_adp_dependency_edge A
        (?labels n) (?labels (Suc n))"
      by (rule relative_adp_selected_label_stream_dependency_edge[
          OF infinite path_edge steps subset lhs_fun])
    show "(?labels n, ?labels (Suc n)) \<in> ?E"
      using source target dependency
      unfolding relative_adp_dependency_graph_def by simp
  qed
  have witness: "\<exists>anchor N. anchor \<in> A \<and>
      (\<forall>n. N \<le> n \<longrightarrow> (anchor, ?labels n) \<in> ?E\<^sup>*) \<and>
      (\<forall>n. N \<le> n \<longrightarrow> (?labels n, anchor) \<in> ?E\<^sup>*)"
  proof (rule finite_ipath_has_eventual_mutual_anchor[
      where V=A and p="?labels" and E="?E", OF finite range edge])
    fix anchor N
    assume anchor: "anchor \<in> A"
      and forward: "\<And>n. N \<le> n \<Longrightarrow> (anchor, ?labels n) \<in> ?E\<^sup>*"
      and backward: "\<And>n. N \<le> n \<Longrightarrow> (?labels n, anchor) \<in> ?E\<^sup>*"
    show "\<exists>anchor N. anchor \<in> A \<and>
        (\<forall>n. N \<le> n \<longrightarrow> (anchor, ?labels n) \<in> ?E\<^sup>*) \<and>
        (\<forall>n. N \<le> n \<longrightarrow> (?labels n, anchor) \<in> ?E\<^sup>*)"
      by (rule exI[of _ anchor], rule exI[of _ N])
         (use anchor forward backward in blast)
  qed
  from witness obtain anchor N where anchor: "anchor \<in> A"
    and forward: "\<And>n. N \<le> n \<Longrightarrow> (anchor, ?labels n) \<in> ?E\<^sup>*"
    and backward: "\<And>n. N \<le> n \<Longrightarrow> (?labels n, anchor) \<in> ?E\<^sup>*"
    by blast
  have component: "\<And>n. N \<le> n \<Longrightarrow>
      ?labels n \<in> relative_adp_dependency_component A anchor"
    using range forward backward
    unfolding relative_adp_dependency_component_def by blast
  show thesis by (rule that[OF anchor component])
qed

lemma relative_adp_dependency_component_subset:
  "relative_adp_dependency_component A anchor \<subseteq> A"
  unfolding relative_adp_dependency_component_def by blast

lemma relative_adp_dependency_component_contains_anchor:
  assumes "anchor \<in> A"
  shows "anchor \<in> relative_adp_dependency_component A anchor"
  using assms unfolding relative_adp_dependency_component_def by simp

lemma relative_adp_dependency_component_connected:
  assumes p: "p \<in> relative_adp_dependency_component A anchor"
    and q: "q \<in> relative_adp_dependency_component A anchor"
  shows "(p,q) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    and "(q,p) \<in> (relative_adp_dependency_graph A)\<^sup>*"
proof -
  from p have p_to: "(p,anchor) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    and to_p: "(anchor,p) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    unfolding relative_adp_dependency_component_def by auto
  from q have q_to: "(q,anchor) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    and to_q: "(anchor,q) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    unfolding relative_adp_dependency_component_def by auto
  show "(p,q) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    by (rule rtrancl_trans[OF p_to to_q])
  show "(q,p) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    by (rule rtrancl_trans[OF q_to to_p])
qed

lemma relative_adp_dependency_component_maximal:
  assumes anchor: "anchor \<in> A"
    and pair: "pair \<in> A"
    and forward: "(anchor,pair) \<in> (relative_adp_dependency_graph A)\<^sup>*"
    and backward: "(pair,anchor) \<in> (relative_adp_dependency_graph A)\<^sup>*"
  shows "pair \<in> relative_adp_dependency_component A anchor"
  using assms unfolding relative_adp_dependency_component_def by simp

lemma relative_adp_selected_offshoot_path_has_branching_base_component:
  assumes A: "A = P \<union> B"
    and finite: "finite A"
    and offshoots: "INFM n. event_offshoot
      (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) path n"
    and no_main: "\<not> (INFM n.
      relative_adp_selected_chain_main_event P A terms (path n))"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains anchor where
    "anchor \<in> relative_adp_lasso_graph_problem P B"
    "\<exists>pair \<in>
      relative_adp_dependency_component
        (relative_adp_lasso_graph_problem P B) anchor \<inter> B.
      relative_adp_branching_pair pair"
proof -
  let ?I = "relative_adp_selected_label_indices P A terms path"
  let ?labels = "relative_adp_selected_label_stream P A terms path"
  let ?L = "relative_adp_lasso_graph_problem P B"
  have infinite: "infinite ?I"
    by (rule relative_adp_selected_offshoots_give_labeled_stream[
        OF offshoots path_edge steps subset])
  have base_witness: "\<exists>K. \<forall>n. K \<le> n \<longrightarrow> ?labels n \<in> A - P"
  proof (rule relative_adp_selected_no_main_eventual_base_stream[
      where P=P and A=A and terms=terms and path=path,
      OF infinite no_main steps subset])
    fix K
    assume base: "\<And>n. K \<le> n \<Longrightarrow> ?labels n \<in> A - P"
    show "\<exists>K. \<forall>n. K \<le> n \<longrightarrow> ?labels n \<in> A - P"
      by (rule exI[of _ K]) (use base in blast)
  qed
  from base_witness obtain K where base: "\<And>n. K \<le> n \<Longrightarrow>
      ?labels n \<in> A - P" by blast
  let ?shifted = "\<lambda>n. ?labels (K+n)"
  have finite_L: "finite ?L"
    using finite unfolding A relative_adp_lasso_graph_problem_def by simp
  have shifted_in_B: "\<And>n. ?shifted n \<in> B"
  proof -
    fix n
    have "?labels (K+n) \<in> A - P" by (rule base) simp
    then show "?shifted n \<in> B" unfolding A by blast
  qed
  have range: "range ?shifted \<subseteq> ?L"
    using shifted_in_B unfolding relative_adp_lasso_graph_problem_def by blast
  have edge: "\<And>n. (?shifted n, ?shifted (Suc n)) \<in>
      relative_adp_dependency_graph ?L"
  proof -
    fix n
    have original: "relative_adp_dependency_edge A
        (?labels (K+n)) (?labels (Suc (K+n)))"
      by (rule relative_adp_selected_label_stream_dependency_edge[
          OF infinite path_edge steps subset lhs_fun])
    have erased: "erase_annotations_adp ` A = erase_annotations_adp ` ?L"
      using relative_adp_lasso_graph_problem_erasure[of P B]
      unfolding A by simp
    have dependency: "relative_adp_dependency_edge ?L
        (?labels (K+n)) (?labels (Suc (K+n)))"
      using original relative_adp_dependency_edge_erasure_cong[OF erased]
      by simp
    have source: "?shifted n \<in> ?L" using range by blast
    have target: "?shifted (Suc n) \<in> ?L" using range by blast
    show "(?shifted n, ?shifted (Suc n)) \<in>
        relative_adp_dependency_graph ?L"
      using source target dependency
      unfolding relative_adp_dependency_graph_def by simp
  qed
  have witness: "\<exists>anchor N. anchor \<in> ?L \<and> (\<forall>n. N \<le> n \<longrightarrow>
      ?shifted n \<in> relative_adp_dependency_component ?L anchor)"
  proof (rule finite_ipath_has_eventual_mutual_anchor[
      where V="?L" and p="?shifted"
        and E="relative_adp_dependency_graph ?L", OF finite_L range edge])
    fix anchor N
    assume anchor: "anchor \<in> ?L"
      and forward: "\<And>n. N \<le> n \<Longrightarrow>
        (anchor, ?shifted n) \<in> (relative_adp_dependency_graph ?L)\<^sup>*"
      and backward: "\<And>n. N \<le> n \<Longrightarrow>
        (?shifted n, anchor) \<in> (relative_adp_dependency_graph ?L)\<^sup>*"
    have component: "\<And>n. N \<le> n \<Longrightarrow>
        ?shifted n \<in> relative_adp_dependency_component ?L anchor"
      using range forward backward
      unfolding relative_adp_dependency_component_def by blast
    show "\<exists>anchor N. anchor \<in> ?L \<and> (\<forall>n. N \<le> n \<longrightarrow>
        ?shifted n \<in> relative_adp_dependency_component ?L anchor)"
      by (rule exI[of _ anchor], rule exI[of _ N])
         (use anchor component in blast)
  qed
  from witness obtain anchor N where anchor: "anchor \<in> ?L"
    and component: "\<And>n. N \<le> n \<Longrightarrow>
      ?shifted n \<in> relative_adp_dependency_component ?L anchor"
    by blast
  have branching_stream: "INFM n. ?labels n \<in> A - P \<and>
      relative_adp_branching_pair (?labels n)"
    by (rule relative_adp_selected_offshoots_give_branching_base_stream[
        OF offshoots no_main path_edge steps subset lhs_fun])
  from branching_stream[unfolded INFM_nat]
  obtain m where large: "K+N < m"
    and branching: "?labels m \<in> A - P"
      "relative_adp_branching_pair (?labels m)" by blast
  let ?n = "m-K"
  have m: "m = K + ?n" using large by simp
  have Nn: "N \<le> ?n" using large by simp
  have shifted_component: "?labels (K+?n) \<in>
      relative_adp_dependency_component ?L anchor"
    by (rule component[OF Nn])
  have in_component: "?labels m \<in>
      relative_adp_dependency_component ?L anchor"
    using shifted_component m by simp
  have in_B: "?labels m \<in> B" using branching(1) unfolding A by blast
  have exists_branching: "\<exists>pair \<in>
      relative_adp_dependency_component ?L anchor \<inter> B.
      relative_adp_branching_pair pair"
    using in_component in_B branching(2) by blast
  show thesis by (rule that[OF anchor exists_branching])
qed

lemma relative_adp_selected_main_path_has_main_component:
  assumes finite: "finite A"
    and main: "INFM n.
      relative_adp_selected_chain_main_event P A terms (path n)"
    and path_edge: "\<And>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    and steps: "\<And>k. (terms k, terms (Suc k)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and lhs_fun: "\<And>pair. pair \<in> A \<Longrightarrow> is_Fun (fst pair)"
  obtains anchor N where
    "anchor \<in> A"
    "relative_adp_dependency_component A anchor \<inter> P \<noteq> {}"
    "\<And>n. N \<le> n \<Longrightarrow>
      relative_adp_selected_label_stream P A terms path n \<in>
        relative_adp_dependency_component A anchor"
proof -
  have label_infinite:
      "infinite (relative_adp_selected_label_indices P A terms path)"
  proof -
    have main_infinite:
        "infinite {n. relative_adp_selected_chain_main_event P A terms (path n)}"
      using main unfolding INFM_iff_infinite .
    have inclusion:
        "{n. relative_adp_selected_chain_main_event P A terms (path n)}
          \<subseteq> relative_adp_selected_label_indices P A terms path"
      unfolding relative_adp_selected_chain_main_event_iff_node_label
        relative_adp_selected_label_indices_def by blast
    show ?thesis by (rule infinite_super[OF inclusion main_infinite])
  qed
  have witness: "\<exists>anchor N. anchor \<in> A \<and> (\<forall>n. N \<le> n \<longrightarrow>
      relative_adp_selected_label_stream P A terms path n \<in>
        relative_adp_dependency_component A anchor)"
  proof (rule relative_adp_selected_label_stream_eventual_component[
      where P=P and A=A and terms=terms and path=path,
      OF finite label_infinite path_edge steps subset lhs_fun])
    fix anchor N
    assume anchor: "anchor \<in> A"
      and eventual: "\<And>n. N \<le> n \<Longrightarrow>
        relative_adp_selected_label_stream P A terms path n \<in>
          relative_adp_dependency_component A anchor"
    show "\<exists>anchor N. anchor \<in> A \<and> (\<forall>n. N \<le> n \<longrightarrow>
        relative_adp_selected_label_stream P A terms path n \<in>
          relative_adp_dependency_component A anchor)"
      by (rule exI[of _ anchor], rule exI[of _ N])
         (use anchor eventual in blast)
  qed
  from witness obtain anchor N where anchor: "anchor \<in> A"
    and eventual: "\<And>n. N \<le> n \<Longrightarrow>
      relative_adp_selected_label_stream P A terms path n \<in>
        relative_adp_dependency_component A anchor"
    by blast
  have main_stream: "INFM n.
      relative_adp_selected_label_stream P A terms path n \<in> P"
    by (rule relative_adp_selected_main_events_give_main_label_stream[OF main])
  from main_stream[unfolded INFM_nat]
  obtain n where Nn: "N < n"
    and in_P: "relative_adp_selected_label_stream P A terms path n \<in> P"
    by blast
  have in_component:
      "relative_adp_selected_label_stream P A terms path n \<in>
        relative_adp_dependency_component A anchor"
    by (rule eventual) (use Nn in simp)
  have intersects: "relative_adp_dependency_component A anchor \<inter> P \<noteq> {}"
    using in_component in_P by blast
  show thesis by (rule that[OF anchor intersects eventual])
qed

lemma finite_relative_adp_selected_chain_origin_successors:
  "finite {target. (source,target) \<in>
    relative_adp_selected_chain_origin_edge P A terms}"
proof (cases source)
  case (Pair i q)
  have subset: "{target. (source,target) \<in>
      relative_adp_selected_chain_origin_edge P A terms} \<subseteq>
      (\<lambda>q'. (Suc i,q')) ` sharp_positions (terms (Suc i))"
  proof
    fix target
    assume edge: "target \<in> {target. (source,target) \<in>
      relative_adp_selected_chain_origin_edge P A terms}"
    then obtain q' where target: "target = (Suc i,q')"
      and source_sharp: "q \<in> sharp_positions (terms i)"
      and origin: "let application = relative_adp_selected_application P A terms i in
        relative_adp_canonical_origin_edge A (fst application)
          (terms i) (terms (Suc i)) (fst (snd application))
          (snd (snd application)) q q'"
      unfolding Pair relative_adp_selected_chain_origin_edge_def
      by (auto simp: Let_def)
    have "q' \<in> sharp_positions (terms (Suc i))"
      using origin source_sharp
      by (auto intro: relative_adp_canonical_origin_edge_preserves_sharp
          simp: Let_def)
    then show "target \<in>
        (\<lambda>q'. (Suc i,q')) ` sharp_positions (terms (Suc i))"
      unfolding target by blast
  qed
  have "finite ((\<lambda>q'. (Suc i,q')) ` sharp_positions (terms (Suc i)))"
    unfolding sharp_positions_def
    by (rule finite_imageI, rule finite_subset[OF _ finite_poss]) auto
  then show ?thesis by (rule finite_subset[OF subset])
qed

lemma relative_adp_selected_chain_target_has_predecessor:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and target: "q' \<in> sharp_positions (terms (Suc i))"
  obtains q where
    "((i,q),(Suc i,q')) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
proof -
  let ?witness = "relative_adp_selected_step_witness P A terms i"
  let ?application = "relative_adp_selected_application P A terms i"
  have preferred: "relative_adp_preferred_step_witness_valid P A
      (terms i) (terms (Suc i)) ?witness"
    by (rule relative_adp_selected_step_witness_valid[OF step subset])
  then have valid: "relative_adp_step_witness_valid A
      (terms i) (terms (Suc i)) ?witness"
    unfolding relative_adp_preferred_step_witness_valid_def by simp
  from relative_adp_step_witness_sharp_position_has_predecessor[
      OF valid target]
  obtain q where source: "q \<in> sharp_positions (terms i)"
    and exact: "relative_adp_step_witness_origin_edge ?witness q q'" .
  have origin: "relative_adp_canonical_origin_edge A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application)) q q'"
    using relative_adp_step_witness_origin_is_canonical[OF valid exact]
    unfolding relative_adp_selected_application_def Let_def by simp
  show thesis
    by (rule that[where q = q])
       (use source origin exact in
        \<open>simp add: relative_adp_selected_chain_origin_edge_def Let_def\<close>)
qed

lemma relative_adp_selected_chain_marker_reachable_from_root:
  assumes steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and marked: "q \<in> sharp_positions (terms i)"
  shows "\<exists>root. root \<in> sharp_positions (terms 0) \<and>
    ((0,root),(i,q)) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
  using marked
proof (induction i arbitrary: q)
  case 0
  then show ?case by auto
next
  case (Suc i)
  from relative_adp_selected_chain_target_has_predecessor[
      OF steps subset Suc.prems]
  obtain predecessor where edge:
    "((i,predecessor),(Suc i,q)) \<in>
      relative_adp_selected_chain_origin_edge P A terms" .
  then have predecessor_marked:
      "predecessor \<in> sharp_positions (terms i)"
    unfolding relative_adp_selected_chain_origin_edge_def by auto
  from Suc.IH[OF predecessor_marked]
  obtain root where root: "root \<in> sharp_positions (terms 0)"
    and path: "((0,root),(i,predecessor)) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*" by blast
  have "((0,root),(Suc i,q)) \<in>
      (relative_adp_selected_chain_origin_edge P A terms)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF path edge])
  with root show ?case by blast
qed

lemma relative_adp_strict_index_is_selected_main_event:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and strict: "(terms i, terms (Suc i)) \<in> adp_step_case_rel P True"
  shows "relative_adp_selected_chain_main_event P A terms
    (i, snd (snd (relative_adp_selected_application P A terms i)))"
proof -
  have preferred: "relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i))
      (relative_adp_selected_application P A terms i)"
    by (rule relative_adp_selected_application_valid[OF step subset])
  show ?thesis
    using preferred strict
    unfolding relative_adp_selected_chain_main_event_def
      relative_adp_preferred_application_valid_def Let_def by simp
qed

lemma relative_adp_ideriv_infinite_selected_main_events:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  shows "infinite {node.
    relative_adp_selected_chain_main_event P A terms node}"
proof -
  let ?I = "{i. (terms i, terms (Suc i)) \<in>
    adp_step_case_rel P True}"
  let ?events = "{node.
    relative_adp_selected_chain_main_event P A terms node}"
  have infinite_I: "infinite ?I"
    using deriv unfolding ideriv_def INFM_iff_infinite by simp
  have projection: "?I \<subseteq> fst ` ?events"
  proof
    fix i
    assume i: "i \<in> ?I"
    then have strict: "(terms i, terms (Suc i)) \<in>
      adp_step_case_rel P True" by simp
    have step: "(terms i, terms (Suc i)) \<in> adp_step A"
      by (rule relative_adp_ideriv_chain_steps[OF deriv subset])
    have event: "relative_adp_selected_chain_main_event P A terms
        (i, snd (snd (relative_adp_selected_application P A terms i)))"
      by (rule relative_adp_strict_index_is_selected_main_event[
          OF step subset strict])
    then show "i \<in> fst ` ?events" by force
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> infinite ?events"
    then have "finite (fst ` ?events)" by simp
    then have "finite ?I" by (rule finite_subset[OF projection])
    with infinite_I show False by contradiction
  qed
qed

lemma relative_adp_selected_main_event_is_marked:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
    and event: "relative_adp_selected_chain_main_event P A terms (i,q)"
  shows "q \<in> sharp_positions (terms i)"
proof -
  let ?application = "relative_adp_selected_application P A terms i"
  have preferred: "relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i)) ?application"
    by (rule relative_adp_selected_application_valid[OF step subset])
  then have applied: "relative_adp_applied_at A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application))"
    unfolding relative_adp_preferred_application_valid_def
      relative_adp_application_valid_def by simp
  from event have sharp: "fst ?application"
    and q: "snd (snd ?application) = q"
    unfolding relative_adp_selected_chain_main_event_def Let_def by auto
  show ?thesis using applied sharp q
    unfolding relative_adp_applied_at_def by auto
qed

lemma relative_adp_ideriv_has_selected_heavy_root:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  obtains root where
    "root \<in> sharp_positions (terms 0)"
    "heavy_node (relative_adp_selected_chain_origin_edge P A terms)
      (relative_adp_selected_chain_main_event P A terms) (0,root)"
proof -
  let ?E = "relative_adp_selected_chain_origin_edge P A terms"
  let ?event = "relative_adp_selected_chain_main_event P A terms"
  let ?events = "{node. ?event node}"
  let ?roots = "sharp_positions (terms 0)"
  have steps: "\<And>i. (terms i, terms (Suc i)) \<in> adp_step A"
    by (rule relative_adp_ideriv_chain_steps[OF deriv subset])
  have infinite_events: "infinite ?events"
    by (rule relative_adp_ideriv_infinite_selected_main_events[OF deriv subset])
  have finite_roots: "finite ?roots"
    unfolding sharp_positions_def
    by (rule finite_subset[OF _ finite_poss]) auto
  have cover: "?events \<subseteq>
      \<Union>(reachable_events ?E ?event ` ((\<lambda>q. (0,q)) ` ?roots))"
  proof
    fix node
    assume node: "node \<in> ?events"
    obtain i q where node_eq: "node = (i,q)" by (cases node) auto
    have event: "?event (i,q)" using node unfolding node_eq by simp
    have marked: "q \<in> sharp_positions (terms i)"
      by (rule relative_adp_selected_main_event_is_marked[
          OF steps subset event])
    from relative_adp_selected_chain_marker_reachable_from_root[
        OF steps subset marked]
    obtain root where root: "root \<in> ?roots"
      and path: "((0,root),(i,q)) \<in> ?E\<^sup>*" by blast
    have "node \<in> reachable_events ?E ?event (0,root)"
      using node path unfolding node_eq reachable_events_def by simp
    with root show "node \<in>
        \<Union>(reachable_events ?E ?event ` ((\<lambda>q. (0,q)) ` ?roots))"
      by blast
  qed
  have heavy_root: "\<exists>root \<in> ?roots.
      heavy_node ?E ?event (0,root)"
  proof (rule ccontr)
    assume none: "\<not> (\<exists>root \<in> ?roots.
      heavy_node ?E ?event (0,root))"
    have finite_each: "\<And>root. root \<in> ?roots \<Longrightarrow>
        finite (reachable_events ?E ?event (0,root))"
      using none unfolding heavy_node_def by blast
    have finite_union:
        "finite (\<Union>(reachable_events ?E ?event `
          ((\<lambda>q. (0,q)) ` ?roots)))"
      using finite_roots finite_each by simp
    have "finite ?events" by (rule finite_subset[OF cover finite_union])
    with infinite_events show False by contradiction
  qed
  from heavy_root obtain root where root: "root \<in> ?roots"
    and heavy: "heavy_node ?E ?event (0,root)" by blast
  show thesis by (rule that[OF root heavy])
qed

theorem relative_adp_ideriv_selected_origin_dichotomy:
  assumes deriv: "ideriv (adp_step_case_rel P True) (adp_step A) terms"
    and subset: "P \<subseteq> A"
  obtains root path where
    "root \<in> sharp_positions (terms 0)"
    "\<forall>n. (path n, path (Suc n)) \<in>
      relative_adp_selected_chain_origin_edge P A terms"
    "(INFM n. relative_adp_selected_chain_main_event P A terms (path n)) \<or>
      (INFM n. event_offshoot
        (relative_adp_selected_chain_origin_edge P A terms)
        (relative_adp_selected_chain_main_event P A terms) path n)"
proof -
  let ?E = "relative_adp_selected_chain_origin_edge P A terms"
  let ?event = "relative_adp_selected_chain_main_event P A terms"
  from relative_adp_ideriv_has_selected_heavy_root[OF deriv subset]
  obtain root where root: "root \<in> sharp_positions (terms 0)"
    and heavy: "heavy_node ?E ?event (0,root)" .
  let ?path = "heavy_path ?E ?event (0,root)"
  from finite_branching_event_dichotomy[OF heavy]
  have dichotomy: "(\<forall>n. (?path n, ?path (Suc n)) \<in> ?E) \<and>
      ((INFM n. ?event (?path n)) \<or>
        (INFM n. event_offshoot ?E ?event ?path n))"
    by (simp add: finite_relative_adp_selected_chain_origin_successors)
  show thesis
    apply (rule that[where path = ?path, OF root])
    using dichotomy apply blast
    using dichotomy apply blast
    done
qed

end
