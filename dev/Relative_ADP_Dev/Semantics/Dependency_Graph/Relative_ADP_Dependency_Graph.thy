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

definition annotated_rhs_subterms ::
  "('f, 'v) adp \<Rightarrow> ('f adp_symbol, 'v) term set" where
  "annotated_rhs_subterms p = {snd p |_ q | q. q \<in> sharp_positions (snd p)}"

definition relative_adp_dependency_edge ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp \<Rightarrow> ('f, 'v) adp \<Rightarrow> bool" where
  "relative_adp_dependency_edge A p q \<longleftrightarrow>
    (\<exists>u \<in> annotated_rhs_subterms p. \<exists>sigma tau.
      (mark_adp_root u \<cdot> sigma, mark_adp_root (fst q) \<cdot> tau) \<in>
        (adp_step_case_rel (erase_annotations_adp ` A) False)\<^sup>*)"

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
  "relative_adp_selected_application P A terms i =
    (SOME application. relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i)) application)"

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

lemma relative_adp_selected_application_valid:
  assumes step: "(terms i, terms (Suc i)) \<in> adp_step A"
    and subset: "P \<subseteq> A"
  shows "relative_adp_preferred_application_valid P A
    (terms i) (terms (Suc i))
    (relative_adp_selected_application P A terms i)"
  unfolding relative_adp_selected_application_def
  by (rule someI_ex, rule adp_step_has_preferred_application[OF step subset])

definition relative_adp_selected_chain_origin_edge ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    (nat \<Rightarrow> ('f adp_symbol, 'v) term) \<Rightarrow> (nat \<times> pos) rel" where
  "relative_adp_selected_chain_origin_edge P A terms =
    {((i,q),(j,q')). j = Suc i \<and> q \<in> sharp_positions (terms i) \<and>
      (let application = relative_adp_selected_application P A terms i in
       relative_adp_canonical_origin_edge A (fst application)
        (terms i) (terms j) (fst (snd application))
        (snd (snd application)) q q')}"

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

lemma relative_adp_selected_chain_labeled_iff:
  "relative_adp_selected_chain_labeled P A terms (i,q) \<longleftrightarrow>
    (let application = relative_adp_selected_application P A terms i in
      fst application \<and> snd (snd application) = q)"
  unfolding relative_adp_selected_chain_labeled_def
    relative_adp_selected_chain_label_def
  by (auto simp: Let_def)

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
      unfolding Pair relative_adp_selected_chain_origin_edge_def by auto
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
  let ?application = "relative_adp_selected_application P A terms i"
  have preferred: "relative_adp_preferred_application_valid P A
      (terms i) (terms (Suc i)) ?application"
    by (rule relative_adp_selected_application_valid[OF step subset])
  then have applied: "relative_adp_applied_at A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application))"
    unfolding relative_adp_preferred_application_valid_def
      relative_adp_application_valid_def by simp
  from relative_adp_applied_at_sharp_position_has_predecessor[
      OF applied target]
  obtain q where source: "q \<in> sharp_positions (terms i)"
    and origin: "relative_adp_canonical_origin_edge A (fst ?application)
      (terms i) (terms (Suc i)) (fst (snd ?application))
      (snd (snd ?application)) q q'" .
  show thesis
    by (rule that[where q = q])
       (use source origin in
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
