theory Relative_ADP_Dependency_Graph
  imports Relative_ADP_Processors_Dev.Relative_ADP_Processors
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
    ('f, 'v) adp \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool" where
  "relative_adp_canonical_origin_edge P at_sharp s t pair q q' \<longleftrightarrow>
    (\<exists>l r phi p sigma A.
      pair = (l,r) \<and> (l,r) \<in> P \<and>
      plain_adp_term_pred l \<and> valid_vrf (l,r) phi \<and>
      p \<in> fun_poss s \<and> at_sharp = (p \<in> sharp_positions s) \<and>
      erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma \<and>
      A = (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ p) \<and>
      t = replace_at s p
        (annotate_term A (erase_adp_term r \<cdot> sigma)) \<and>
      origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
        (if at_sharp then sharp_positions r else {}) phi q q')"

lemma relative_adp_canonical_origin_edge_is_step:
  assumes edge:
    "relative_adp_canonical_origin_edge P at_sharp s t pair q q'"
  shows "adp_step_case P at_sharp s t"
  using edge unfolding relative_adp_canonical_origin_edge_def
  by (auto intro: adp_step_case.adp_stepI)

lemma relative_adp_canonical_origin_edge_preserves_sharp:
  assumes edge:
      "relative_adp_canonical_origin_edge P at_sharp s t pair q q'"
    and source: "q \<in> sharp_positions s"
  shows "q' \<in> sharp_positions t"
proof -
  from edge obtain l r phi p sigma A where
      p: "p \<in> fun_poss s"
    and at: "at_sharp = (p \<in> sharp_positions s)"
    and A: "A = (if at_sharp then sharp_positions r else {}) \<union>
      transported_annotations phi l (s |_ p)"
    and t: "t = replace_at s p
      (annotate_term A (erase_adp_term r \<cdot> sigma))"
    and origin: "origin_edge (erase_adp_term l) (erase_adp_term r)
      p sigma (if at_sharp then sharp_positions r else {}) phi q q'"
    unfolding relative_adp_canonical_origin_edge_def by blast
  have p_poss: "p \<in> poss s" by (rule fun_poss_imp_poss[OF p])
  from origin show ?thesis
  proof cases
    case preserved
    have q': "q' = q" using preserved by simp
    have outside: "q <\<^sub>p p \<or> q \<bottom> p" using preserved by simp
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
    have local_source: "rho @ beta \<in> sharp_positions (s |_ p)"
      using source variable_transport
        sharp_positions_below_iff[OF p_poss, of "rho @ beta"]
      by simp
    have transported: "alpha @ beta \<in>
      transported_annotations phi l (s |_ p)"
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
    P at_sharp s t pair q q'}"
proof (rule finite_subset[of _ "sharp_positions t"])
  show "{q'. relative_adp_canonical_origin_edge
      P at_sharp s t pair q q'} \<subseteq> sharp_positions t"
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
      relative_adp_canonical_origin_edge P True s t pair p (p @ alpha)"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  have p_sharp: "p \<in> sharp_positions s" using adp_stepI(5) by simp
  have roots: "\<forall>alpha \<in> sharp_positions r.
      relative_adp_canonical_origin_edge P True s t (l,r) p (p @ alpha)"
  proof (intro ballI)
    fix alpha
    assume alpha: "alpha \<in> sharp_positions r"
    show "relative_adp_canonical_origin_edge P True s t
      (l,r) p (p @ alpha)"
      unfolding relative_adp_canonical_origin_edge_def
      apply (rule exI[where x = l])
      apply (rule exI[where x = r])
      apply (rule exI[where x = phi])
      apply (rule exI[where x = p])
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
      relative_adp_canonical_origin_edge P True s t (l,r) p (p @ alpha)"
      using roots by simp
  qed
qed

lemma adp_pr_step_has_a_labeled_root_origin:
  assumes step: "adp_step_case P True s t"
    and annotated: "\<forall>pair \<in> P. sharp_positions (snd pair) \<noteq> {}"
  obtains pair p q where
    "pair \<in> P"
    "p \<in> sharp_positions s"
    "relative_adp_canonical_origin_edge P True s t pair p q"
proof (rule adp_pr_step_has_labeled_root_origins[OF step])
  fix pair p
  assume pair: "pair \<in> P"
    and p: "p \<in> sharp_positions s"
    and roots: "\<forall>alpha \<in> sharp_positions (snd pair).
      relative_adp_canonical_origin_edge P True s t pair p (p @ alpha)"
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
  obtains pair q where
    "pair \<in> P"
    "q \<in> sharp_positions s"
    "relative_adp_canonical_origin_edge P at_sharp s t pair q q'"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  have p_poss: "p \<in> poss s"
    by (rule fun_poss_imp_poss[OF adp_stepI(4)])
  have canonical:
    "\<And>q. origin_edge (erase_adp_term l) (erase_adp_term r) p sigma
        (if at_sharp then sharp_positions r else {}) phi q q' \<Longrightarrow>
      relative_adp_canonical_origin_edge P at_sharp s t (l,r) q q'"
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

end
