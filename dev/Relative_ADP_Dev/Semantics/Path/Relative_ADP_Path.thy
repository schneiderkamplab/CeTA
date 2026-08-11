theory Relative_ADP_Path
  imports Relative_ADP_Origin_Dev.Relative_ADP_Origin
begin

text \<open>
  Experimental finite origin-path layer.  The local rewrite lifting API is
  frozen in the parent session; this child composes its position relations.
\<close>

lemma root_subt_replace_strictly_below:
  assumes p: "p \<in> poss s" and qp: "q <\<^sub>p p"
  shows "root (replace_at s p u |_ q) = root (s |_ q)"
  using p qp
proof (induct q arbitrary: s p)
  case Nil
  then obtain i p' where p: "p = i # p'" by (cases p) auto
  from Nil.prems(1) obtain f ts where s: "s = Fun f ts"
    by (cases s) (auto simp: p)
  from Nil.prems(1) have i: "i < length ts" unfolding s p by simp
  show ?case unfolding s p using i by simp
next
  case (Cons i q)
  from Cons.prems(2) obtain p' where p: "p = i # p'" and qp: "q <\<^sub>p p'"
    unfolding strict_prefix_def prefix_def by auto
  from Cons.prems(1) obtain f ts where s: "s = Fun f ts"
    and i: "i < length ts" and p': "p' \<in> poss (ts ! i)"
    unfolding p by (cases s) auto
  from Cons.hyps[OF p' qp]
  show ?case unfolding s p using i by (simp add: nth_append)
qed

lemma adp_defined_position_preserved_outside:
  assumes p: "p \<in> poss s"
    and q: "q \<in> adp_defined_positions D (replace_at s p u)"
    and outside: "q <\<^sub>p p \<or> q \<bottom> p"
  shows "q \<in> adp_defined_positions D s"
proof -
  from q obtain f ts where q_after: "q \<in> poss (replace_at s p u)"
    and q_at: "replace_at s p u |_ q = Fun f ts" and fD: "f \<in> D"
    unfolding adp_defined_positions_def by blast
  from outside show ?thesis
  proof
    assume qp: "q <\<^sub>p p"
    have q_before: "q \<in> poss s"
      using p qp prefix_order.less_imp_le poss_append_poss
      unfolding prefix_def by blast
    have root_after: "root (replace_at s p u |_ q) = Some (f, length ts)"
      using q_at by simp
    have root_before: "root (s |_ q) = Some (f, length ts)"
      using root_subt_replace_strictly_below[OF p qp] root_after by simp
    from root_before obtain us where "s |_ q = Fun f us"
      by (cases "s |_ q") auto
    with q_before fD show ?thesis unfolding adp_defined_positions_def by blast
  next
    assume parallel: "q \<bottom> p"
    have q_before: "q \<in> poss s"
      using q_after parallel_poss_replace_at[OF parallel_pos_sym[OF parallel] p]
      by simp
    have "s |_ q = Fun f ts"
      using q_at parallel_replace_at_subt_at[OF parallel_pos_sym[OF parallel] p q_before]
      by simp
    with q_before fD show ?thesis unfolding adp_defined_positions_def by blast
  qed
qed

lemma adp_defined_position_in_lhs_variable:
  assumes p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and rho: "rho \<in> var_poss l"
    and rho_x: "l |_ rho = Var x"
    and beta: "beta \<in> poss (sigma x)"
    and beta_at: "sigma x |_ beta = Fun f ts"
    and fD: "f \<in> D"
  shows "p @ rho @ beta \<in> adp_defined_positions D s"
proof -
  have rho_poss: "rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
  have rho_subst: "rho \<in> poss (l \<cdot> sigma)"
    using rho_poss by simp
  have rho_beta: "rho @ beta \<in> poss (l \<cdot> sigma)"
    using rho_poss rho_x beta by simp
  have source_poss: "p @ rho @ beta \<in> poss s"
    using p rho_beta by (simp only: poss_append_poss redex)
  have source_at: "s |_ (p @ rho @ beta) = Fun f ts"
  proof -
    have at_rho: "(l \<cdot> sigma) |_ rho = sigma x"
      using subt_at_subst[OF rho_poss, of sigma] rho_x by simp
    have split_source:
        "s |_ (p @ rho @ beta) = (s |_ p) |_ (rho @ beta)"
      by (rule subt_at_append[OF p])
    have split_redex:
        "(l \<cdot> sigma) |_ (rho @ beta) = ((l \<cdot> sigma) |_ rho) |_ beta"
      by (rule subt_at_append[OF rho_subst])
    have enter_redex:
        "(s |_ p) |_ (rho @ beta) = (l \<cdot> sigma) |_ (rho @ beta)"
      by (rule arg_cong[OF redex])
    have enter_argument:
        "((l \<cdot> sigma) |_ rho) |_ beta = sigma x |_ beta"
      by (rule arg_cong[OF at_rho])
    show ?thesis
      by (rule trans[OF split_source])
         (rule trans[OF enter_redex], rule trans[OF split_redex],
          rule trans[OF enter_argument], rule beta_at)
  qed
  show ?thesis
    unfolding adp_defined_positions_def mem_Collect_eq
  proof (rule conjI[OF source_poss], rule exI[of _ f], rule exI[of _ ts])
    show "s |_ (p @ rho @ beta) = Fun f ts \<and> f \<in> D"
      by (rule conjI[OF source_at fD])
  qed
qed

lemma replacement_variable_target_has_defined_subterm:
  assumes p: "p \<in> poss s"
    and q: "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    and q_eq: "q = p @ alpha @ beta"
    and alpha: "alpha \<in> var_poss r"
    and alpha_x: "r |_ alpha = Var x"
  obtains f ts where "sigma x |_ beta = Fun f ts" and "f \<in> D"
proof -
  from q obtain f ts where q_poss:
      "q \<in> poss (replace_at s p (r \<cdot> sigma))"
    and q_at: "replace_at s p (r \<cdot> sigma) |_ q = Fun f ts"
    and fD: "f \<in> D"
    unfolding adp_defined_positions_def by blast
  have p_after: "p \<in> poss (replace_at s p (r \<cdot> sigma))"
    by (rule replace_at_below_poss[OF p]) simp
  have alpha_poss: "alpha \<in> poss r"
    by (rule var_poss_imp_poss[OF alpha])
  have alpha_subst: "alpha \<in> poss (r \<cdot> sigma)"
    using alpha_poss by simp
  have split_target:
      "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ beta) =
        (replace_at s p (r \<cdot> sigma) |_ p) |_ (alpha @ beta)"
    by (rule subt_at_append[OF p_after])
  have replace_root:
      "replace_at s p (r \<cdot> sigma) |_ p = r \<cdot> sigma"
    by (rule replace_at_subt_at[OF p])
  have split_rhs:
      "(r \<cdot> sigma) |_ (alpha @ beta) = ((r \<cdot> sigma) |_ alpha) |_ beta"
    by (rule subt_at_append[OF alpha_subst])
  have at_alpha: "(r \<cdot> sigma) |_ alpha = sigma x"
    using subt_at_subst[OF alpha_poss, of sigma] alpha_x by simp
  have target_at: "sigma x |_ beta = Fun f ts"
  proof -
    have q_at':
        "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ beta) = Fun f ts"
      using q_at unfolding q_eq .
    have leave_root:
        "(replace_at s p (r \<cdot> sigma) |_ p) |_ (alpha @ beta) =
          (r \<cdot> sigma) |_ (alpha @ beta)"
      by (rule arg_cong[OF replace_root])
    have leave_alpha:
        "((r \<cdot> sigma) |_ alpha) |_ beta = sigma x |_ beta"
      by (rule arg_cong[OF at_alpha])
    show ?thesis
      by (rule sym, rule trans[OF sym[OF q_at']])
         (rule trans[OF split_target], rule trans[OF leave_root],
          rule trans[OF split_rhs], rule leave_alpha)
  qed
  show thesis by (rule that[OF target_at fD])
qed

lemma singleton_origin_root_target:
  assumes positive: "0 < n" and alpha: "alpha \<in> adp_defined_positions D r"
  shows "origin_root_targets n D r {alpha}"
proof -
  have nonempty_set: "adp_defined_positions D r \<noteq> {}"
  proof
    assume "adp_defined_positions D r = {}"
    with alpha show False by simp
  qed
  have nonempty: "0 < card (adp_defined_positions D r)"
    unfolding card_gt_0_iff
    by (rule conjI[OF nonempty_set finite_adp_defined_positions])
  show ?thesis
    unfolding origin_root_targets_def using positive nonempty alpha by simp
qed

lemma fun_position_below_instantiated_variable:
  assumes alpha: "alpha \<in> var_poss r"
    and alpha_x: "r |_ alpha = Var x"
    and beta: "beta \<in> fun_poss (sigma x)"
  shows "alpha @ beta \<in> fun_poss (r \<cdot> sigma)"
proof -
  have alpha_poss: "alpha \<in> poss r"
    by (rule var_poss_imp_poss[OF alpha])
  have alpha_subst: "alpha \<in> poss (r \<cdot> sigma)"
    using alpha_poss by simp
  have beta_poss: "beta \<in> poss (sigma x)"
    by (rule fun_poss_imp_poss[OF beta])
  have at_alpha: "(r \<cdot> sigma) |_ alpha = sigma x"
    using subt_at_subst[OF alpha_poss, of sigma] alpha_x by simp
  have combined_poss: "alpha @ beta \<in> poss (r \<cdot> sigma)"
    using alpha_subst beta_poss by (simp only: poss_append_poss at_alpha)
  obtain f ts where beta_at: "sigma x |_ beta = Fun f ts"
    using fun_poss_fun_conv[OF beta] by blast
  have split:
      "(r \<cdot> sigma) |_ (alpha @ beta) = ((r \<cdot> sigma) |_ alpha) |_ beta"
    by (rule subt_at_append[OF alpha_subst])
  have enter_argument:
      "((r \<cdot> sigma) |_ alpha) |_ beta = sigma x |_ beta"
    by (rule arg_cong[OF at_alpha])
  have combined_at: "(r \<cdot> sigma) |_ (alpha @ beta) = Fun f ts"
    by (rule trans[OF split], rule trans[OF enter_argument], rule beta_at)
  show ?thesis
    by (rule poss_is_Fun_fun_poss[OF combined_poss]) (use combined_at in simp)
qed

lemma replacement_defined_position_has_origin_predecessor:
  assumes p: "p \<in> poss s"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q: "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    and roots: "\<And>a. q = p @ a \<Longrightarrow>
      a \<in> adp_defined_positions D r \<Longrightarrow> a \<in> A"
    and transport: "\<And>x alpha beta. q = p @ alpha @ beta \<Longrightarrow>
      alpha \<in> var_poss r \<Longrightarrow> r |_ alpha = Var x \<Longrightarrow>
      beta \<in> fun_poss (sigma x) \<Longrightarrow>
      \<exists>rho. rho \<in> var_poss l \<and> l |_ rho = Var x \<and> phi rho = Some alpha"
  obtains q' where
    "q' \<in> adp_defined_positions D s"
    "origin_edge l r p sigma A phi q' q"
proof -
  from pos_cases[of p q]
  consider (below) "p \<le>\<^sub>p q"
    | (above) "q <\<^sub>p p"
    | (parallel) "p \<bottom> q"
    by blast
  then show thesis
  proof cases
    case below
    from replacement_defined_position_origin[OF p q below]
    show thesis
    proof cases
      case (1 a)
      have target: "a \<in> A" by (rule roots[OF 1])
      have edge: "origin_edge l r p sigma A phi p (p @ a)"
        by (rule origin_edge.root_target[OF target])
      show thesis
        by (rule that[OF p_defined]) (use edge 1(1) in simp)
    next
      case (2 x alpha beta)
      from transport[OF 2]
      obtain rho where rho: "rho \<in> var_poss l"
        and rho_x: "l |_ rho = Var x"
        and phi: "phi rho = Some alpha"
        by blast
      obtain f ts where beta_at: "sigma x |_ beta = Fun f ts" and fD: "f \<in> D"
        by (rule replacement_variable_target_has_defined_subterm[OF p q 2(1-3)])
      have beta_poss: "beta \<in> poss (sigma x)"
        using 2(4) by (rule fun_poss_imp_poss)
      have source: "p @ rho @ beta \<in> adp_defined_positions D s"
        by (rule adp_defined_position_in_lhs_variable[OF p redex rho rho_x
              beta_poss beta_at fD])
      have transported: "alpha @ beta \<in> fun_poss (r \<cdot> sigma)"
        by (rule fun_position_below_instantiated_variable[
              where alpha = alpha and r = r and x = x and beta = beta and sigma = sigma])
           (rule 2(2), rule 2(3), rule 2(4))
      have edge: "origin_edge l r p sigma A phi
          (p @ rho @ beta) (p @ alpha @ beta)"
        by (rule origin_edge.variable_transport[
              where rho = rho and l = l and phi = phi and alpha = alpha
                and beta = beta and r = r and sigma = sigma and p = p and A = A])
           (rule rho, rule phi, rule transported)
      show thesis
        by (rule that[OF source]) (use edge 2(1) in simp)
    qed
  next
    case above
    have source: "q \<in> adp_defined_positions D s"
      by (rule adp_defined_position_preserved_outside[OF p q]) (rule disjI1[OF above])
    have edge: "origin_edge l r p sigma A phi q q"
      by (rule origin_edge.preserved) (rule disjI1[OF above])
    show thesis by (rule that[OF source edge])
  next
    case parallel
    have qp: "q \<bottom> p" by (rule parallel_pos_sym[OF parallel])
    have source: "q \<in> adp_defined_positions D s"
      by (rule adp_defined_position_preserved_outside[OF p q]) (rule disjI2[OF qp])
    have edge: "origin_edge l r p sigma A phi q q"
      by (rule origin_edge.preserved) (rule disjI2[OF qp])
    show thesis by (rule that[OF source edge])
  qed
qed

definition target_root_positions ::
  "pos \<Rightarrow> pos \<Rightarrow> 'f set \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set" where
  "target_root_positions p q D r =
    {a \<in> adp_defined_positions D r. q = p @ a}"

lemma target_root_positions_subset:
  "target_root_positions p q D r \<subseteq> adp_defined_positions D r"
  unfolding target_root_positions_def by blast

lemma target_root_positions_card_le_one:
  "card (target_root_positions p q D r) \<le> 1"
proof -
  have singleton:
      "target_root_positions p q D r \<subseteq> {drop (length p) q}"
  proof
    fix a
    assume "a \<in> target_root_positions p q D r"
    then have "q = p @ a" unfolding target_root_positions_def by blast
    then have "a = drop (length p) q" by simp
    then show "a \<in> {drop (length p) q}" by simp
  qed
  have finite_target: "finite {drop (length p) q}" by simp
  have "card (target_root_positions p q D r) \<le>
      card {drop (length p) q}"
    by (rule card_mono[OF finite_target singleton])
  then show ?thesis by simp
qed

lemma paired_target_root_positions:
  shows "origin_root_targets 2 D r
    (target_root_positions p q1 D r \<union> target_root_positions p q2 D r)"
proof -
  let ?A = "target_root_positions p q1 D r \<union>
    target_root_positions p q2 D r"
  have subset: "?A \<subseteq> adp_defined_positions D r"
    using target_root_positions_subset by blast
  have at_most_two: "card ?A \<le> 2"
    using card_Un_le[of "target_root_positions p q1 D r"
        "target_root_positions p q2 D r"]
      target_root_positions_card_le_one[of p q1 D r]
      target_root_positions_card_le_one[of p q2 D r]
    by linarith
  have at_most_available: "card ?A \<le> card (adp_defined_positions D r)"
    by (rule card_mono[OF finite_adp_defined_positions subset])
  show ?thesis
    unfolding origin_root_targets_def
    using subset at_most_two at_most_available by simp
qed

lemma nonduplicating_rewrite_has_paired_origin_predecessors:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> poss s"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q1: "q1 \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    and q2: "q2 \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
  shows "origin_root_targets 2 D r
      (target_root_positions p q1 D r \<union> target_root_positions p q2 D r)"
    and "\<forall>q \<in> {q1, q2}. \<exists>q'.
      q' \<in> adp_defined_positions D s \<and>
      origin_edge l r p sigma
        (target_root_positions p q1 D r \<union> target_root_positions p q2 D r)
        (covering_vrf l r) q' q"
proof -
  let ?A = "target_root_positions p q1 D r \<union>
    target_root_positions p q2 D r"
  show "origin_root_targets 2 D r ?A"
    by (rule paired_target_root_positions)
  show "\<forall>q \<in> {q1, q2}. \<exists>q'.
      q' \<in> adp_defined_positions D s \<and>
      origin_edge l r p sigma ?A (covering_vrf l r) q' q"
  proof (intro ballI)
    fix q
    assume q_pair: "q \<in> {q1, q2}"
    have q_defined:
        "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    proof -
      from q_pair have "q = q1 \<or> q = q2" by simp
      then show ?thesis
      proof
        assume "q = q1"
        then show ?thesis by (rule ssubst) (rule q1)
      next
        assume "q = q2"
        then show ?thesis by (rule ssubst) (rule q2)
      qed
    qed
    obtain q' where source: "q' \<in> adp_defined_positions D s"
      and edge: "origin_edge l r p sigma ?A (covering_vrf l r) q' q"
    proof (rule replacement_defined_position_has_origin_predecessor[
          OF p p_defined redex q_defined])
      fix a
      assume qa: "q = p @ a" and a: "a \<in> adp_defined_positions D r"
      from q_pair show "a \<in> ?A"
        unfolding target_root_positions_def using qa a by auto
    next
      fix x alpha beta
      assume qa: "q = p @ alpha @ beta"
        and alpha: "alpha \<in> var_poss r"
        and alpha_x: "r |_ alpha = Var x"
        and beta: "beta \<in> fun_poss (sigma x)"
      let ?rho = "rhs_predecessor l r alpha"
      have rho: "?rho \<in> var_poss l"
        by (rule rhs_predecessor_properties(1)[OF nd alpha])
      have rho_x: "l |_ ?rho = Var x"
        using rhs_predecessor_properties(2)[OF nd alpha] alpha_x by simp
      have selected: "covering_vrf l r ?rho = Some alpha"
        by (rule covering_vrf_covers[OF nd alpha])
      show "\<exists>rho. rho \<in> var_poss l \<and> l |_ rho = Var x \<and>
          covering_vrf l r rho = Some alpha"
        by (rule exI[of _ ?rho], rule conjI[OF rho],
            rule conjI[OF rho_x selected])
    qed
    show "\<exists>q'. q' \<in> adp_defined_positions D s \<and>
        origin_edge l r p sigma ?A (covering_vrf l r) q' q"
      by (rule exI[of _ q'], rule conjI[OF source edge])
  qed
qed

lemma strict_rewrite_has_origin_predecessor:
  assumes vars: "vars_term r \<subseteq> vars_term l"
    and p: "p \<in> poss s"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q: "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
  obtains A phi q' where
    "origin_root_targets 1 D r A"
    "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    "q' \<in> adp_defined_positions D s"
    "origin_edge l r p sigma A phi q' q"
proof -
  from pos_cases[of p q]
  consider (below) "p \<le>\<^sub>p q"
    | (above) "q <\<^sub>p p"
    | (parallel) "p \<bottom> q"
    by blast
  then show thesis
  proof cases
    case below
    from replacement_defined_position_origin[OF p q below]
    show thesis
    proof cases
      case (1 a)
      have targets: "origin_root_targets 1 D r {a}"
        by (rule singleton_origin_root_target[OF zero_less_one 1(2)])
      have valid: "valid_vrf (plain_adp_term l, plain_adp_term r) (\<lambda>_. None)"
        by (rule empty_vrf_valid)
      have edge: "origin_edge l r p sigma {a} (\<lambda>_. None) p (p @ a)"
        by (rule origin_edge.root_target) simp
      show thesis
        by (rule that[OF targets valid p_defined]) (use edge 1(1) in simp)
    next
      case (2 x alpha beta)
      have x_rhs: "x \<in> vars_term r"
        unfolding vars_term_var_poss_iff
        by (rule exI[of _ alpha], rule conjI[OF 2(2)]) (rule sym[OF 2(3)])
      have x_lhs: "x \<in> vars_term l" by (rule subsetD[OF vars x_rhs])
      from x_lhs obtain rho where rho: "rho \<in> var_poss l"
        and rho_x': "Var x = l |_ rho"
        unfolding vars_term_var_poss_iff by blast
      have rho_x: "l |_ rho = Var x" by (rule sym[OF rho_x'])
      have same: "l |_ rho = r |_ alpha" using rho_x 2(3) by simp
      have valid: "valid_vrf (plain_adp_term l, plain_adp_term r)
          (singleton_vrf rho alpha)"
        by (rule singleton_vrf_valid[OF rho 2(2) same])
      obtain f ts where beta_at: "sigma x |_ beta = Fun f ts" and fD: "f \<in> D"
        by (rule replacement_variable_target_has_defined_subterm[OF p q 2(1-3)])
      have beta_poss: "beta \<in> poss (sigma x)"
        by (rule fun_poss_imp_poss[OF 2(4)])
      have source: "p @ rho @ beta \<in> adp_defined_positions D s"
        by (rule adp_defined_position_in_lhs_variable[OF p redex rho rho_x
              beta_poss beta_at fD])
      have selected: "singleton_vrf rho alpha rho = Some alpha"
        by (simp add: singleton_vrf_def)
      have transported: "alpha @ beta \<in> fun_poss (r \<cdot> sigma)"
        by (rule fun_position_below_instantiated_variable[
              where alpha = alpha and r = r and x = x and beta = beta and sigma = sigma])
           (rule 2(2), rule 2(3), rule 2(4))
      have edge: "origin_edge l r p sigma {} (singleton_vrf rho alpha)
          (p @ rho @ beta) (p @ alpha @ beta)"
        by (rule origin_edge.variable_transport[
              where rho = rho and l = l and phi = "singleton_vrf rho alpha"
                and alpha = alpha and beta = beta and r = r and sigma = sigma
                and p = p and A = "{}"])
           (rule rho, rule selected, rule transported)
      show thesis
        by (rule that[of "{}" "singleton_vrf rho alpha" "p @ rho @ beta"])
           (simp, rule valid, rule source, use edge 2(1) in simp)
    qed
  next
    case above
    have source: "q \<in> adp_defined_positions D s"
      by (rule adp_defined_position_preserved_outside[OF p q]) (rule disjI1[OF above])
    have edge: "origin_edge l r p sigma {} (\<lambda>_. None) q q"
      by (rule origin_edge.preserved) (rule disjI1[OF above])
    show thesis
      by (rule that[of "{}" "\<lambda>_. None" q])
         (simp, rule empty_vrf_valid, rule source, rule edge)
  next
    case parallel
    have qp: "q \<bottom> p" by (rule parallel_pos_sym[OF parallel])
    have source: "q \<in> adp_defined_positions D s"
      by (rule adp_defined_position_preserved_outside[OF p q]) (rule disjI2[OF qp])
    have edge: "origin_edge l r p sigma {} (\<lambda>_. None) q q"
      by (rule origin_edge.preserved) (rule disjI2[OF qp])
    show thesis
      by (rule that[of "{}" "\<lambda>_. None" q])
         (simp, rule empty_vrf_valid, rule source, rule edge)
  qed
qed

definition realizes_origin_relation ::
  "(pos \<Rightarrow> pos \<Rightarrow> bool) \<Rightarrow>
    ('f adp_symbol, 'v) term \<Rightarrow> ('f adp_symbol, 'v) term \<Rightarrow> bool" where
  "realizes_origin_relation E s t \<longleftrightarrow>
    (\<forall>p q. E p q \<longrightarrow>
      p \<in> sharp_positions s \<longrightarrow> q \<in> sharp_positions t)"

lemma realizes_origin_relationI:
  assumes "\<And>p q. E p q \<Longrightarrow>
    p \<in> sharp_positions s \<Longrightarrow> q \<in> sharp_positions t"
  shows "realizes_origin_relation E s t"
  using assms unfolding realizes_origin_relation_def by blast

lemma realizes_origin_relationD:
  assumes "realizes_origin_relation E s t"
    "E p q"
    "p \<in> sharp_positions s"
  shows "q \<in> sharp_positions t"
  using assms unfolding realizes_origin_relation_def by blast

lemma realizes_origin_relation_identity [simp]:
  "realizes_origin_relation (=) s s"
  unfolding realizes_origin_relation_def by blast

lemma realizes_origin_relation_comp:
  assumes "realizes_origin_relation E s t"
    "realizes_origin_relation F t u"
  shows "realizes_origin_relation (E OO F) s u"
proof (rule realizes_origin_relationI)
  fix p r
  assume "(E OO F) p r" and marked: "p \<in> sharp_positions s"
  then obtain q where Eq: "E p q" and Fq: "F q r" by blast
  from realizes_origin_relationD[OF assms(1) Eq marked]
  show "r \<in> sharp_positions u"
    by (rule realizes_origin_relationD[OF assms(2) Fq])
qed

fun origin_relations_comp ::
  "(pos \<Rightarrow> pos \<Rightarrow> bool) list \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool" where
  "origin_relations_comp [] = (=)"
| "origin_relations_comp (E # Es) = (E OO origin_relations_comp Es)"

lemma realizes_origin_relations_comp:
  assumes "length Es + 1 = length ts"
    "\<And>i. i < length Es \<Longrightarrow>
      realizes_origin_relation (Es ! i) (ts ! i) (ts ! Suc i)"
  shows "realizes_origin_relation (origin_relations_comp Es) (hd ts) (last ts)"
  using assms
proof (induct Es arbitrary: ts)
  case Nil
  then obtain t where "ts = [t]" by (cases ts) auto
  then show ?case by simp
next
  case (Cons E Es)
  then obtain s t us where ts: "ts = s # t # us"
    by (cases ts; cases "tl ts") auto
  have first: "realizes_origin_relation E s t"
    using Cons.prems(2)[of 0] unfolding ts by simp
  have len: "length Es + 1 = length (t # us)"
    using Cons.prems(1) unfolding ts by simp
  have rest: "\<And>i. i < length Es \<Longrightarrow>
      realizes_origin_relation (Es ! i) ((t # us) ! i) ((t # us) ! Suc i)"
  proof -
    fix i
    assume i: "i < length Es"
    have si: "Suc i < length (E # Es)" using i by simp
    from Cons.prems(2)[of "Suc i", OF si]
    show "realizes_origin_relation (Es ! i) ((t # us) ! i) ((t # us) ! Suc i)"
      unfolding ts by simp
  qed
  have tail: "realizes_origin_relation (origin_relations_comp Es) t (last (t # us))"
    using Cons.hyps[OF len rest] by simp
  from realizes_origin_relation_comp[OF first tail]
  show ?case unfolding ts by simp
qed

lemma canonical_nonduplicating_step_realizes_origin:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
    and nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
  obtains t where
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    "realizes_origin_relation
      (origin_edge l r p sigma A (covering_vrf l r)) s t"
proof (rule canonical_nonduplicating_origin_step[OF rule targets nd p redex])
  fix t
  assume erased:
      "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    and step:
      "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    and realizes: "\<forall>q q'.
      origin_edge l r p sigma A (covering_vrf l r) q q' \<longrightarrow>
      q \<in> sharp_positions s \<longrightarrow> q' \<in> sharp_positions t"
  have relation: "realizes_origin_relation
      (origin_edge l r p sigma A (covering_vrf l r)) s t"
    by (rule realizes_origin_relationI) (use realizes in blast)
  show thesis by (rule that[OF erased step relation])
qed

lemma canonical_strict_step_realizes_origin:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
    and vrf: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
  obtains t where
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    "realizes_origin_relation (origin_edge l r p sigma A phi) s t"
proof (rule canonical_strict_origin_step[OF rule targets vrf p redex])
  fix t
  assume erased:
      "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    and step:
      "adp_step_case (canonical_adps n D R) (p \<in> sharp_positions s) s t"
    and realizes: "\<forall>q q'. origin_edge l r p sigma A phi q q' \<longrightarrow>
      q \<in> sharp_positions s \<longrightarrow> q' \<in> sharp_positions t"
  have relation:
      "realizes_origin_relation (origin_edge l r p sigma A phi) s t"
    by (rule realizes_origin_relationI) (use realizes in blast)
  show thesis by (rule that[OF erased step relation])
qed

end
