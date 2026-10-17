theory Relative_ADP_Nontermination
  imports Relative_ADP_Path_Dev.Relative_ADP_Path
begin

text \<open>
  Experimental semantic invariant for the hard direction of the relative ADP
  chain criterion.  The checked origin-path API remains frozen in the parent
  session; this child records which defined subterms are relatively
  nonterminating and pulls those positions backwards through rewrite events.
\<close>

definition nonterminating_defined_positions ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> pos set" where
  "nonterminating_defined_positions R B D t =
    {p \<in> adp_defined_positions D t.
      \<not> SN_on (relstep R B) {t |_ p}}"

lemma nontermination_backwards_rewrite:
  assumes step: "(s, t) \<in> rstep R \<union> rstep B"
    and target: "\<not> SN_on (relstep R B) {t}"
  shows "\<not> SN_on (relstep R B) {s}"
proof
  assume source: "SN_on (relstep R B) {s}"
  from step_preserves_SN_on_relto[OF step source]
  show False using target by simp
qed

lemma nontermination_lifts_from_subterm:
  assumes subterm: "t \<unrhd> u"
    and target: "\<not> SN_on (relstep R B) {u}"
  shows "\<not> SN_on (relstep R B) {t}"
proof
  assume source: "SN_on (relstep R B) {t}"
  from subterm_preserves_SN_on_relstep[OF source subterm]
  show False using target by simp
qed

lemma minimal_nonterminating_defined_positions_root:
  assumes minimal: "t \<in> Tinf (relstep R B)"
    and root_defined: "[] \<in> adp_defined_positions D t"
  shows "nonterminating_defined_positions R B D t = {[]}"
proof (rule equalityI)
  show "nonterminating_defined_positions R B D t \<subseteq> {[]}"
  proof
    fix p
    assume p_nt: "p \<in> nonterminating_defined_positions R B D t"
    then have p_defined: "p \<in> adp_defined_positions D t"
      and p_nonterminating: "\<not> SN_on (relstep R B) {t |_ p}"
      unfolding nonterminating_defined_positions_def by auto
    have p_poss: "p \<in> poss t"
      using p_defined unfolding adp_defined_positions_def by auto
    show "p \<in> {[]}"
    proof (cases p)
      case Nil
      then show ?thesis by simp
    next
      case (Cons i p')
      have proper: "t \<rhd> t |_ p"
        unfolding Cons by (rule subt_at_nepos_imp_supt) (use p_poss Cons in simp)
      from minimal have "SN_on (relstep R B) {t |_ p}"
        unfolding Tinf_def using proper by blast
      with p_nonterminating show ?thesis by contradiction
    qed
  qed
  show "{[]} \<subseteq> nonterminating_defined_positions R B D t"
  proof
    fix p :: pos
    assume "p \<in> {[]}"
    then have p: "p = []" by simp
    from minimal have "\<not> SN_on (relstep R B) {t}"
      unfolding Tinf_def by blast
    with root_defined show "p \<in> nonterminating_defined_positions R B D t"
      unfolding nonterminating_defined_positions_def p by simp
  qed
qed

lemma valid_vrf_plain_selected:
  assumes valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and rho: "rho \<in> var_poss l"
    and selected: "phi rho = Some alpha"
  shows "alpha \<in> var_poss r" and "l |_ rho = r |_ alpha"
proof -
  have rho_plain: "rho \<in> var_poss (plain_adp_term l)" using rho by simp
  from valid have selected_plain:
      "alpha \<in> var_poss (plain_adp_term r) \<and>
        plain_adp_term l |_ rho = plain_adp_term r |_ alpha"
    unfolding valid_vrf_def fst_conv snd_conv
    using rho_plain selected by force
  then show "alpha \<in> var_poss r" by simp
  have rho_poss: "rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
  have alpha_poss: "alpha \<in> poss r"
    by (rule var_poss_imp_poss) (use selected_plain in simp)
  have plain_eq: "plain_adp_term (l |_ rho) = plain_adp_term (r |_ alpha)"
    using selected_plain plain_adp_term_subt_at[OF rho_poss]
      plain_adp_term_subt_at[OF alpha_poss] by simp
  have "erase_adp_term (plain_adp_term (l |_ rho)) =
      erase_adp_term (plain_adp_term (r |_ alpha))"
    by (rule arg_cong[OF plain_eq])
  then show "l |_ rho = r |_ alpha" by simp
qed

lemma rewrite_below_position:
  assumes rule: "(l, r) \<in> B"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q_below: "q \<le>\<^sub>p p"
  shows "(s |_ q, replace_at s p (r \<cdot> sigma) |_ q) \<in> rstep B"
proof -
  from prefixE[OF q_below] obtain d where p_eq: "p = q @ d" by blast
  have full: "(s, replace_at s p (r \<cdot> sigma)) \<in>
      qrstep_r_p_s False {} B (l, r) p sigma"
    unfolding qrstep_r_p_s_def
    using rule p redex by simp
  have local: "(s |_ q, replace_at s p (r \<cdot> sigma) |_ q) \<in>
      qrstep_r_p_s False {} B (l, r) d sigma"
    unfolding p_eq
    by (rule qrstep_subt_at_gen[OF full[unfolded p_eq]])
  have "(s |_ q, replace_at s p (r \<cdot> sigma) |_ q) \<in>
      qrstep False {} B"
    unfolding qrstep_qrstep_r_p_s_conv by (rule exI[of _ "(l, r)"],
      rule exI[of _ d], rule exI[of _ sigma], rule local)
  then show ?thesis by simp
qed

lemma lhs_variable_subterm:
  assumes p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and rho: "rho \<in> poss l"
    and rho_x: "l |_ rho = Var x"
    and beta: "beta \<in> poss (sigma x)"
  shows "s |_ (p @ rho @ beta) = sigma x |_ beta"
proof -
  have rho_subst: "rho \<in> poss (l \<cdot> sigma)" using rho by simp
  have split_source:
      "s |_ (p @ rho @ beta) = (s |_ p) |_ (rho @ beta)"
    by (rule subt_at_append[OF p])
  have split_redex:
      "(l \<cdot> sigma) |_ (rho @ beta) = ((l \<cdot> sigma) |_ rho) |_ beta"
    by (rule subt_at_append[OF rho_subst])
  have at_rho: "(l \<cdot> sigma) |_ rho = sigma x"
    using subt_at_subst[OF rho, of sigma] rho_x by simp
  have enter_redex:
      "(s |_ p) |_ (rho @ beta) = (l \<cdot> sigma) |_ (rho @ beta)"
    by (rule arg_cong[OF redex])
  have enter_argument:
      "((l \<cdot> sigma) |_ rho) |_ beta = sigma x |_ beta"
    by (rule arg_cong[OF at_rho])
  show ?thesis
    by (rule trans[OF split_source], rule trans[OF enter_redex],
        rule trans[OF split_redex], rule enter_argument)
qed

lemma replacement_variable_subterm:
  assumes p: "p \<in> poss s"
    and alpha: "alpha \<in> poss r"
    and alpha_x: "r |_ alpha = Var x"
    and beta: "beta \<in> poss (sigma x)"
  shows "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ beta) = sigma x |_ beta"
proof -
  have p_after: "p \<in> poss (replace_at s p (r \<cdot> sigma))"
    by (rule replace_at_below_poss[OF p]) simp
  have alpha_subst: "alpha \<in> poss (r \<cdot> sigma)" using alpha by simp
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
    using subt_at_subst[OF alpha, of sigma] alpha_x by simp
  have leave_root:
      "(replace_at s p (r \<cdot> sigma) |_ p) |_ (alpha @ beta) =
        (r \<cdot> sigma) |_ (alpha @ beta)"
    by (rule arg_cong[OF replace_root])
  have leave_alpha:
      "((r \<cdot> sigma) |_ alpha) |_ beta = sigma x |_ beta"
    by (rule arg_cong[OF at_alpha])
  show ?thesis
    by (rule trans[OF split_target], rule trans[OF leave_root],
        rule trans[OF split_rhs], rule leave_alpha)
qed

lemma origin_edge_preserves_nontermination_backwards:
  assumes rule: "(l, r) \<in> R \<union> B"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and edge: "origin_edge l r p sigma A phi q' q"
    and target: "q \<in> nonterminating_defined_positions R B D
      (replace_at s p (r \<cdot> sigma))"
  shows "\<not> SN_on (relstep R B) {s |_ q'}"
proof -
  from target have target_defined:
      "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    and target_nonterminating:
      "\<not> SN_on (relstep R B) {replace_at s p (r \<cdot> sigma) |_ q}"
    unfolding nonterminating_defined_positions_def by auto
  have target_poss: "q \<in> poss (replace_at s p (r \<cdot> sigma))"
    using target_defined unfolding adp_defined_positions_def by auto
  from edge show ?thesis
  proof cases
    case preserved
    have q_eq: "q = q'" using preserved by simp
    have outside: "q' <\<^sub>p p \<or> q' \<bottom> p" using preserved by simp
    from outside show ?thesis
    proof
      assume above: "q' <\<^sub>p p"
      have local_step:
          "(s |_ q', replace_at s p (r \<cdot> sigma) |_ q')
            \<in> rstep R \<union> rstep B"
        unfolding rstep_union[symmetric]
        by (rule rewrite_below_position[OF rule p redex
              prefix_order.less_imp_le[OF above]])
      have target_at_q':
          "\<not> SN_on (relstep R B) {replace_at s p (r \<cdot> sigma) |_ q'}"
        using target_nonterminating q_eq by simp
      show ?thesis
        by (rule nontermination_backwards_rewrite[OF _ target_at_q'])
           (rule local_step)
    next
      assume parallel: "q' \<bottom> p"
      have source_poss: "q' \<in> poss s"
        using target_poss q_eq parallel
          parallel_poss_replace_at[OF parallel_pos_sym[OF parallel] p]
        by simp
      have unchanged:
          "replace_at s p (r \<cdot> sigma) |_ q' = s |_ q'"
        by (rule parallel_replace_at_subt_at[
              OF parallel_pos_sym[OF parallel] p source_poss])
      show ?thesis using target_nonterminating q_eq unchanged by simp
    qed
  next
    case (root_target alpha)
    have p_after: "p \<in> poss (replace_at s p (r \<cdot> sigma))"
      by (rule replace_at_below_poss[OF p]) simp
    have replace_root:
        "replace_at s p (r \<cdot> sigma) |_ p = r \<cdot> sigma"
      by (rule replace_at_subt_at[OF p])
    have alpha_poss: "alpha \<in> poss (r \<cdot> sigma)"
      using target_poss root_target p_after replace_root
      by (simp only: poss_append_poss)
    have target_at:
        "replace_at s p (r \<cdot> sigma) |_ (p @ alpha) =
          (r \<cdot> sigma) |_ alpha"
      by (rule trans[OF subt_at_append[OF p_after]],
          rule arg_cong[OF replace_root])
    have rhs_sub_nonterminating:
        "\<not> SN_on (relstep R B) {(r \<cdot> sigma) |_ alpha}"
      using target_nonterminating root_target target_at by simp
    have rhs_nonterminating: "\<not> SN_on (relstep R B) {r \<cdot> sigma}"
      by (rule nontermination_lifts_from_subterm[
            OF subt_at_imp_supteq[OF alpha_poss] rhs_sub_nonterminating])
    have root_step: "(l \<cdot> sigma, r \<cdot> sigma) \<in> rstep R \<union> rstep B"
      unfolding rstep_union[symmetric]
      by (rule rstep_r_p_s_imp_rstep[where r = "(l, r)" and p = "[]" and \<sigma> = sigma])
         (use rule in \<open>auto simp: rstep_r_p_s_def'\<close>)
    have lhs_nonterminating: "\<not> SN_on (relstep R B) {l \<cdot> sigma}"
      by (rule nontermination_backwards_rewrite[OF root_step rhs_nonterminating])
    show ?thesis using root_target redex lhs_nonterminating by simp
  next
    case (variable_transport rho alpha beta)
    have source_eq: "q' = p @ rho @ beta" by fact
    have target_eq: "q = p @ alpha @ beta" by fact
    have rho_member: "rho \<in> var_poss l" by fact
    have selected: "phi rho = Some alpha" by fact
    have transported: "alpha @ beta \<in> fun_poss (r \<cdot> sigma)" by fact
    from valid_vrf_plain_selected[OF valid rho_member selected]
    have alpha: "alpha \<in> var_poss r" and same: "l |_ rho = r |_ alpha"
      by blast+
    from rho_member obtain x where rho_poss: "rho \<in> poss l"
      and rho_x: "l |_ rho = Var x"
      unfolding var_poss_iff by blast
    have alpha_poss: "alpha \<in> poss r"
      by (rule var_poss_imp_poss[OF alpha])
    have alpha_x: "r |_ alpha = Var x" using same rho_x by simp
    have alpha_subst: "alpha \<in> poss (r \<cdot> sigma)" using alpha_poss by simp
    have at_alpha: "(r \<cdot> sigma) |_ alpha = sigma x"
      using subt_at_subst[OF alpha_poss, of sigma] alpha_x by simp
    have alpha_beta_poss: "alpha @ beta \<in> poss (r \<cdot> sigma)"
      by (rule fun_poss_imp_poss[OF transported])
    have beta_poss: "beta \<in> poss (sigma x)"
      using alpha_beta_poss alpha_subst by (simp only: poss_append_poss at_alpha)
    have source_at: "s |_ (p @ rho @ beta) = sigma x |_ beta"
      by (rule lhs_variable_subterm[
            where p = p and s = s and l = l and sigma = sigma and rho = rho
              and x = x and beta = beta])
         (rule p, rule redex, rule rho_poss, rule rho_x, rule beta_poss)
    have target_at:
        "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ beta) = sigma x |_ beta"
      by (rule replacement_variable_subterm[
            where p = p and s = s and r = r and sigma = sigma and alpha = alpha
              and x = x and beta = beta])
         (rule p, rule alpha_poss, rule alpha_x, rule beta_poss)
    show ?thesis
      using target_nonterminating source_eq target_eq source_at target_at by simp
  qed
qed

lemma nonduplicating_weak_rewrite_pulls_back_pair:
  assumes rule: "(l, r) \<in> B"
    and nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> poss s"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q1: "q1 \<in> nonterminating_defined_positions R B D
      (replace_at s p (r \<cdot> sigma))"
    and q2: "q2 \<in> nonterminating_defined_positions R B D
      (replace_at s p (r \<cdot> sigma))"
  shows "origin_root_targets 2 D r
      (target_root_positions p q1 D r \<union> target_root_positions p q2 D r)"
    and "\<forall>q \<in> {q1, q2}. \<exists>q'.
      q' \<in> nonterminating_defined_positions R B D s \<and>
      origin_edge l r p sigma
        (target_root_positions p q1 D r \<union> target_root_positions p q2 D r)
        (covering_vrf l r) q' q"
proof -
  have q1_defined:
      "q1 \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    using q1 unfolding nonterminating_defined_positions_def by auto
  have q2_defined:
      "q2 \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    using q2 unfolding nonterminating_defined_positions_def by auto
  note origins = nonduplicating_rewrite_has_paired_origin_predecessors[
    OF nd p p_defined redex q1_defined q2_defined]
  show "origin_root_targets 2 D r
      (target_root_positions p q1 D r \<union> target_root_positions p q2 D r)"
    by (rule origins(1))
  let ?A = "target_root_positions p q1 D r \<union>
    target_root_positions p q2 D r"
  show "\<forall>q \<in> {q1, q2}. \<exists>q'.
      q' \<in> nonterminating_defined_positions R B D s \<and>
      origin_edge l r p sigma ?A (covering_vrf l r) q' q"
  proof (intro ballI)
    fix q
    assume q_pair: "q \<in> {q1, q2}"
    from origins(2) q_pair obtain q' where source_defined:
        "q' \<in> adp_defined_positions D s"
      and edge: "origin_edge l r p sigma ?A (covering_vrf l r) q' q"
      by blast
    have q_nt: "q \<in> nonterminating_defined_positions R B D
        (replace_at s p (r \<cdot> sigma))"
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
    have source_nonterminating: "\<not> SN_on (relstep R B) {s |_ q'}"
      by (rule origin_edge_preserves_nontermination_backwards[
            OF UnI2[OF rule] p redex covering_vrf_valid[OF nd] edge q_nt])
    have source: "q' \<in> nonterminating_defined_positions R B D s"
      unfolding nonterminating_defined_positions_def mem_Collect_eq
      by (rule conjI[OF source_defined source_nonterminating])
    show "\<exists>q'. q' \<in> nonterminating_defined_positions R B D s \<and>
        origin_edge l r p sigma ?A (covering_vrf l r) q' q"
      by (rule exI[of _ q'], rule conjI[OF source edge])
  qed
qed

lemma strict_rewrite_pulls_back_target:
  assumes rule: "(l, r) \<in> R"
    and vars: "vars_term r \<subseteq> vars_term l"
    and p: "p \<in> poss s"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q: "q \<in> nonterminating_defined_positions R B D
      (replace_at s p (r \<cdot> sigma))"
  obtains A phi q' where
    "origin_root_targets 1 D r A"
    "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    "q' \<in> nonterminating_defined_positions R B D s"
    "origin_edge l r p sigma A phi q' q"
proof -
  have q_defined:
      "q \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    using q unfolding nonterminating_defined_positions_def by auto
  obtain A phi q' where targets: "origin_root_targets 1 D r A"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and source_defined: "q' \<in> adp_defined_positions D s"
    and edge: "origin_edge l r p sigma A phi q' q"
    by (rule strict_rewrite_has_origin_predecessor[
          OF vars p p_defined redex q_defined])
  have source_nonterminating: "\<not> SN_on (relstep R B) {s |_ q'}"
    by (rule origin_edge_preserves_nontermination_backwards[
          OF UnI1[OF rule] p redex valid edge q])
  have source: "q' \<in> nonterminating_defined_positions R B D s"
    unfolding nonterminating_defined_positions_def mem_Collect_eq
    by (rule conjI[OF source_defined source_nonterminating])
  show thesis by (rule that[OF targets valid source edge])
qed

lemma canonical_nonduplicating_step_marks_pair:
  assumes rule: "(l, r) \<in> B"
    and targets: "origin_root_targets 2 D r A"
    and nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
    and edge1: "origin_edge l r p sigma A (covering_vrf l r) q1' q1"
    and edge2: "origin_edge l r p sigma A (covering_vrf l r) q2' q2"
    and marked1: "q1' \<in> sharp_positions s"
    and marked2: "q2' \<in> sharp_positions s"
  obtains t where
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps 2 D B) (p \<in> sharp_positions s) s t"
    "q1 \<in> sharp_positions t"
    "q2 \<in> sharp_positions t"
proof -
  obtain t where erased:
      "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    and step: "adp_step_case (canonical_adps 2 D B)
      (p \<in> sharp_positions s) s t"
    and realizes: "realizes_origin_relation
      (origin_edge l r p sigma A (covering_vrf l r)) s t"
    by (rule canonical_nonduplicating_step_realizes_origin[
          OF rule targets nd p redex])
  have q1: "q1 \<in> sharp_positions t"
    by (rule realizes_origin_relationD[OF realizes edge1 marked1])
  have q2: "q2 \<in> sharp_positions t"
    by (rule realizes_origin_relationD[OF realizes edge2 marked2])
  show thesis by (rule that[OF erased step q1 q2])
qed

lemma canonical_strict_step_marks_target:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets 1 D r A"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and p: "p \<in> fun_poss s"
    and redex: "erase_adp_term (s |_ p) = l \<cdot> sigma"
    and edge: "origin_edge l r p sigma A phi q' q"
    and root_marked: "p \<in> sharp_positions s"
    and predecessor_marked: "q' \<in> sharp_positions s"
  obtains t where
    "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    "adp_step_case (canonical_adps 1 D R) True s t"
    "q \<in> sharp_positions t"
proof -
  obtain t where erased:
      "erase_adp_term t = replace_at (erase_adp_term s) p (r \<cdot> sigma)"
    and step: "adp_step_case (canonical_adps 1 D R)
      (p \<in> sharp_positions s) s t"
    and realizes: "realizes_origin_relation (origin_edge l r p sigma A phi) s t"
    by (rule canonical_strict_step_realizes_origin[
          OF rule targets valid p redex])
  have strict_step: "adp_step_case (canonical_adps 1 D R) True s t"
    using step root_marked by simp
  have q: "q \<in> sharp_positions t"
    by (rule realizes_origin_relationD[OF realizes edge predecessor_marked])
  show thesis by (rule that[OF erased strict_step q])
qed

lemma weak_rstep_has_defined_event:
  assumes step: "(s, t) \<in> rstep B"
    and wf: "wf_trs B"
    and defined: "adp_defined_symbols (R \<union> B) \<subseteq> D"
  obtains l r p sigma where
    "(l, r) \<in> B"
    "p \<in> poss s"
    "p \<in> adp_defined_positions D s"
    "s |_ p = l \<cdot> sigma"
    "t = replace_at s p (r \<cdot> sigma)"
    "vars_term r \<subseteq> vars_term l"
proof -
  from step obtain l r p sigma where event:
      "(s, t) \<in> rstep_r_p_s B (l, r) p sigma"
    unfolding rstep_iff_rstep_r_p_s by blast
  from event have rule: "(l, r) \<in> B" and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and target: "t = replace_at s p (r \<cdot> sigma)"
    unfolding rstep_r_p_s_def' by auto
  from wf rule obtain f ts where lhs: "l = Fun f ts"
    using wf_trs_imp_lhs_Fun by blast
  have f_defined: "f \<in> adp_defined_symbols (R \<union> B)"
    unfolding adp_defined_symbols_def
    by (rule CollectI, rule exI[of _ l], rule exI[of _ r],
        rule exI[of _ ts], rule conjI[OF UnI2[OF rule] lhs])
  have fD: "f \<in> D" by (rule subsetD[OF defined f_defined])
  have redex_root: "s |_ p = Fun f (map (\<lambda>u. u \<cdot> sigma) ts)"
    unfolding redex lhs by simp
  have p_defined: "p \<in> adp_defined_positions D s"
    unfolding adp_defined_positions_def mem_Collect_eq
    by (rule conjI[OF p], rule exI[of _ f],
        rule exI[of _ "map (\<lambda>u. u \<cdot> sigma) ts"],
        rule conjI[OF redex_root fD])
  have vars: "vars_term r \<subseteq> vars_term l"
    using wf rule unfolding wf_trs_def by blast
  show thesis by (rule that[OF rule p p_defined redex target vars])
qed

lemma fun_poss_erase_adp_term [simp]:
  "fun_poss (erase_adp_term t) = fun_poss t"
  by (induct t) auto

definition marked_pair_lift ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool" where
  "marked_pair_lift P s t q1 q2 q1' q2' \<longleftrightarrow>
    (\<forall>sh. erase_adp_term sh = s \<longrightarrow>
      q1 \<in> sharp_positions sh \<longrightarrow> q2 \<in> sharp_positions sh \<longrightarrow>
      (\<exists>th. erase_adp_term th = t \<and>
        (sh, th) \<in> (adp_step P)\<^sup>* \<and>
        q1' \<in> sharp_positions th \<and> q2' \<in> sharp_positions th))"

lemma marked_pair_lift_identity:
  "marked_pair_lift P s s q1 q2 q1 q2"
  unfolding marked_pair_lift_def by blast

lemma marked_pair_lift_comp:
  assumes first: "marked_pair_lift P s t q1 q2 q1' q2'"
    and second: "marked_pair_lift P t u q1' q2' q1'' q2''"
  shows "marked_pair_lift P s u q1 q2 q1'' q2''"
  unfolding marked_pair_lift_def
proof (intro allI impI)
  fix sh
  assume erased: "erase_adp_term sh = s"
    and marked1: "q1 \<in> sharp_positions sh"
    and marked2: "q2 \<in> sharp_positions sh"
  from first erased marked1 marked2 obtain th where th:
      "erase_adp_term th = t"
      "(sh, th) \<in> (adp_step P)\<^sup>*"
      "q1' \<in> sharp_positions th"
      "q2' \<in> sharp_positions th"
    unfolding marked_pair_lift_def by blast
  from second th obtain uh where uh:
      "erase_adp_term uh = u"
      "(th, uh) \<in> (adp_step P)\<^sup>*"
      "q1'' \<in> sharp_positions uh"
      "q2'' \<in> sharp_positions uh"
    unfolding marked_pair_lift_def by blast
  show "\<exists>uh. erase_adp_term uh = u \<and>
      (sh, uh) \<in> (adp_step P)\<^sup>* \<and>
      q1'' \<in> sharp_positions uh \<and> q2'' \<in> sharp_positions uh"
    by (rule exI[of _ uh], rule conjI[OF uh(1)],
        rule conjI[OF rtrancl_trans[OF th(2) uh(2)]],
        rule conjI[OF uh(3) uh(4)])
qed

lemma nonduplicating_weak_step_marked_pair_lift:
  assumes rule: "(l, r) \<in> B"
    and nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> poss s"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q1: "q1 \<in> nonterminating_defined_positions R B D
      (replace_at s p (r \<cdot> sigma))"
    and q2: "q2 \<in> nonterminating_defined_positions R B D
      (replace_at s p (r \<cdot> sigma))"
  obtains q1' q2' where
    "q1' \<in> nonterminating_defined_positions R B D s"
    "q2' \<in> nonterminating_defined_positions R B D s"
    "marked_pair_lift (canonical_adps 2 D B) s
      (replace_at s p (r \<cdot> sigma)) q1' q2' q1 q2"
proof -
  note pullback = nonduplicating_weak_rewrite_pulls_back_pair[
    OF rule nd p p_defined redex q1 q2]
  let ?A = "target_root_positions p q1 D r \<union>
    target_root_positions p q2 D r"
  have exists1: "\<exists>q1'.
      q1' \<in> nonterminating_defined_positions R B D s \<and>
      origin_edge l r p sigma ?A (covering_vrf l r) q1' q1"
    by (rule bspec[OF pullback(2)]) simp
  from exists1 obtain q1' where q1'_nt:
      "q1' \<in> nonterminating_defined_positions R B D s"
    and edge1: "origin_edge l r p sigma ?A (covering_vrf l r) q1' q1"
    by blast
  have exists2: "\<exists>q2'.
      q2' \<in> nonterminating_defined_positions R B D s \<and>
      origin_edge l r p sigma ?A (covering_vrf l r) q2' q2"
    by (rule bspec[OF pullback(2)]) simp
  from exists2 obtain q2' where q2'_nt:
      "q2' \<in> nonterminating_defined_positions R B D s"
    and edge2: "origin_edge l r p sigma ?A (covering_vrf l r) q2' q2"
    by blast
  have lift: "marked_pair_lift (canonical_adps 2 D B) s
      (replace_at s p (r \<cdot> sigma)) q1' q2' q1 q2"
    unfolding marked_pair_lift_def
  proof (intro allI impI)
    fix sh
    assume erased: "erase_adp_term sh = s"
      and marked1: "q1' \<in> sharp_positions sh"
      and marked2: "q2' \<in> sharp_positions sh"
    from p_defined obtain f ts where p_at: "s |_ p = Fun f ts"
      unfolding adp_defined_positions_def by blast
    have p_fun_plain: "p \<in> fun_poss s"
      by (rule poss_is_Fun_fun_poss[OF p]) (use p_at in simp)
    have erase_fun: "fun_poss s = fun_poss sh"
      using erased fun_poss_erase_adp_term[of sh] by simp
    have p_fun: "p \<in> fun_poss sh" using p_fun_plain unfolding erase_fun .
    have p_poss_sh: "p \<in> poss sh" by (rule fun_poss_imp_poss[OF p_fun])
    have redex_sh: "erase_adp_term (sh |_ p) = l \<cdot> sigma"
      using erase_adp_term_subt_at[OF p_poss_sh] erased redex by simp
    obtain th where erased_th:
        "erase_adp_term th = replace_at (erase_adp_term sh) p (r \<cdot> sigma)"
      and step: "adp_step_case (canonical_adps 2 D B)
        (p \<in> sharp_positions sh) sh th"
      and marked_q1: "q1 \<in> sharp_positions th"
      and marked_q2: "q2 \<in> sharp_positions th"
      by (rule canonical_nonduplicating_step_marks_pair[
            OF rule pullback(1) nd p_fun redex_sh edge1 edge2 marked1 marked2])
    have erased_target:
        "erase_adp_term th = replace_at s p (r \<cdot> sigma)"
      using erased_th erased by simp
    have adp_step: "(sh, th) \<in> adp_step (canonical_adps 2 D B)"
    proof (cases "p \<in> sharp_positions sh")
      case True
      have strict: "adp_step_case (canonical_adps 2 D B) True sh th"
        using step True by simp
      show ?thesis
        unfolding adp_step_def adp_step_case_rel_def using strict by auto
    next
      case False
      have weak: "adp_step_case (canonical_adps 2 D B) False sh th"
        using step False by simp
      show ?thesis
        unfolding adp_step_def adp_step_case_rel_def using weak by auto
    qed
    show "\<exists>th. erase_adp_term th = replace_at s p (r \<cdot> sigma) \<and>
        (sh, th) \<in> (adp_step (canonical_adps 2 D B))\<^sup>* \<and>
        q1 \<in> sharp_positions th \<and> q2 \<in> sharp_positions th"
      by (rule exI[of _ th], rule conjI[OF erased_target],
          rule conjI[OF r_into_rtrancl[OF adp_step]],
          rule conjI[OF marked_q1 marked_q2])
  qed
  show thesis by (rule that[OF q1'_nt q2'_nt lift])
qed

lemma nonduplicating_weak_sequence_marked_pair_lift:
  assumes wf: "wf_trs B"
    and nd: "nonduplicating_trs B"
    and defined: "adp_defined_symbols (R \<union> B) \<subseteq> D"
    and steps: "(s, t) \<in> (rstep B)\<^sup>*"
    and q1: "q1 \<in> nonterminating_defined_positions R B D t"
    and q2: "q2 \<in> nonterminating_defined_positions R B D t"
  shows "\<exists>q1' q2'.
    q1' \<in> nonterminating_defined_positions R B D s \<and>
    q2' \<in> nonterminating_defined_positions R B D s \<and>
    marked_pair_lift (canonical_adps 2 D B) s t q1' q2' q1 q2"
using steps q1 q2
proof (induct arbitrary: q1 q2 rule: rtrancl_induct)
  case base
  show ?case
    by (rule exI[of _ q1], rule exI[of _ q2],
        rule conjI[OF base.prems(1)], rule conjI[OF base.prems(2)],
        rule marked_pair_lift_identity)
next
  case (step u v)
  obtain l r p sigma where rule: "(l, r) \<in> B"
    and p: "p \<in> poss u"
    and p_defined: "p \<in> adp_defined_positions D u"
    and redex: "u |_ p = l \<cdot> sigma"
    and target: "v = replace_at u p (r \<cdot> sigma)"
    and vars: "vars_term r \<subseteq> vars_term l"
    by (rule weak_rstep_has_defined_event[OF step.hyps(2) wf defined])
  have rule_nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    using nd rule unfolding nonduplicating_trs_def by blast
  have q1_target: "q1 \<in> nonterminating_defined_positions R B D
      (replace_at u p (r \<cdot> sigma))"
    using step.prems(1) unfolding target .
  have q2_target: "q2 \<in> nonterminating_defined_positions R B D
      (replace_at u p (r \<cdot> sigma))"
    using step.prems(2) unfolding target .
  obtain a b where a_nt: "a \<in> nonterminating_defined_positions R B D u"
    and b_nt: "b \<in> nonterminating_defined_positions R B D u"
    and last_lift: "marked_pair_lift (canonical_adps 2 D B) u v a b q1 q2"
  proof -
    obtain a b where a_nt: "a \<in> nonterminating_defined_positions R B D u"
      and b_nt: "b \<in> nonterminating_defined_positions R B D u"
      and lift: "marked_pair_lift (canonical_adps 2 D B) u
        (replace_at u p (r \<cdot> sigma)) a b q1 q2"
      by (rule nonduplicating_weak_step_marked_pair_lift[
            OF rule rule_nd p p_defined redex q1_target q2_target])
    have lift': "marked_pair_lift (canonical_adps 2 D B) u v a b q1 q2"
      using lift unfolding target .
    show thesis by (rule that[OF a_nt b_nt lift'])
  qed
  obtain q1' q2' where q1'_nt:
      "q1' \<in> nonterminating_defined_positions R B D s"
    and q2'_nt: "q2' \<in> nonterminating_defined_positions R B D s"
    and first_lift:
      "marked_pair_lift (canonical_adps 2 D B) s u q1' q2' a b"
    using step.hyps(3)[OF a_nt b_nt] by blast
  have lift: "marked_pair_lift (canonical_adps 2 D B) s v q1' q2' q1 q2"
    by (rule marked_pair_lift_comp[OF first_lift last_lift])
  show ?case
    by (rule exI[of _ q1'], rule exI[of _ q2'],
        rule conjI[OF q1'_nt], rule conjI[OF q2'_nt lift])
qed

end
