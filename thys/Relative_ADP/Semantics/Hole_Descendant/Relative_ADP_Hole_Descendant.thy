theory Relative_ADP_Hole_Descendant
  imports Relative_ADP_Hole_Transport_Dev.Relative_ADP_Hole_Transport
begin

lemma base_variable_transport_subterm:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> poss s"
    and redex: "s |_ p = l \<cdot> sigma"
    and alpha: "alpha \<in> var_poss r"
    and alpha_x: "r |_ alpha = Var x"
    and beta: "beta \<in> poss (sigma x)"
  shows "replace_at s p (r \<cdot> sigma) |_
      (p @ alpha @ beta) =
    s |_ (p @ rhs_predecessor l r alpha @ beta)"
proof -
  let ?rho = "rhs_predecessor l r alpha"
  have rho: "?rho \<in> var_poss l"
    by (rule rhs_predecessor_properties(1)[OF nd alpha])
  have rho_x: "l |_ ?rho = Var x"
    using rhs_predecessor_properties(2)[OF nd alpha] alpha_x by simp
  have alpha_poss: "alpha \<in> poss r" by (rule var_poss_imp_poss[OF alpha])
  have rho_poss: "?rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
  have p_target: "p \<in> poss (replace_at s p (r \<cdot> sigma))"
    by (rule replace_at_below_poss[OF p]) simp
  have alpha_subst: "alpha \<in> poss (r \<cdot> sigma)"
    using alpha_poss by simp
  have rho_subst: "?rho \<in> poss (l \<cdot> sigma)"
    using rho_poss by simp
  have lhs_at: "(l \<cdot> sigma) |_ ?rho = sigma x"
    using subt_at_subst[OF rho_poss, of sigma] rho_x by simp
  have rhs_at: "(r \<cdot> sigma) |_ alpha = sigma x"
    using subt_at_subst[OF alpha_poss, of sigma] alpha_x by simp
  have source_rho: "p @ ?rho \<in> poss s"
    using p rho_subst redex by (simp only: poss_append_poss)
  have target_alpha: "p @ alpha \<in> poss (replace_at s p (r \<cdot> sigma))"
    using p_target alpha_subst replace_at_subt_at[OF p]
    by (simp only: poss_append_poss)
  have target_split:
    "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ beta) =
      (replace_at s p (r \<cdot> sigma) |_ (p @ alpha)) |_ beta"
    using subt_at_append[OF target_alpha, of beta]
    by (simp add: append_assoc)
  have source_split:
    "s |_ (p @ ?rho @ beta) = (s |_ (p @ ?rho)) |_ beta"
    using subt_at_append[OF source_rho, of beta]
    by (simp add: append_assoc)
  have target_at:
    "replace_at s p (r \<cdot> sigma) |_ (p @ alpha) = sigma x"
    using subt_at_append[OF p_target, of alpha]
      replace_at_subt_at[OF p] rhs_at by simp
  have source_at: "s |_ (p @ ?rho) = sigma x"
    using subt_at_append[OF p, of ?rho] redex lhs_at by simp
  show ?thesis using target_split source_split target_at source_at by simp
qed

lemma concrete_new_hole_descends_from_old:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and length: "num_holes C = length holes"
    and source: "fill_holes C holes = s"
    and p_context: "p \<in> poss_mctxt C"
    and redex: "s |_ p = l \<cdot> sigma"
    and q_hole:
      "q \<in> hole_poss
        (mreplace_at C p (rhs_origin_mctxt l r p C))"
  obtains h beta where
    "h \<in> hole_poss C"
    "beta \<in> poss (s |_ h)"
    "replace_at s p (r \<cdot> sigma) |_ q = (s |_ h) |_ beta"
proof -
  have C_prefix: "C \<le> mctxt_of_term s"
    using fill_holes_suffix[OF length] source by simp
  have p_all: "p \<in> all_poss_mctxt C"
    using p_context unfolding all_poss_mctxt_conv by blast
  have p: "p \<in> poss s"
  proof -
    have "p \<in> all_poss_mctxt (mctxt_of_term s)"
      by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] p_all])
    then show ?thesis by simp
  qed
  from hole_pos_mreplace_at_disj[OF p_context q_hole]
  show thesis
  proof
    assume outside: "q \<in> hole_poss C \<and> q \<bottom> p"
    have q_all: "q \<in> all_poss_mctxt C"
      using outside unfolding all_poss_mctxt_conv by blast
    have q_poss: "q \<in> poss s"
    proof -
      have "q \<in> all_poss_mctxt (mctxt_of_term s)"
        by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] q_all])
      then show ?thesis by simp
    qed
    have unchanged:
      "replace_at s p (r \<cdot> sigma) |_ q = s |_ q"
      by (rule parallel_replace_at_subt_at[
            OF parallel_pos_sym[OF outside[THEN conjunct2]] p q_poss])
    show thesis
    proof (rule that[of q "[]"])
      show "q \<in> hole_poss C" using outside by blast
      show "[] \<in> poss (s |_ q)" by simp
      show "replace_at s p (r \<cdot> sigma) |_ q = (s |_ q) |_ []"
        using unchanged by simp
    qed
  next
    assume inside: "\<exists>a. q = p @ a \<and>
      a \<in> hole_poss (rhs_origin_mctxt l r p C)"
    then obtain a where q: "q = p @ a"
      and a_hole: "a \<in> hole_poss (rhs_origin_mctxt l r p C)"
      by blast
    from rhs_origin_mctxt_hole_root[OF nd C_prefix p redex a_hole]
    show thesis
    proof
      assume moved: "\<exists>alpha beta.
        alpha \<in> var_poss r \<and> a = alpha @ beta \<and>
        p @ rhs_predecessor l r alpha @ beta \<in> hole_poss C"
      then obtain alpha beta where alpha: "alpha \<in> var_poss r"
        and a: "a = alpha @ beta"
        and h: "p @ rhs_predecessor l r alpha @ beta \<in> hole_poss C"
        by blast
      obtain x where alpha_x: "r |_ alpha = Var x"
        using alpha unfolding var_poss_iff by blast
      let ?rho = "rhs_predecessor l r alpha"
      have rho: "?rho \<in> var_poss l"
        by (rule rhs_predecessor_properties(1)[OF nd alpha])
      have rho_x: "l |_ ?rho = Var x"
        using rhs_predecessor_properties(2)[OF nd alpha] alpha_x by simp
      have h_all: "p @ ?rho @ beta \<in> all_poss_mctxt C"
        using h unfolding all_poss_mctxt_conv by blast
      have h_poss: "p @ ?rho @ beta \<in> poss s"
      proof -
        have "p @ ?rho @ beta \<in> all_poss_mctxt (mctxt_of_term s)"
          by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] h_all])
        then show ?thesis by simp
      qed
      have rho_poss: "?rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
      have source_rho: "s |_ (p @ ?rho) = sigma x"
        using subt_at_append[OF p, of ?rho]
          subt_at_subst[OF rho_poss, of sigma] redex rho_x by simp
      have source_rho_nested: "(s |_ p) |_ ?rho = sigma x"
        using subt_at_append[OF p, of ?rho] source_rho by simp
      have beta_poss: "beta \<in> poss (sigma x)"
        using h_poss p source_rho_nested by (simp only: poss_append_poss)
      have transported:
        "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ beta) =
          s |_ (p @ ?rho @ beta)"
        by (rule base_variable_transport_subterm[
              OF nd p redex alpha alpha_x beta_poss])
      show thesis
      proof (rule that[of "p @ ?rho @ beta" "[]"])
        show "p @ ?rho @ beta \<in> hole_poss C" by (rule h)
        show "[] \<in> poss (s |_ (p @ ?rho @ beta))" by simp
        show "replace_at s p (r \<cdot> sigma) |_ q =
          (s |_ (p @ ?rho @ beta)) |_ []"
          using transported q a by simp
      qed
    next
      assume split: "\<exists>alpha h beta.
        alpha \<in> var_poss r \<and> a = alpha \<and>
        h \<in> hole_poss C \<and>
        p @ rhs_predecessor l r alpha = h @ beta"
      then obtain alpha h beta where alpha: "alpha \<in> var_poss r"
        and a: "a = alpha" and h: "h \<in> hole_poss C"
        and source_pos: "p @ rhs_predecessor l r alpha = h @ beta"
        by blast
      obtain x where alpha_x: "r |_ alpha = Var x"
        using alpha unfolding var_poss_iff by blast
      have h_all: "h \<in> all_poss_mctxt C"
        using h unfolding all_poss_mctxt_conv by blast
      have h_poss: "h \<in> poss s"
      proof -
        have "h \<in> all_poss_mctxt (mctxt_of_term s)"
          by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] h_all])
        then show ?thesis by simp
      qed
      have source_term: "p @ rhs_predecessor l r alpha \<in> poss s"
      proof -
        have rho: "rhs_predecessor l r alpha \<in> var_poss l"
          by (rule rhs_predecessor_properties(1)[OF nd alpha])
        have rho_poss: "rhs_predecessor l r alpha \<in> poss l"
          by (rule var_poss_imp_poss[OF rho])
        show ?thesis using p rho_poss redex
          by (simp only: poss_append_poss) simp
      qed
      have beta_poss: "beta \<in> poss (s |_ h)"
        using source_term h_poss source_pos by (simp only: poss_append_poss)
      have transported:
        "replace_at s p (r \<cdot> sigma) |_ (p @ alpha) =
          s |_ (p @ rhs_predecessor l r alpha)"
        using base_variable_transport_subterm[
          OF nd p redex alpha alpha_x, of "[]"] by simp
      have source_at:
        "s |_ (p @ rhs_predecessor l r alpha) = (s |_ h) |_ beta"
        using subt_at_append[OF h_poss, of beta] source_pos by simp
      show thesis
      proof (rule that[of h beta])
        show "h \<in> hole_poss C" by (rule h)
        show "beta \<in> poss (s |_ h)" by (rule beta_poss)
        show "replace_at s p (r \<cdot> sigma) |_ q = (s |_ h) |_ beta"
          using transported source_at q a by simp
      qed
    qed
  qed
qed

end
