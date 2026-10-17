theory Relative_ADP_Witness_Parallel
  imports Relative_ADP_Hole_Witness_Dev.Relative_ADP_Hole_Witness
begin

lemma parallel_pos_remove_common_left:
  fixes p a b :: pos
  assumes "p @ a \<bottom> p @ b"
  shows "a \<bottom> b"
  using assms by (induct p) auto

lemma concrete_hole_witness_same_parent_parallel:
  fixes p q1 q2 h beta1 beta2 :: pos
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and first: "concrete_hole_witness l r p C q1 h beta1"
    and second: "concrete_hole_witness l r p C q2 h beta2"
    and distinct: "q1 \<noteq> q2"
  shows "beta1 \<bottom> beta2"
proof -
  note injective = rhs_predecessor_inj_on[OF nd]
  from concrete_hole_witness_cases_disj[OF first]
  show ?thesis
  proof (elim disjE)
    assume outside1:
      "q1 = h \<and> beta1 = [] \<and> h \<in> hole_poss C \<and> h \<bottom> p"
    from concrete_hole_witness_cases_disj[OF second]
    show ?thesis
    proof (elim disjE)
      assume outside2:
        "q2 = h \<and> beta2 = [] \<and> h \<in> hole_poss C \<and> h \<bottom> p"
      with outside1 distinct show ?thesis by blast
    next
      assume moved2: "\<exists>alpha tail.
        alpha \<in> var_poss r \<and> q2 = p @ alpha @ tail \<and>
        h = p @ rhs_predecessor l r alpha @ tail \<and>
        beta2 = [] \<and> h \<in> hole_poss C"
      then obtain alpha tail where h: "h = p @ rhs_predecessor l r alpha @ tail"
        by blast
      have "p \<le>\<^sub>p h" unfolding h by simp
      with outside1 show ?thesis unfolding parallel_pos by auto
    next
      assume split2: "\<exists>alpha.
        alpha \<in> var_poss r \<and> q2 = p @ alpha \<and>
        h \<in> hole_poss C \<and>
        p @ rhs_predecessor l r alpha = h @ beta2"
      then obtain alpha where source: "p @ rhs_predecessor l r alpha = h @ beta2"
        by blast
      have "p \<le>\<^sub>p h @ beta2" unfolding source[symmetric] by simp
      then have "\<not> (p \<bottom> h)"
        by (rule pos_less_eq_append_not_parallel)
      with outside1 show ?thesis using parallel_pos_sym by blast
    qed
  next
    assume moved1: "\<exists>alpha tail.
      alpha \<in> var_poss r \<and> q1 = p @ alpha @ tail \<and>
      h = p @ rhs_predecessor l r alpha @ tail \<and>
      beta1 = [] \<and> h \<in> hole_poss C"
    then obtain alpha1 tail1 where alpha1: "alpha1 \<in> var_poss r"
      and q1: "q1 = p @ alpha1 @ tail1"
      and h1: "h = p @ rhs_predecessor l r alpha1 @ tail1"
      and beta1: "beta1 = []" by blast
    let ?rho1 = "rhs_predecessor l r alpha1"
    have rho1: "?rho1 \<in> var_poss l"
      by (rule rhs_predecessor_properties(1)[OF nd alpha1])
    from concrete_hole_witness_cases_disj[OF second]
    show ?thesis
    proof (elim disjE)
      assume outside2:
        "q2 = h \<and> beta2 = [] \<and> h \<in> hole_poss C \<and> h \<bottom> p"
      have "p \<le>\<^sub>p h" unfolding h1 by simp
      with outside2 show ?thesis unfolding parallel_pos by auto
    next
      assume moved2: "\<exists>alpha tail.
        alpha \<in> var_poss r \<and> q2 = p @ alpha @ tail \<and>
        h = p @ rhs_predecessor l r alpha @ tail \<and>
        beta2 = [] \<and> h \<in> hole_poss C"
      then obtain alpha2 tail2 where alpha2: "alpha2 \<in> var_poss r"
        and q2: "q2 = p @ alpha2 @ tail2"
        and h2: "h = p @ rhs_predecessor l r alpha2 @ tail2"
        and beta2: "beta2 = []" by blast
      let ?rho2 = "rhs_predecessor l r alpha2"
      have rho2: "?rho2 \<in> var_poss l"
        by (rule rhs_predecessor_properties(1)[OF nd alpha2])
      have split: "?rho1 @ tail1 = ?rho2 @ tail2"
        using h1 h2 by simp
      from var_position_decomposition_unique[OF rho1 rho2 split]
      have rho_eq: "?rho1 = ?rho2" and tail_eq: "tail1 = tail2" by blast+
      have alpha_eq: "alpha1 = alpha2"
        by (rule inj_onD[OF injective rho_eq alpha1 alpha2])
      with q1 q2 tail_eq distinct show ?thesis by simp
    next
      assume split2: "\<exists>alpha.
        alpha \<in> var_poss r \<and> q2 = p @ alpha \<and>
        h \<in> hole_poss C \<and>
        p @ rhs_predecessor l r alpha = h @ beta2"
      then obtain alpha2 where alpha2: "alpha2 \<in> var_poss r"
        and q2: "q2 = p @ alpha2"
        and source2: "p @ rhs_predecessor l r alpha2 = h @ beta2"
        by blast
      let ?rho2 = "rhs_predecessor l r alpha2"
      have rho2: "?rho2 \<in> var_poss l"
        by (rule rhs_predecessor_properties(1)[OF nd alpha2])
      have split: "?rho2 @ [] = ?rho1 @ (tail1 @ beta2)"
        using h1 source2 by (simp add: append_assoc)
      from var_position_decomposition_unique[OF rho2 rho1 split]
      have rho_eq: "?rho2 = ?rho1" and empty: "[] = tail1 @ beta2" by blast+
      have alpha_eq: "alpha2 = alpha1"
        by (rule inj_onD[OF injective rho_eq alpha2 alpha1])
      from empty have tail1: "tail1 = []" and beta2: "beta2 = []" by auto
      with alpha_eq q1 q2 distinct show ?thesis by simp
    qed
  next
    assume split1: "\<exists>alpha.
      alpha \<in> var_poss r \<and> q1 = p @ alpha \<and>
      h \<in> hole_poss C \<and>
      p @ rhs_predecessor l r alpha = h @ beta1"
    then obtain alpha1 where alpha1: "alpha1 \<in> var_poss r"
      and q1: "q1 = p @ alpha1"
      and source1: "p @ rhs_predecessor l r alpha1 = h @ beta1"
      by blast
    let ?rho1 = "rhs_predecessor l r alpha1"
    have rho1: "?rho1 \<in> var_poss l"
      by (rule rhs_predecessor_properties(1)[OF nd alpha1])
    from concrete_hole_witness_cases_disj[OF second]
    show ?thesis
    proof (elim disjE)
      assume outside2:
        "q2 = h \<and> beta2 = [] \<and> h \<in> hole_poss C \<and> h \<bottom> p"
      have "p \<le>\<^sub>p h @ beta1" unfolding source1[symmetric] by simp
      then have "\<not> (p \<bottom> h)"
        by (rule pos_less_eq_append_not_parallel)
      with outside2 show ?thesis using parallel_pos_sym by blast
    next
      assume moved2: "\<exists>alpha tail.
        alpha \<in> var_poss r \<and> q2 = p @ alpha @ tail \<and>
        h = p @ rhs_predecessor l r alpha @ tail \<and>
        beta2 = [] \<and> h \<in> hole_poss C"
      then obtain alpha2 tail2 where alpha2: "alpha2 \<in> var_poss r"
        and q2: "q2 = p @ alpha2 @ tail2"
        and h2: "h = p @ rhs_predecessor l r alpha2 @ tail2"
        and beta2: "beta2 = []" by blast
      let ?rho2 = "rhs_predecessor l r alpha2"
      have rho2: "?rho2 \<in> var_poss l"
        by (rule rhs_predecessor_properties(1)[OF nd alpha2])
      have split: "?rho1 @ [] = ?rho2 @ (tail2 @ beta1)"
        using source1 h2 by (simp add: append_assoc)
      from var_position_decomposition_unique[OF rho1 rho2 split]
      have rho_eq: "?rho1 = ?rho2" and empty: "[] = tail2 @ beta1" by blast+
      have alpha_eq: "alpha1 = alpha2"
        by (rule inj_onD[OF injective rho_eq alpha1 alpha2])
      from empty have tail2: "tail2 = []" and beta1: "beta1 = []" by auto
      with alpha_eq q1 q2 distinct show ?thesis by simp
    next
      assume split2: "\<exists>alpha.
        alpha \<in> var_poss r \<and> q2 = p @ alpha \<and>
        h \<in> hole_poss C \<and>
        p @ rhs_predecessor l r alpha = h @ beta2"
      then obtain alpha2 where alpha2: "alpha2 \<in> var_poss r"
        and q2: "q2 = p @ alpha2"
        and source2: "p @ rhs_predecessor l r alpha2 = h @ beta2"
        by blast
      let ?rho2 = "rhs_predecessor l r alpha2"
      have rho2: "?rho2 \<in> var_poss l"
        by (rule rhs_predecessor_properties(1)[OF nd alpha2])
      have alpha_neq: "alpha1 \<noteq> alpha2" using distinct q1 q2 by auto
      have rho_neq: "?rho1 \<noteq> ?rho2"
        using inj_onD[OF injective _ alpha1 alpha2] alpha_neq by blast
      have rho_parallel: "?rho1 \<bottom> ?rho2"
        by (rule var_poss_parallel[OF rho1 rho2 rho_neq])
      have source_parallel: "p @ ?rho1 \<bottom> p @ ?rho2"
        by (rule parallel_pos_append_common_left[OF rho_parallel])
      have "h @ beta1 \<bottom> h @ beta2"
        using source_parallel source1 source2 by simp
      then show ?thesis by (rule parallel_pos_remove_common_left)
    qed
  qed
qed

end
