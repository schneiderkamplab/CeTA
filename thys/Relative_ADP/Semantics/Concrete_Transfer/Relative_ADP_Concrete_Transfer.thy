theory Relative_ADP_Concrete_Transfer
  imports Relative_ADP_Context_Update_Dev.Relative_ADP_Context_Update
begin

lemma var_position_decomposition_unique:
  assumes alpha: "alpha \<in> var_poss r"
    and gamma: "gamma \<in> var_poss r"
    and split: "alpha @ beta = gamma @ delta"
  shows "alpha = gamma \<and> beta = delta"
  using assms
  by (metis append_eq_append_conv less_eq_pos_simps(1)
      pos_less_eq_append_not_parallel var_poss_parallel)

lemma concrete_context_position_has_origin_predecessor:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> poss s"
    and p_context: "p \<in> poss_mctxt C"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
    and q_context:
      "q \<in> poss_mctxt
        (mreplace_at C p (rhs_origin_mctxt l r p C))"
    and q_defined:
      "q \<in> adp_defined_positions D
        (replace_at s p (r \<cdot> sigma))"
    and roots: "target_root_positions p q D r \<subseteq> A"
  obtains q' where
    "q' \<in> poss_mctxt C"
    "q' \<in> adp_defined_positions D s"
    "origin_edge l r p sigma A (covering_vrf l r) q' q"
proof -
  have classified:
    "(q \<in> poss_mctxt C \<and> (q <\<^sub>p p \<or> q \<bottom> p)) \<or>
     (\<exists>a. q = p @ a \<and> a \<in> poss_mctxt (rhs_origin_mctxt l r p C))"
    by (rule poss_mctxt_mreplace_at_disj[OF p_context q_context])
  from classified
  show thesis
  proof
  assume outside: "q \<in> poss_mctxt C \<and> (q <\<^sub>p p \<or> q \<bottom> p)"
  have q_source: "q \<in> poss_mctxt C" using outside by blast
  have q_outside: "q <\<^sub>p p \<or> q \<bottom> p" using outside by blast
  have source_defined: "q \<in> adp_defined_positions D s"
    by (rule adp_defined_position_preserved_outside[OF p q_defined q_outside])
  have edge: "origin_edge l r p sigma A (covering_vrf l r) q q"
    by (rule origin_edge.preserved[OF q_outside])
  show thesis by (rule that[OF q_source source_defined edge])
next
  assume inside: "\<exists>a. q = p @ a \<and>
    a \<in> poss_mctxt (rhs_origin_mctxt l r p C)"
  then obtain a where q: "q = p @ a"
    and a_context: "a \<in> poss_mctxt (rhs_origin_mctxt l r p C)"
    by blast
  have below: "p \<le>\<^sub>p q" unfolding q by simp
  from replacement_defined_position_origin[OF p q_defined below]
  show thesis
  proof cases
    case (1 b)
    have b: "b \<in> target_root_positions p q D r"
      using 1 unfolding target_root_positions_def by blast
    have edge: "origin_edge l r p sigma A (covering_vrf l r) p q"
      using origin_edge.root_target[OF subsetD[OF roots b]] 1(1) by simp
    show thesis by (rule that[OF p_context p_defined edge])
  next
    case (2 x alpha beta)
    have a_split: "a = alpha @ beta" using q 2(1) by simp
    from rhs_origin_mctxt_position_root[OF a_context]
    have source_context:
      "p @ rhs_predecessor l r alpha @ beta \<in> poss_mctxt C"
    proof
      assume skeleton: "a \<in> fun_poss r"
      have alpha_beta: "alpha @ beta \<in> poss r"
        using skeleton a_split fun_poss_imp_poss by blast
      have False
      proof (cases beta)
        case Nil
        from fun_poss_fun_conv[OF skeleton] obtain f ts where
          r_at: "r |_ a = Fun f ts" by blast
        show False using r_at 2(3) a_split Nil by simp
      next
        case (Cons i beta')
        from var_pos_maximal[OF var_poss_imp_poss[OF 2(2)] 2(3),
            of beta]
        show False using alpha_beta unfolding Cons by simp
      qed
      then show ?thesis by blast
    next
      assume "\<exists>gamma delta.
        gamma \<in> var_poss r \<and>
        a = gamma @ delta \<and>
        p @ rhs_predecessor l r gamma @ delta \<in> poss_mctxt C"
      then obtain gamma delta where gamma: "gamma \<in> var_poss r"
        and a_gamma: "a = gamma @ delta"
        and source:
          "p @ rhs_predecessor l r gamma @ delta \<in> poss_mctxt C"
        by blast
      have split: "alpha @ beta = gamma @ delta"
        using a_split a_gamma by simp
      from var_position_decomposition_unique[OF 2(2) gamma split]
      show ?thesis using source by auto
    qed
    let ?rho = "rhs_predecessor l r alpha"
    have rho: "?rho \<in> var_poss l"
      by (rule rhs_predecessor_properties(1)[OF nd 2(2)])
    have rho_x: "l |_ ?rho = Var x"
      using rhs_predecessor_properties(2)[OF nd 2(2)] 2(3) by simp
    obtain f ts where beta_at: "sigma x |_ beta = Fun f ts" and fD: "f \<in> D"
      by (rule replacement_variable_target_has_defined_subterm[OF p q_defined
            2(1-3)])
    have beta_poss: "beta \<in> poss (sigma x)"
      by (rule fun_poss_imp_poss[OF 2(4)])
    have source_defined:
      "p @ ?rho @ beta \<in> adp_defined_positions D s"
      by (rule adp_defined_position_in_lhs_variable[OF p redex rho rho_x
            beta_poss beta_at fD])
    have selected: "covering_vrf l r ?rho = Some alpha"
      by (rule covering_vrf_covers[OF nd 2(2)])
    have target_fun: "alpha @ beta \<in> fun_poss (r \<cdot> sigma)"
      by (rule fun_position_below_instantiated_variable[
            where alpha = alpha and r = r and x = x and beta = beta
              and sigma = sigma])
         (rule 2(2), rule 2(3), rule 2(4))
    have edge:
      "origin_edge l r p sigma A (covering_vrf l r)
        (p @ ?rho @ beta) q"
    proof -
      have transported:
        "origin_edge l r p sigma A (covering_vrf l r)
          (p @ ?rho @ beta) (p @ alpha @ beta)"
        by (rule origin_edge.variable_transport[
              where rho = ?rho and l = l and phi = "covering_vrf l r"
                and alpha = alpha and beta = beta and r = r and sigma = sigma
                and p = p and A = A])
           (rule rho, rule selected, rule target_fun)
      show ?thesis using transported 2(1) by simp
    qed
    show thesis by (rule that[OF source_context source_defined edge])
  qed
  qed
qed

lemma concrete_base_context_pair_transfer:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> poss s"
    and p_context: "p \<in> poss_mctxt C"
    and p_defined: "p \<in> adp_defined_positions D s"
    and redex: "s |_ p = l \<cdot> sigma"
  shows "base_context_pair_transfer l r p sigma D s
    (replace_at s p (r \<cdot> sigma)) C
    (mreplace_at C p (rhs_origin_mctxt l r p C))"
proof (unfold base_context_pair_transfer_def, intro ballI impI)
  fix q1 q2
  assume q1_context:
      "q1 \<in> poss_mctxt
        (mreplace_at C p (rhs_origin_mctxt l r p C))"
    and q2_context:
      "q2 \<in> poss_mctxt
        (mreplace_at C p (rhs_origin_mctxt l r p C))"
    and q1_defined:
      "q1 \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
    and q2_defined:
      "q2 \<in> adp_defined_positions D (replace_at s p (r \<cdot> sigma))"
  let ?A = "target_root_positions p q1 D r \<union>
    target_root_positions p q2 D r"
  have targets: "origin_root_targets 2 D r ?A"
    by (rule paired_target_root_positions)
  obtain p1 where p1_context: "p1 \<in> poss_mctxt C"
    and p1_defined: "p1 \<in> adp_defined_positions D s"
    and edge1: "origin_edge l r p sigma ?A (covering_vrf l r) p1 q1"
  proof (rule concrete_context_position_has_origin_predecessor[
        OF nd p p_context p_defined redex q1_context q1_defined])
    show "target_root_positions p q1 D r \<subseteq> ?A" by blast
  qed
  obtain p2 where p2_context: "p2 \<in> poss_mctxt C"
    and p2_defined: "p2 \<in> adp_defined_positions D s"
    and edge2: "origin_edge l r p sigma ?A (covering_vrf l r) p2 q2"
  proof (rule concrete_context_position_has_origin_predecessor[
        OF nd p p_context p_defined redex q2_context q2_defined])
    show "target_root_positions p q2 D r \<subseteq> ?A" by blast
  qed
  show "\<exists>A p1 p2.
      origin_root_targets 2 D r A \<and>
      p1 \<in> poss_mctxt C \<and> p2 \<in> poss_mctxt C \<and>
      p1 \<in> adp_defined_positions D s \<and>
      p2 \<in> adp_defined_positions D s \<and>
      origin_edge l r p sigma A (covering_vrf l r) p1 q1 \<and>
      origin_edge l r p sigma A (covering_vrf l r) p2 q2"
    by (intro exI[of _ ?A] exI[of _ p1] exI[of _ p2])
       (use targets p1_context p2_context p1_defined p2_defined edge1 edge2
        in blast)
qed

end
