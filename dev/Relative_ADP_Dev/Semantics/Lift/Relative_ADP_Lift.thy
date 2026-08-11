theory Relative_ADP_Lift
  imports Relative_ADP_Trace_Dev.Relative_ADP_Trace
begin

lemma parallel_pos_common_prefix [simp]:
  "(c @ p \<bottom> c @ q) \<longleftrightarrow> p \<bottom> q"
  by (induct c) auto

lemma less_pos_common_prefix [simp]:
  "(c @ p <\<^sub>p c @ q) \<longleftrightarrow> p <\<^sub>p q"
  unfolding less_pos_def' by auto

lemma replace_at_append_context:
  assumes q: "q \<in> poss s"
  shows "replace_at s (q @ p) u = replace_at s q (replace_at (s |_ q) p u)"
  unfolding ctxt_of_pos_term_append[OF q]
  by (simp add: replace_at_subt_at[OF q])

lemma fun_poss_below:
  assumes q: "q \<in> poss s" and p: "p \<in> fun_poss (s |_ q)"
  shows "q @ p \<in> fun_poss s"
proof -
  have qp: "q @ p \<in> poss s"
    using q fun_poss_imp_poss[OF p] by simp
  from p obtain f ts where at: "s |_ q |_ p = Fun f ts"
    using fun_poss_fun_conv by blast
  have "s |_ (q @ p) = Fun f ts" using subt_at_append[OF q] at by simp
  then have "is_Fun (s |_ (q @ p))" by simp
  then show ?thesis by (rule poss_is_Fun_fun_poss[OF qp])
qed

lemma origin_edge_prefix:
  assumes edge: "origin_edge l r p sigma A phi a b"
  shows "origin_edge l r (q @ p) sigma A phi (q @ a) (q @ b)"
  using edge
proof cases
  case preserved
  have "q @ a <\<^sub>p q @ p \<or> q @ a \<bottom> q @ p"
    using preserved by auto
  then have "origin_edge l r (q @ p) sigma A phi (q @ a) (q @ a)"
    by (rule origin_edge.preserved)
  with preserved show ?thesis by simp
next
  case (root_target alpha)
  have "origin_edge l r (q @ p) sigma A phi
      (q @ p) ((q @ p) @ alpha)"
    by (rule origin_edge.root_target[OF root_target(3)])
  with root_target show ?thesis by (simp add: append_assoc)
next
  case (variable_transport rho alpha beta)
  have "origin_edge l r (q @ p) sigma A phi
      ((q @ p) @ rho @ beta) ((q @ p) @ alpha @ beta)"
    by (rule origin_edge.variable_transport[
          where rho = rho and l = l and phi = phi and alpha = alpha
            and beta = beta and r = r and sigma = sigma and p = "q @ p"
            and A = A])
       (rule variable_transport(3), rule variable_transport(4),
        rule variable_transport(5))
  with variable_transport show ?thesis by (simp add: append_assoc)
qed

lemma relative_origin_block_context:
  assumes block: "relative_origin_block R B D v u a b c"
    and q: "q \<in> poss s"
    and at: "s |_ q = v"
  shows "relative_origin_block R B D s (replace_at s q u)
    (q @ a) (q @ b) (q @ c)"
  using block q at
proof (induct arbitrary: s rule: relative_origin_block.induct)
  case (strict l r A phi p v sigma c' c)
  have qp_fun: "q @ p \<in> fun_poss s"
    by (rule fun_poss_below[OF strict.prems(1)])
       (use strict.hyps(4) strict.prems(2) in simp)
  have redex: "s |_ (q @ p) = l \<cdot> sigma"
    using subt_at_append[OF strict.prems(1)] strict.prems(2) strict.hyps(5)
    by simp
  have edge: "origin_edge l r (q @ p) sigma A phi (q @ c') (q @ c)"
    by (rule origin_edge_prefix[OF strict.hyps(6)])
  have target: "replace_at s q (replace_at v p (r \<cdot> sigma)) =
      replace_at s (q @ p) (r \<cdot> sigma)"
    using replace_at_append_context[OF strict.prems(1), of p "r \<cdot> sigma"]
      strict.prems(2) by simp
  show ?case
    unfolding target
    by (rule relative_origin_block.strict[OF strict.hyps(1-3) qp_fun redex edge])
next
  case (weak l r A p v sigma a' a b' b u c)
  let ?m = "replace_at v p (r \<cdot> sigma)"
  let ?sm = "replace_at s (q @ p) (r \<cdot> sigma)"
  have qp_fun: "q @ p \<in> fun_poss s"
    by (rule fun_poss_below[OF weak.prems(1)])
       (use weak.hyps(4) weak.prems(2) in simp)
  have redex: "s |_ (q @ p) = l \<cdot> sigma"
    using subt_at_append[OF weak.prems(1)] weak.prems(2) weak.hyps(5)
    by simp
  have edge1: "origin_edge l r (q @ p) sigma A (covering_vrf l r)
      (q @ a') (q @ a)"
    by (rule origin_edge_prefix[OF weak.hyps(6)])
  have edge2: "origin_edge l r (q @ p) sigma A (covering_vrf l r)
      (q @ b') (q @ b)"
    by (rule origin_edge_prefix[OF weak.hyps(7)])
  have q_middle: "q \<in> poss ?sm"
    by (rule replace_at_below_poss[OF fun_poss_imp_poss[OF qp_fun]]) simp
  have middle_at: "?sm |_ q = ?m"
  proof -
    have nested: "?sm = replace_at s q ?m"
      using replace_at_append_context[OF weak.prems(1), of p "r \<cdot> sigma"]
        weak.prems(2) by simp
    show ?thesis unfolding nested by (simp add: replace_at_subt_at[OF weak.prems(1)])
  qed
  have tail: "relative_origin_block R B D ?sm (replace_at ?sm q u)
      (q @ a) (q @ b) (q @ c)"
    by (rule weak.hyps(9)[OF q_middle middle_at])
  have lifted: "relative_origin_block R B D s (replace_at ?sm q u)
      (q @ a') (q @ b') (q @ c)"
    by (rule relative_origin_block.weak[
          OF weak.hyps(1-3) qp_fun redex edge1 edge2 tail])
  have target: "replace_at ?sm q u = replace_at s q u"
  proof -
    have nested: "?sm = replace_at s q ?m"
      using replace_at_append_context[OF weak.prems(1), of p "r \<cdot> sigma"]
        weak.prems(2) by simp
    have ctxt: "ctxt_of_pos_term q (replace_at s q ?m) = ctxt_of_pos_term q s"
      by (rule ctxt_of_pos_term_replace_at_below[
            OF weak.prems(1), where p' = q]) simp
    show ?thesis unfolding nested using ctxt by simp
  qed
  show ?case using lifted unfolding target .
next
  case (strict_prefix l r p v sigma a b u c)
  let ?m = "replace_at v p (r \<cdot> sigma)"
  let ?sm = "replace_at s (q @ p) (r \<cdot> sigma)"
  have qp_fun: "q @ p \<in> fun_poss s"
    by (rule fun_poss_below[OF strict_prefix.prems(1)])
       (use strict_prefix.hyps(2) strict_prefix.prems(2) in simp)
  have redex: "s |_ (q @ p) = l \<cdot> sigma"
    using subt_at_append[OF strict_prefix.prems(1)] strict_prefix.prems(2)
      strict_prefix.hyps(3) by simp
  have outside1: "q @ a <\<^sub>p q @ p \<or> q @ a \<bottom> q @ p"
    using strict_prefix.hyps(4) by simp
  have outside2: "q @ b <\<^sub>p q @ p \<or> q @ b \<bottom> q @ p"
    using strict_prefix.hyps(5) by simp
  have q_middle: "q \<in> poss ?sm"
    by (rule replace_at_below_poss[OF fun_poss_imp_poss[OF qp_fun]]) simp
  have middle_at: "?sm |_ q = ?m"
  proof -
    have nested: "?sm = replace_at s q ?m"
      using replace_at_append_context[OF strict_prefix.prems(1),
        of p "r \<cdot> sigma"] strict_prefix.prems(2) by simp
    show ?thesis unfolding nested
      by (simp add: replace_at_subt_at[OF strict_prefix.prems(1)])
  qed
  have tail: "relative_origin_block R B D ?sm (replace_at ?sm q u)
      (q @ a) (q @ b) (q @ c)"
    by (rule strict_prefix.hyps(7)[OF q_middle middle_at])
  have lifted: "relative_origin_block R B D s (replace_at ?sm q u)
      (q @ a) (q @ b) (q @ c)"
    by (rule relative_origin_block.strict_prefix[
          OF strict_prefix.hyps(1) qp_fun redex outside1 outside2 tail])
  have target: "replace_at ?sm q u = replace_at s q u"
  proof -
    have nested: "?sm = replace_at s q ?m"
      using replace_at_append_context[OF strict_prefix.prems(1),
        of p "r \<cdot> sigma"] strict_prefix.prems(2) by simp
    have ctxt: "ctxt_of_pos_term q (replace_at s q ?m) = ctxt_of_pos_term q s"
      by (rule ctxt_of_pos_term_replace_at_below[
            OF strict_prefix.prems(1), where p' = q]) simp
    show ?thesis unfolding nested using ctxt by simp
  qed
  show ?case using lifted unfolding target .
qed

end
