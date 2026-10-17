theory Relative_ADP_Concrete_Refinement
  imports Relative_ADP_Witness_Parallel_Dev.Relative_ADP_Witness_Parallel
begin

lemma removeAll_Nil_map:
  "removeAll [] (map f xs) = map f (filter (\<lambda>x. f x \<noteq> []) xs)"
  by (induct xs) auto

lemma distinct_map_Cons:
  "distinct xs \<Longrightarrow> distinct (map ((#) i) xs)"
  by (induct xs) auto

lemma distinct_hole_poss': "distinct (hole_poss' C)"
proof (induct C)
  case (MFun f Cs)
  let ?F = "\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))"
  let ?is = "[0..<length Cs]"
  have children: "\<And>i. i < length Cs \<Longrightarrow> distinct (hole_poss' (Cs ! i))"
    using MFun.hyps nth_mem by blast
  have remove:
    "removeAll [] (map ?F ?is) = map ?F (filter (\<lambda>i. ?F i \<noteq> []) ?is)"
    by (rule removeAll_Nil_map)
  have injective:
    "inj_on ?F {i. i < length Cs \<and> ?F i \<noteq> []}"
  proof (rule inj_onI)
    fix i j
    assume i: "i \<in> {i. i < length Cs \<and> ?F i \<noteq> []}"
      and j: "j \<in> {i. i < length Cs \<and> ?F i \<noteq> []}"
      and eq: "?F i = ?F j"
    from i obtain pi ps where hi: "?F i = (i # pi) # ps"
      by (cases "hole_poss' (Cs ! i)") auto
    from j obtain pj qs where hj: "?F j = (j # pj) # qs"
      by (cases "hole_poss' (Cs ! j)") auto
    show "i = j" using eq hi hj by simp
  qed
  have blocks: "distinct (removeAll [] (map ?F ?is))"
    unfolding remove
    by (rule distinct_map[THEN iffD2])
       (use injective in auto)
  show ?case
    unfolding hole_poss'.simps
  proof (rule distinct_concat_iff[THEN iffD2], intro conjI)
    show "distinct (removeAll [] (map ?F ?is))" by (rule blocks)
    show "\<forall>ys. ys \<in> set (map ?F ?is) \<longrightarrow> distinct ys"
    proof (intro allI impI)
      fix ys
      assume "ys \<in> set (map ?F ?is)"
      then obtain i where i: "i < length Cs" and ys: "ys = ?F i" by auto
      show "distinct ys"
        unfolding ys
        by (rule distinct_map_Cons, rule children[OF i])
    qed
    show "\<forall>ys zs. ys \<in> set (map ?F ?is) \<and>
      zs \<in> set (map ?F ?is) \<and> ys \<noteq> zs \<longrightarrow>
      set ys \<inter> set zs = {}"
    proof (intro allI impI)
      fix ys zs
      assume assms: "ys \<in> set (map ?F ?is) \<and>
        zs \<in> set (map ?F ?is) \<and> ys \<noteq> zs"
      then obtain i j where i: "i < length Cs" and ys: "ys = ?F i"
        and j: "j < length Cs" and zs: "zs = ?F j" by auto
      have ij: "i \<noteq> j" using assms ys zs by auto
      show "set ys \<inter> set zs = {}"
        unfolding ys zs using ij by auto
    qed
  qed
qed auto

lemma concrete_hole_witness_semantic:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and length: "num_holes C = length holes"
    and source: "fill_holes C holes = s"
    and p_context: "p \<in> poss_mctxt C"
    and redex: "s |_ p = l \<cdot> sigma"
    and witness: "concrete_hole_witness l r p C q h beta"
  shows "h \<in> hole_poss C \<and>
    beta \<in> poss (s |_ h) \<and>
    replace_at s p (r \<cdot> sigma) |_ q = (s |_ h) |_ beta"
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
  from concrete_hole_witness_cases_disj[OF witness]
  show ?thesis
  proof (elim disjE)
    assume outside:
      "q = h \<and> beta = [] \<and> h \<in> hole_poss C \<and> h \<bottom> p"
    have h_all: "h \<in> all_poss_mctxt C"
      using outside unfolding all_poss_mctxt_conv by blast
    have h_poss: "h \<in> poss s"
    proof -
      have "h \<in> all_poss_mctxt (mctxt_of_term s)"
        by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] h_all])
      then show ?thesis by simp
    qed
    have unchanged: "replace_at s p (r \<cdot> sigma) |_ h = s |_ h"
      by (rule parallel_replace_at_subt_at[
            OF parallel_pos_sym[OF outside[THEN conjunct2, THEN conjunct2,
              THEN conjunct2]] p h_poss])
    show ?thesis using outside unchanged by simp
  next
    assume moved: "\<exists>alpha tail.
      alpha \<in> var_poss r \<and> q = p @ alpha @ tail \<and>
      h = p @ rhs_predecessor l r alpha @ tail \<and>
      beta = [] \<and> h \<in> hole_poss C"
    then obtain alpha tail where alpha: "alpha \<in> var_poss r"
      and q: "q = p @ alpha @ tail"
      and h: "h = p @ rhs_predecessor l r alpha @ tail"
      and beta: "beta = []" and h_hole: "h \<in> hole_poss C"
      by blast
    obtain x where alpha_x: "r |_ alpha = Var x"
      using alpha unfolding var_poss_iff by blast
    let ?rho = "rhs_predecessor l r alpha"
    have rho: "?rho \<in> var_poss l"
      by (rule rhs_predecessor_properties(1)[OF nd alpha])
    have rho_x: "l |_ ?rho = Var x"
      using rhs_predecessor_properties(2)[OF nd alpha] alpha_x by simp
    have h_all: "h \<in> all_poss_mctxt C"
      using h_hole unfolding all_poss_mctxt_conv by blast
    have h_poss: "h \<in> poss s"
    proof -
      have "h \<in> all_poss_mctxt (mctxt_of_term s)"
        by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] h_all])
      then show ?thesis by simp
    qed
    have rho_poss: "?rho \<in> poss l" by (rule var_poss_imp_poss[OF rho])
    have source_nested: "(s |_ p) |_ ?rho = sigma x"
      using subt_at_subst[OF rho_poss, of sigma] redex rho_x by simp
    have tail_poss: "tail \<in> poss (sigma x)"
      using h_poss p h source_nested by (simp only: poss_append_poss)
    have transported:
      "replace_at s p (r \<cdot> sigma) |_ (p @ alpha @ tail) =
        s |_ (p @ ?rho @ tail)"
      by (rule base_variable_transport_subterm[
            OF nd p redex alpha alpha_x tail_poss])
    show ?thesis using h_hole transported q h beta by simp
  next
    assume split: "\<exists>alpha.
      alpha \<in> var_poss r \<and> q = p @ alpha \<and>
      h \<in> hole_poss C \<and>
      p @ rhs_predecessor l r alpha = h @ beta"
    then obtain alpha where alpha: "alpha \<in> var_poss r"
      and q: "q = p @ alpha" and h_hole: "h \<in> hole_poss C"
      and source_pos: "p @ rhs_predecessor l r alpha = h @ beta"
      by blast
    obtain x where alpha_x: "r |_ alpha = Var x"
      using alpha unfolding var_poss_iff by blast
    have h_all: "h \<in> all_poss_mctxt C"
      using h_hole unfolding all_poss_mctxt_conv by blast
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
    show ?thesis using h_hole beta_poss transported source_at q by simp
  qed
qed

lemma concrete_carrier_refinement_exists:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and length: "num_holes C = length holes"
    and source: "fill_holes C holes = s"
    and p_context: "p \<in> poss_mctxt C"
    and redex: "s |_ p = l \<cdot> sigma"
  defines "C' \<equiv> mreplace_at C p (rhs_origin_mctxt l r p C)"
    and "t' \<equiv> replace_at s p (r \<cdot> sigma)"
    and "holes' \<equiv> unfill_holes
      (mreplace_at C p (rhs_origin_mctxt l r p C))
      (replace_at s p (r \<cdot> sigma))"
  shows "\<exists>parents tails. carrier_refinement holes' parents tails holes"
proof -
  have C'_prefix: "C' \<le> mctxt_of_term t'"
    unfolding C'_def t'_def
    by (rule concrete_target_context_prefix[OF nd length source p_context redex])
  have new_length: "length holes' = num_holes C'"
    unfolding holes'_def C'_def t'_def
    using length_unfill_holes[OF C'_prefix] unfolding C'_def t'_def by simp
  have old_positions: "length (hole_poss' C) = length holes"
    using length by simp
  have new_positions: "length (hole_poss' C') = length holes'"
    using new_length by simp
  have per_index:
    "\<forall>i < length holes'. \<exists>j beta.
      j < length holes \<and>
      concrete_hole_witness l r p C (hole_poss' C' ! i)
        (hole_poss' C ! j) beta"
  proof (intro allI impI)
    fix i
    assume i: "i < length holes'"
    have iC: "i < num_holes C'" using i new_length by simp
    have q_hole: "hole_poss' C' ! i \<in> hole_poss C'"
      using nth_mem[of i "hole_poss' C'"] iC
      unfolding set_hole_poss'[symmetric] by simp
    have q_hole': "hole_poss' C' ! i \<in> hole_poss
      (mreplace_at C p (rhs_origin_mctxt l r p C))"
      using q_hole unfolding C'_def .
    obtain h beta where witness:
      "concrete_hole_witness l r p C (hole_poss' C' ! i) h beta"
      using concrete_hole_witness_total[
        OF nd length source p_context redex q_hole']
      by blast
    have h: "h \<in> hole_poss C"
      by (rule concrete_hole_witness_old_hole[OF witness])
    from h obtain j where j_pos: "j < length (hole_poss' C)"
      and at: "hole_poss' C ! j = h"
      unfolding set_hole_poss'[symmetric] by (auto simp: in_set_conv_nth)
    have j: "j < length holes" using j_pos old_positions by simp
    show "\<exists>j beta. j < length holes \<and>
      concrete_hole_witness l r p C (hole_poss' C' ! i)
        (hole_poss' C ! j) beta"
      by (intro exI[of _ j] exI[of _ beta]) (use j witness at in simp)
  qed
  obtain parent tail where selected:
    "\<And>i. i < length holes' \<Longrightarrow>
      parent i < length holes \<and>
      concrete_hole_witness l r p C (hole_poss' C' ! i)
        (hole_poss' C ! (parent i)) (tail i)"
    using per_index by metis
  let ?parents = "map parent [0..<length holes']"
  let ?tails = "map tail [0..<length holes']"
  have point:
    "?parents ! i < length holes \<and>
     ?tails ! i \<in> poss (holes ! (?parents ! i)) \<and>
     holes' ! i = holes ! (?parents ! i) |_ (?tails ! i)"
    if i: "i < length holes'" for i
  proof -
    from selected[OF i] have parent: "parent i < length holes"
      and witness:
        "concrete_hole_witness l r p C (hole_poss' C' ! i)
          (hole_poss' C ! (parent i)) (tail i)"
      by blast+
    have parent_C: "parent i < num_holes C" using parent length by simp
    have old_at:
      "holes ! parent i = s |_ (hole_poss' C ! parent i)"
      using subt_at_fill_holes[OF length[symmetric] parent_C] source by simp
    from concrete_hole_witness_semantic[
      OF nd length source p_context redex witness]
    have tail_poss: "tail i \<in> poss (s |_ (hole_poss' C ! parent i))"
      and semantic:
        "t' |_ (hole_poss' C' ! i) =
          (s |_ (hole_poss' C ! parent i)) |_ tail i"
      unfolding t'_def by blast+
    have holes'_conv:
      "holes' = map (subt_at t') (hole_poss' C')"
      unfolding holes'_def C'_def t'_def
      using unfill_holes_conv[OF C'_prefix] unfolding C'_def t'_def by simp
    show ?thesis
      using i parent tail_poss semantic old_at holes'_conv
      by simp
  qed
  have parallel:
    "?tails ! i \<bottom> ?tails ! j"
    if i: "i < length holes'" and j: "j < length holes'"
      and distinct: "i \<noteq> j" and same: "?parents ! i = ?parents ! j"
    for i j
  proof -
    from selected[OF i] have witness_i:
      "concrete_hole_witness l r p C (hole_poss' C' ! i)
        (hole_poss' C ! (parent i)) (tail i)" by blast
    from selected[OF j] have witness_j:
      "concrete_hole_witness l r p C (hole_poss' C' ! j)
        (hole_poss' C ! (parent j)) (tail j)" by blast
    have parent_eq: "parent i = parent j" using same i j by simp
    have witness_j_same:
      "concrete_hole_witness l r p C (hole_poss' C' ! j)
        (hole_poss' C ! parent i) (tail j)"
      using witness_j parent_eq by simp
    have q_distinct: "hole_poss' C' ! i \<noteq> hole_poss' C' ! j"
      using distinct_hole_poss'[of C'] i j new_positions distinct
      by (metis distinct_conv_nth)
    have "tail i \<bottom> tail j"
      using concrete_hole_witness_same_parent_parallel[
        OF nd witness_i witness_j_same q_distinct] .
    then show ?thesis using i j by simp
  qed
  have "carrier_refinement holes' ?parents ?tails holes"
    unfolding carrier_refinement_def
    using point parallel by simp
  then show ?thesis by blast
qed

end
