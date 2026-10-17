theory Relative_ADP_Inner_State
  imports Relative_ADP_Context_State_Dev.Relative_ADP_Context_State
begin

lemma context_position_safe_below_indexed_hole:
  assumes length: "num_holes C = length holes"
    and i: "i < length holes"
    and ctxt_pos: "q \<in> poss_mctxt C"
  shows "q <\<^sub>p (hole_poss' C ! i @ beta) \<or>
    parallel_pos q (hole_poss' C ! i @ beta)"
proof -
  have i_holes: "i < num_holes C" using length i by simp
  have hole: "hole_poss' C ! i \<in> hole_poss C"
    using set_hole_poss'[of C] i_holes by auto
  show ?thesis
    by (rule context_pos_above_or_parallel_below_hole[OF ctxt_pos hole])
qed

lemma relative_context_origin_state_inner_strict:
  assumes state: "relative_context_origin_state R B D s t C holes"
    and i: "i < length holes"
    and rule: "(l, r) \<in> R"
    and p: "p = hole_poss' C ! i @ beta"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and target:
      "fill_holes C (holes[i := ti]) = replace_at t p (r \<cdot> sigma)"
  shows "relative_context_origin_state R B D s
    (fill_holes C (holes[i := ti])) C (holes[i := ti])"
proof -
  from state have length: "num_holes C = length holes"
    and source: "fill_holes C holes = t"
    and traces: "\<And>q1 q2. q1 \<in> poss_mctxt C \<Longrightarrow>
      q2 \<in> poss_mctxt C \<Longrightarrow>
      q1 \<in> adp_defined_positions D t \<Longrightarrow>
      q2 \<in> adp_defined_positions D t \<Longrightarrow>
      weak_pair_origin_trace R B D s t [] [] q1 q2"
    unfolding relative_context_origin_state_def by blast+
  have updated_length: "num_holes C = length (holes[i := ti])"
    using length by simp
  have updated_trace:
    "weak_pair_origin_trace R B D s (fill_holes C (holes[i := ti]))
      [] [] q1 q2"
    if q1: "q1 \<in> poss_mctxt C" and q2: "q2 \<in> poss_mctxt C"
      and q1_defined: "q1 \<in> adp_defined_positions D
        (fill_holes C (holes[i := ti]))"
      and q2_defined: "q2 \<in> adp_defined_positions D
        (fill_holes C (holes[i := ti]))"
    for q1 q2
  proof -
    have safe1: "q1 <\<^sub>p p \<or> parallel_pos q1 p"
      unfolding p
      by (rule context_position_safe_below_indexed_hole[OF length i q1])
    have safe2: "q2 <\<^sub>p p \<or> parallel_pos q2 p"
      unfolding p
      by (rule context_position_safe_below_indexed_hole[OF length i q2])
    have p_poss: "p \<in> poss t" by (rule fun_poss_imp_poss[OF p_fun])
    have q1_before: "q1 \<in> adp_defined_positions D t"
      by (rule adp_defined_position_preserved_outside[OF p_poss])
         (use q1_defined target safe1 in auto)
    have q2_before: "q2 \<in> adp_defined_positions D t"
      by (rule adp_defined_position_preserved_outside[OF p_poss])
         (use q2_defined target safe2 in auto)
    have trace_target:
      "weak_pair_origin_trace R B D s (replace_at t p (r \<cdot> sigma))
        [] [] q1 q2"
      by (rule weak_pair_origin_trace.strict_prefix[
            OF traces[OF q1 q2 q1_before q2_before]
              rule p_fun redex safe1 safe2])
    show ?thesis using trace_target target by simp
  qed
  show ?thesis
    unfolding relative_context_origin_state_def
    using updated_length updated_trace by blast
qed

lemma relative_context_origin_state_inner_base:
  assumes state: "relative_context_origin_state R B D s t C holes"
    and i: "i < length holes"
    and rule: "(l, r) \<in> B"
    and targets: "origin_root_targets 2 D r A"
    and nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p = hole_poss' C ! i @ beta"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and target:
      "fill_holes C (holes[i := ti]) = replace_at t p (r \<cdot> sigma)"
  shows "relative_context_origin_state R B D s
    (fill_holes C (holes[i := ti])) C (holes[i := ti])"
proof -
  from state have length: "num_holes C = length holes"
    and traces: "\<And>q1 q2. q1 \<in> poss_mctxt C \<Longrightarrow>
      q2 \<in> poss_mctxt C \<Longrightarrow>
      q1 \<in> adp_defined_positions D t \<Longrightarrow>
      q2 \<in> adp_defined_positions D t \<Longrightarrow>
      weak_pair_origin_trace R B D s t [] [] q1 q2"
    unfolding relative_context_origin_state_def by blast+
  have updated_length: "num_holes C = length (holes[i := ti])"
    using length by simp
  have updated_trace:
    "weak_pair_origin_trace R B D s (fill_holes C (holes[i := ti]))
      [] [] q1 q2"
    if q1: "q1 \<in> poss_mctxt C" and q2: "q2 \<in> poss_mctxt C"
      and q1_defined: "q1 \<in> adp_defined_positions D
        (fill_holes C (holes[i := ti]))"
      and q2_defined: "q2 \<in> adp_defined_positions D
        (fill_holes C (holes[i := ti]))"
    for q1 q2
  proof -
    have safe1: "q1 <\<^sub>p p \<or> parallel_pos q1 p"
      unfolding p
      by (rule context_position_safe_below_indexed_hole[OF length i q1])
    have safe2: "q2 <\<^sub>p p \<or> parallel_pos q2 p"
      unfolding p
      by (rule context_position_safe_below_indexed_hole[OF length i q2])
    have p_poss: "p \<in> poss t" by (rule fun_poss_imp_poss[OF p_fun])
    have q1_before: "q1 \<in> adp_defined_positions D t"
      by (rule adp_defined_position_preserved_outside[OF p_poss])
         (use q1_defined target safe1 in auto)
    have q2_before: "q2 \<in> adp_defined_positions D t"
      by (rule adp_defined_position_preserved_outside[OF p_poss])
         (use q2_defined target safe2 in auto)
    have edge1: "origin_edge l r p sigma A (covering_vrf l r) q1 q1"
      by (rule origin_edge.preserved[OF safe1])
    have edge2: "origin_edge l r p sigma A (covering_vrf l r) q2 q2"
      by (rule origin_edge.preserved[OF safe2])
    have trace_target:
      "weak_pair_origin_trace R B D s (replace_at t p (r \<cdot> sigma))
        [] [] q1 q2"
      by (rule weak_pair_origin_trace.step[
            OF traces[OF q1 q2 q1_before q2_before]
              rule targets nondup p_fun redex edge1 edge2])
    show ?thesis using trace_target target by simp
  qed
  show ?thesis
    unfolding relative_context_origin_state_def
    using updated_length updated_trace by blast
qed

end
