theory Relative_ADP_Outer_State
  imports Relative_ADP_Inner_State_Dev.Relative_ADP_Inner_State
begin

definition base_context_pair_transfer ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow>
    ('f, 'v, 'v) gsubst \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> bool" where
  "base_context_pair_transfer l r p sigma D s t C C' \<longleftrightarrow>
    (\<forall>q1 \<in> poss_mctxt C'. \<forall>q2 \<in> poss_mctxt C'.
      q1 \<in> adp_defined_positions D t \<longrightarrow>
      q2 \<in> adp_defined_positions D t \<longrightarrow>
      (\<exists>A p1 p2.
        origin_root_targets 2 D r A \<and>
        p1 \<in> poss_mctxt C \<and> p2 \<in> poss_mctxt C \<and>
        p1 \<in> adp_defined_positions D s \<and>
        p2 \<in> adp_defined_positions D s \<and>
        origin_edge l r p sigma A (covering_vrf l r) p1 q1 \<and>
        origin_edge l r p sigma A (covering_vrf l r) p2 q2))"

lemma relative_context_origin_state_outer_base:
  assumes state: "relative_context_origin_state R B D s t C holes"
    and rule: "(l, r) \<in> B"
    and nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and target: "fill_holes C' holes' = replace_at t p (r \<cdot> sigma)"
    and length: "num_holes C' = length holes'"
    and transfer: "base_context_pair_transfer l r p sigma D t
      (fill_holes C' holes') C C'"
  shows "relative_context_origin_state R B D s
    (fill_holes C' holes') C' holes'"
proof -
  from state have traces:
    "\<And>q1 q2. q1 \<in> poss_mctxt C \<Longrightarrow>
      q2 \<in> poss_mctxt C \<Longrightarrow>
      q1 \<in> adp_defined_positions D t \<Longrightarrow>
      q2 \<in> adp_defined_positions D t \<Longrightarrow>
      weak_pair_origin_trace R B D s t [] [] q1 q2"
    unfolding relative_context_origin_state_def by blast
  have new_trace:
    "weak_pair_origin_trace R B D s (fill_holes C' holes') [] [] q1 q2"
    if q1: "q1 \<in> poss_mctxt C'" and q2: "q2 \<in> poss_mctxt C'"
      and q1_defined: "q1 \<in> adp_defined_positions D (fill_holes C' holes')"
      and q2_defined: "q2 \<in> adp_defined_positions D (fill_holes C' holes')"
    for q1 q2
  proof -
    obtain A p1 p2 where targets: "origin_root_targets 2 D r A"
      and p1: "p1 \<in> poss_mctxt C" and p2: "p2 \<in> poss_mctxt C"
      and p1_defined: "p1 \<in> adp_defined_positions D t"
      and p2_defined: "p2 \<in> adp_defined_positions D t"
      and edge1: "origin_edge l r p sigma A (covering_vrf l r) p1 q1"
      and edge2: "origin_edge l r p sigma A (covering_vrf l r) p2 q2"
      using transfer q1 q2 q1_defined q2_defined
      unfolding base_context_pair_transfer_def by blast
    have trace_target:
      "weak_pair_origin_trace R B D s (replace_at t p (r \<cdot> sigma))
        [] [] q1 q2"
      by (rule weak_pair_origin_trace.step[
            OF traces[OF p1 p2 p1_defined p2_defined]
              rule targets nondup p_fun redex edge1 edge2])
    show ?thesis using trace_target target by simp
  qed
  show ?thesis
    unfolding relative_context_origin_state_def
    using length new_trace by blast
qed

lemma base_context_pair_transferD:
  assumes transfer: "base_context_pair_transfer l r p sigma D s t C C'"
    and q1: "q1 \<in> poss_mctxt C'" and q2: "q2 \<in> poss_mctxt C'"
    and q1_defined: "q1 \<in> adp_defined_positions D t"
    and q2_defined: "q2 \<in> adp_defined_positions D t"
  obtains A p1 p2 where
    "origin_root_targets 2 D r A"
    "p1 \<in> poss_mctxt C" "p2 \<in> poss_mctxt C"
    "p1 \<in> adp_defined_positions D s" "p2 \<in> adp_defined_positions D s"
    "origin_edge l r p sigma A (covering_vrf l r) p1 q1"
    "origin_edge l r p sigma A (covering_vrf l r) p2 q2"
proof -
  obtain A p1 p2 where
    "origin_root_targets 2 D r A"
    "p1 \<in> poss_mctxt C" "p2 \<in> poss_mctxt C"
    "p1 \<in> adp_defined_positions D s" "p2 \<in> adp_defined_positions D s"
    "origin_edge l r p sigma A (covering_vrf l r) p1 q1"
    "origin_edge l r p sigma A (covering_vrf l r) p2 q2"
    using transfer q1 q2 q1_defined q2_defined
    unfolding base_context_pair_transfer_def by blast
  then show thesis by (rule that)
qed

end
