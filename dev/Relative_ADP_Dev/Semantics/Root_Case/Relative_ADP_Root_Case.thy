theory Relative_ADP_Root_Case
  imports Relative_ADP_Prefix_Dev.Relative_ADP_Prefix
begin

lemma first_root_strict_origin_witness:
  fixes D :: "'f set"
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and D: "D = adp_defined_symbols (R \<union> B)"
    and minimal: "s \<in> Tinf (relstep R B)"
    and prefix: "(s, t) \<in> (nrrstep (R \<union> B))\<^sup>*"
    and root_step: "(t, u) \<in> rrstep R"
    and target_nt: "\<not> SN_on (relstep R B) {u}"
  obtains q l r A phi sigma where
    "weak_pair_origin_trace R B D s t [] [] [] []"
    "(l, r) \<in> R"
    "origin_root_targets 1 D r A"
    "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    "t |_ [] = l \<cdot> sigma"
    "u = replace_at t [] (r \<cdot> sigma)"
    "origin_edge l r [] sigma A phi [] q"
    "q \<in> adp_defined_positions D u"
    "u |_ q \<in> Tinf (relstep R B)"
proof -
  have trace: "weak_pair_origin_trace R B D s t [] [] [] []"
    by (rule nonroot_steps_root_origin_trace[OF wf nd prefix])
  have t_minimal: "t \<in> Tinf (relstep R B)"
  proof -
    have target_step: "(t, u) \<in> rstep R \<union> rstep B"
      using root_step unfolding rstep_iff_rrstep_or_nrrstep by auto
    have t_nt: "\<not> SN_on (relstep R B) {t}"
      by (rule nontermination_backwards_rewrite[OF target_step target_nt])
    show ?thesis by (rule Tinf_nrrsteps_local[OF minimal prefix t_nt])
  qed
  obtain l r sigma where rule: "(l, r) \<in> R"
    and t: "t = l \<cdot> sigma" and u: "u = r \<cdot> sigma"
    using root_step by (auto elim: rrstepE)
  have t_root: "[] \<in> adp_defined_positions D t"
    unfolding D by (rule Tinf_root_is_adp_defined[OF wf t_minimal])
  obtain q A phi where targets: "origin_root_targets 1 D r A"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and edge: "origin_edge l r [] sigma A phi [] q"
    and q_defined: "q \<in> adp_defined_positions D u"
    and q_minimal: "u |_ q \<in> Tinf (relstep R B)"
    by (rule direct_root_strict_origin_trace[
          OF wf D t_minimal t_root rule t u target_nt]) blast+
  have redex: "t |_ [] = l \<cdot> sigma" using t by simp
  have target: "u = replace_at t [] (r \<cdot> sigma)" using t u by simp
  show thesis by (rule that[OF trace rule targets valid redex target edge
        q_defined q_minimal])
qed

end
