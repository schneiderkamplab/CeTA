theory Relative_ADP_Base
  imports Relative_ADP_Bridge_Dev.Relative_ADP_Bridge
begin

lemma adp_defined_root_subterm_imp_position:
  assumes q: "q \<in> poss s"
    and root: "[] \<in> adp_defined_positions D (s |_ q)"
  shows "q \<in> adp_defined_positions D s"
proof -
  from root obtain f ts where at: "s |_ q = Fun f ts" and fD: "f \<in> D"
    unfolding adp_defined_positions_def by auto
  show ?thesis unfolding adp_defined_positions_def using q at fD by blast
qed

lemma direct_root_strict_origin_trace:
  fixes D :: "'f set"
  assumes wf: "wf_trs (R \<union> B)"
    and D: "D = adp_defined_symbols (R \<union> B)"
    and minimal: "s \<in> Tinf (relstep R B)"
    and root_defined: "[] \<in> adp_defined_positions D s"
    and rule: "(l, r) \<in> R"
    and redex: "s = l \<cdot> sigma"
    and target: "u = r \<cdot> sigma"
    and target_nt: "\<not> SN_on (relstep R B) {u}"
  obtains q A phi where
    "weak_pair_origin_trace R B D s s [] [] [] []"
    "origin_root_targets 1 D r A"
    "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    "origin_edge l r [] sigma A phi [] q"
    "q \<in> adp_defined_positions D u"
    "u |_ q \<in> Tinf (relstep R B)"
proof -
  obtain v where uv: "u \<unrhd> v" and v_minimal: "v \<in> Tinf (relstep R B)"
    using not_SN_imp_subt_Tinf[OF target_nt] by blast
  obtain q where q_poss: "q \<in> poss u" and q_at: "u |_ q = v"
    using supteq_imp_subt_at[OF uv] by blast
  have q_minimal: "u |_ q \<in> Tinf (relstep R B)"
    using v_minimal q_at by simp
  have local_root: "[] \<in> adp_defined_positions D (u |_ q)"
    unfolding D by (rule Tinf_root_is_adp_defined[OF wf q_minimal])
  have q_defined: "q \<in> adp_defined_positions D u"
    by (rule adp_defined_root_subterm_imp_position[OF q_poss local_root])
  have q_nonterminating: "\<not> SN_on (relstep R B) {u |_ q}"
    using q_minimal unfolding Tinf_def by blast
  have vars: "vars_term r \<subseteq> vars_term l"
    using wf rule unfolding wf_trs_def by blast
  obtain A phi q' where targets: "origin_root_targets 1 D r A"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and q'_nt: "q' \<in> nonterminating_defined_positions R B D s"
    and edge: "origin_edge l r [] sigma A phi q' q"
  proof (rule strict_rewrite_pulls_back_target[
        OF rule vars empty_pos_in_poss root_defined])
    show "s |_ [] = l \<cdot> sigma" using redex by simp
    show "q \<in> nonterminating_defined_positions R B D
        (replace_at s [] (r \<cdot> sigma))"
      unfolding nonterminating_defined_positions_def
      using q_defined q_nonterminating redex target by simp
  qed
  have nt_root: "nonterminating_defined_positions R B D s = {[]}"
    by (rule minimal_nonterminating_defined_positions_root[
          OF minimal root_defined])
  have q': "q' = []" using q'_nt unfolding nt_root by simp
  have trace: "weak_pair_origin_trace R B D s s [] [] [] []"
    by (rule weak_pair_origin_trace.refl)
  show thesis by (rule that[OF trace targets valid])
    (use edge q' q_defined q_minimal in auto)
qed

end
