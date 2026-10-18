theory Relative_ADP_Com_Order_Check
  imports Relative_ADP_Com_Reduction_Pair Ord.Term_Order_Impl
begin

definition rel_impl_adp_com_redpair where
  "rel_impl_adp_com_redpair rp = do {
    rel_impl_redpair rp;
    check (0 \<in> rel_impl.mono_af rp (Com2,2) \<and>
      1 \<in> rel_impl.mono_af rp (Com2,2))
      (showsl_lit (STR ''relative ADP order is not strict in both compound arguments''))
  }"

lemma rel_impl_adp_com_redpair_sound:
  fixes rp :: "('f adp_com_symbol,'v) rel_impl"
  assumes rp: "rel_impl rp"
    and checked: "isOK (rel_impl_adp_com_redpair rp)"
    and strict: "isOK (rel_impl_s rp strict_rules)"
    and weak: "isOK (rel_impl_ns rp weak_rules)"
  shows "\<exists>S NS NST. adp_com_redtriple_order S NS NST \<and>
    set strict_rules \<subseteq> S \<and> set weak_rules \<subseteq> NS"
proof -
  from checked have valid: "isOK (rel_impl_redpair rp)"
    and zero: "0 \<in> rel_impl.mono_af rp (Com2,2)"
    and one: "1 \<in> rel_impl.mono_af rp (Com2,2)"
    unfolding rel_impl_adp_com_redpair_def by auto
  from valid have flags: "isOK (rel_impl.valid rp)"
    "isOK (rel_impl.standard rp)" "isOK (rel_impl.SN rp)"
    "isOK (rel_impl.subst_s rp)"
    unfolding rel_impl_redpair_def by auto
  from rp[unfolded rel_impl_def, rule_format, OF flags(1),
      of "strict_rules @ weak_rules"]
  obtain S NS NST where properties:
    "rel_impl_prop rp (strict_rules @ weak_rules) S NS NST" by (elim exE) assumption
  with flags strict weak
  have s: "set strict_rules \<subseteq> S" and ns: "set weak_rules \<subseteq> NS"
    and mono: "af_monotone (rel_impl.mono_af rp) S"
    and facts: "S \<subseteq> NS" "ctxt.closed NS"
      "subst.closed NS" "subst.closed S" "S O NS \<subseteq> S"
      "NS O S \<subseteq> S" "trans NS" "trans S" "refl NS" "SN S"
    by (auto simp: rel_impl_list)
  have com: "adp_com_monotone S"
    unfolding adp_com_monotone_def
  proof (intro allI impI conjI)
    fix s t u :: "('f adp_com_symbol,'v) term"
    assume st: "(s,t) \<in> S"
    have left: "length [] \<in> rel_impl.mono_af rp (Com2, Suc (length [] + length [u]))"
      using zero by (simp add: numeral_2_eq_2)
    have right: "length [u] \<in> rel_impl.mono_af rp (Com2, Suc (length [u] + length []))"
      using one by (simp add: numeral_2_eq_2)
    show "(Fun Com2 [s,u], Fun Com2 [t,u]) \<in> S"
      using af_monotoneD[OF mono left st] by simp
    show "(Fun Com2 [u,s], Fun Com2 [u,t]) \<in> S"
      using af_monotoneD[OF mono right st] by simp
  qed
  have identity_subst: "subst.closed (Id :: (('f adp_com_symbol,'v) term \<times> ('f adp_com_symbol,'v) term) set)"
    by (rule subst.closedI) simp
  have general: "adp_com_redtriple_order S NS Id"
    by (unfold_locales; (intro facts com identity_subst)?)
      (auto simp: trans_def refl_on_def subst.closed_def)
  show ?thesis using general s ns by blast
qed

end
