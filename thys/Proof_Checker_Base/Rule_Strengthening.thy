theory Rule_Strengthening
  imports First_Order_Rewriting.Trs_Impl Framework.QDP_Framework_Impl
begin

text \<open>A general strengthening check, not specific to string rewriting:
each original rule must be one actual rewrite step of the proposed system.
Context and substitution closure then simulate every original rewrite step.\<close>

definition rule_strengthens :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> bool" where
  "rule_strengthens R S = list_all (\<lambda>(l,r). r \<in> set (rewrite S l)) R"

lemma rule_strengthens_steps:
  assumes "rule_strengthens R S"
  shows "rstep (set R) \<subseteq> rstep (set S)"
proof (rule rstep_subset)
  show "ctxt.closed (rstep (set S))" by (rule ctxt_closed_rstep)
  show "subst.closed (rstep (set S))" by (rule subst_closed_rstep)
  show "set R \<subseteq> rstep (set S)"
    using assms unfolding rule_strengthens_def list_all_iff
    by (auto intro: rewrite_sound)
qed

lemma rule_strengthens_SN:
  assumes "rule_strengthens R S" "SN (rstep (set S))"
  shows "SN (rstep (set R))"
  using SN_subset[OF assms(2) rule_strengthens_steps[OF assms(1)]] .

definition rule_strengthening_tt ::
  "('tp, 'f::showl, 'v::showl) tp_ops \<Rightarrow> ('f,'v) rules \<Rightarrow> 'tp proc" where
  "rule_strengthening_tt I S tp = check_return (do {
    check (tp_ops.Q I tp = []) (showsl_lit (STR ''rule strengthening requires empty Q''));
    check (tp_ops.Rw I tp = []) (showsl_lit (STR ''rule strengthening requires no weak rules''));
    check (rule_strengthens (tp_ops.R I tp) S)
      (showsl_lit (STR ''an original rule is not a rewrite step of the stronger system''))
  }) (tp_ops.mk I False [] S [])"

lemma (in tp_spec) rule_strengthening_tt_sound:
  "sound_tt_impl (rule_strengthening_tt I S)"
proof
  fix tp tp'
  assume step: "rule_strengthening_tt I S tp = return tp'"
    and fin: "SN_qrel (qreltrs tp')"
  from step have Q: "Q tp = []" and W: "Rw tp = []"
    and stronger: "rule_strengthens (R tp) S"
    and target: "tp' = mk False [] S []"
    unfolding rule_strengthening_tt_def by auto
  from fin have "SN (rstep (set S))" unfolding target mk_sound by simp
  from rule_strengthens_SN[OF stronger this] show "SN_qrel (qreltrs tp)"
    unfolding qreltrs_sound Q W by simp
qed

end
