theory LP_Cut_Stack_Split
  imports LP_Cut_Barriers
begin

text \<open>Conservative decomposition of an ordered alternative stack. All
singleton alternatives are obligations. Unlike unrestricted binary Parallel,
this cannot hide a nonterminating suffix behind a newly reachable cut. No
substitution is shared between saved alternatives.\<close>

lemma lpc_prune_is_suffix:
  "\<exists>n. lp_cut_prune m es = drop n es"
proof (induct es)
  case Nil then show ?case by simp
next
  case (Cons e es)
  then obtain n where n: "lp_cut_prune m es = drop n es" by blast
  show ?case
    by (cases e) (auto simp: n intro: exI[of _ 0] exI[of _ "Suc n"])
qed

lemma lpc_admin_append_suffix:
  assumes "s\<noteq>[]" "lp_cut_admin (s@es)=Some t"
  shows "\<exists>u n. lp_cut_admin s=Some u \<and> t=u@drop n es"
  using assms
proof (induct s rule: lp_cut_admin.induct)
  case (5 g gs ss)
  show ?case
  proof (cases g)
    case (LPCCut m)
    obtain n where n: "lp_cut_prune m es = drop n es"
      using lpc_prune_is_suffix by blast
    show ?thesis using 5 LPCCut n
      by (auto simp: lp_cut_prune_append lp_cut_prune_absent
        split: if_splits intro: exI[of _ 0] exI[of _ n])
  qed (use 5 in \<open>auto intro: exI[of _ 0]\<close>)
qed (auto intro: exI[of _ 0])

lemma lpc_source_append_suffix:
  assumes ne: "s\<noteq>[]" and step: "(s@es,t)\<in>lp_cut_source P"
  shows "\<exists>u n. (s,u)\<in>lp_cut_source P \<and> t=u@drop n es"
proof -
  obtain e ss where s: "s=e#ss" using ne by (cases s) auto
  from step show ?thesis
  proof cases
    case admin
    show ?thesis using lpc_admin_append_suffix[OF ne admin]
      by (blast intro: lp_cut_source.admin)
  qed (use s in \<open>force simp: lp_cut_fresh_def append_assoc
    intro: exI[of _ 0] lp_cut_source.case_call lp_cut_source.resolve
      lp_cut_source.backtrack lp_cut_source.unify lp_cut_source.unify_fail
      lp_cut_source.meta lp_cut_source.meta_unlowerable\<close>)+
qed

lemma lpc_append_all_suffixes_SN:
  fixes P :: "('f,'v) lp_cut_program"
    and s es :: "('f lp_cut_symbol,'w) lp_iterm lp_cut_entry list"
  assumes sn: "SN_on (lp_cut_source P) {s}"
    and suffix: "\<And>n. SN_on (lp_cut_source P) {drop n es}"
  shows "SN_on (lp_cut_source P) {s@es}"
proof -
  have all: "\<forall>es. (\<forall>n. SN_on (lp_cut_source P) {drop n es}) \<longrightarrow>
      SN_on (lp_cut_source P) {s@es}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s es :: "('f lp_cut_symbol,'w) lp_iterm lp_cut_entry list"
    assume ih: "\<And>u. (s,u)\<in>lp_cut_source P \<Longrightarrow>
      \<forall>es. (\<forall>n. SN_on (lp_cut_source P) {drop n es}) \<longrightarrow>
      SN_on (lp_cut_source P) {u@es}"
      and tails: "\<forall>n. SN_on (lp_cut_source P) {drop n es}"
    show "SN_on (lp_cut_source P) {s@es}"
    proof (cases "s=[]")
      case True then show ?thesis using tails[rule_format, of 0] by simp
    next
      case False
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix t assume "(s@es,t)\<in>lp_cut_source P"
        then obtain u n where step: "(s,u)\<in>lp_cut_source P"
          and t: "t=u@drop n es" using lpc_source_append_suffix[OF False] by blast
        show "SN_on (lp_cut_source P) {t}"
          using ih[OF step, rule_format, of "drop n es"] tails
          by (simp add: t drop_drop)
      qed
    qed
  qed
  show ?thesis using all suffix by blast
qed

theorem lpc_singleton_stack_SN:
  assumes "\<And>e. e\<in>set es \<Longrightarrow> SN_on (lp_cut_source P) {[e]}"
  shows "SN_on (lp_cut_source P) {es}"
  using assms
proof (induct es rule: length_induct)
  case (1 es)
  show ?case
  proof (cases es)
    case Nil
    show ?thesis unfolding Nil
      by (rule step_reflects_SN_on) (auto elim: lp_cut_source.cases)
  next
    case (Cons e ss)
    have first: "SN_on (lp_cut_source P) {[e]}" using "1.prems" Cons by simp
    have tails: "SN_on (lp_cut_source P) {drop n ss}" for n
      by (rule "1.hyps"[rule_format]) (use Cons "1.prems" in \<open>auto dest: in_set_dropD\<close>)
    show ?thesis using lpc_append_all_suffixes_SN[OF first tails] Cons by simp
  qed
qed

end
