theory LP_Cut_MGU_Stack
  imports LP_Cut_MGU_Equality LP_Cut_Stack_Split
begin

lemma lpc_mgu_source_append_barriers:
  assumes ne: "s\<noteq>[]" and bs: "lp_cut_barriers bs"
    and step: "(s@bs,t)\<in>lp_cut_mgu_source P"
  shows "\<exists>u cs. (s,u)\<in>lp_cut_mgu_source P \<and> lp_cut_barriers cs \<and> t=u@cs"
proof -
  obtain e es where s: "s=e#es" using ne by (cases s) auto
  from step show ?thesis
  proof cases
    case admin
    show ?thesis using lp_cut_admin_append_barriers[OF ne bs admin]
      by (blast intro: lp_cut_mgu_source.admin)
  qed (use bs in \<open>force simp: s lp_cut_fresh_def append_assoc
    intro: lp_cut_mgu_source.case_call lp_cut_mgu_source.resolve lp_cut_mgu_source.backtrack
      lp_cut_mgu_source.unify lp_cut_mgu_source.unify_fail lp_cut_mgu_source.meta lp_cut_mgu_source.meta_unlowerable\<close>)+
qed

lemma lpc_mgu_barriers_SN:
  "lp_cut_barriers bs \<Longrightarrow> SN_on (lp_cut_mgu_source P) {bs}"
proof (induct bs)
  case Nil
  show ?case by (rule step_reflects_SN_on) (auto elim: lp_cut_mgu_source.cases)
next
  case (Cons b bs)
  obtain m where b: "b=LPCBarrier m" using Cons.prems by (cases b) auto
  have tail: "SN_on (lp_cut_mgu_source P) {bs}" using Cons by simp
  show ?case by (rule step_reflects_SN_on)
    (use tail in \<open>auto simp: b elim: lp_cut_mgu_source.cases\<close>)
qed

theorem lpc_mgu_append_barriers_SN:
  fixes P :: "('f,string) lp_cut_program"
    and s bs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes sn: "SN_on (lp_cut_mgu_source P) {s}" and barriers: "lp_cut_barriers bs"
  shows "SN_on (lp_cut_mgu_source P) {s@bs}"
proof -
  have all: "\<forall>bs. lp_cut_barriers bs \<longrightarrow> SN_on (lp_cut_mgu_source P) {s@bs}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s bs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
    assume ih: "\<And>t. (s,t)\<in>lp_cut_mgu_source P \<Longrightarrow>
      \<forall>cs. lp_cut_barriers cs \<longrightarrow> SN_on (lp_cut_mgu_source P) {t@cs}"
      and bs: "lp_cut_barriers bs"
    show "SN_on (lp_cut_mgu_source P) {s@bs}"
    proof (cases "s=[]")
      case True then show ?thesis using lpc_mgu_barriers_SN[OF bs, of P] by simp
    next
      case False
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix t assume step: "(s@bs,t)\<in>lp_cut_mgu_source P"
        obtain u cs where src: "(s,u)\<in>lp_cut_mgu_source P"
          and bar: "lp_cut_barriers cs" and shape: "t=u@cs"
          using lpc_mgu_source_append_barriers[OF False bs step] by blast
        show "SN_on (lp_cut_mgu_source P) {t}" using ih[OF src] bar shape by blast
      qed
    qed
  qed
  show ?thesis using all barriers by blast
qed

lemma lpc_mgu_source_append_suffix:
  assumes ne: "s\<noteq>[]" and step: "(s@es,t)\<in>lp_cut_mgu_source P"
  shows "\<exists>u n. (s,u)\<in>lp_cut_mgu_source P \<and> t=u@drop n es"
proof -
  obtain e ss where s: "s=e#ss" using ne by (cases s) auto
  from step show ?thesis
  proof cases
    case admin
    show ?thesis using lpc_admin_append_suffix[OF ne admin]
      by (blast intro: lp_cut_mgu_source.admin)
  qed (use s in \<open>force simp: lp_cut_fresh_def append_assoc
    intro: exI[of _ 0] lp_cut_mgu_source.case_call lp_cut_mgu_source.resolve
      lp_cut_mgu_source.backtrack lp_cut_mgu_source.unify lp_cut_mgu_source.unify_fail
      lp_cut_mgu_source.meta lp_cut_mgu_source.meta_unlowerable\<close>)+
qed

lemma lpc_mgu_append_all_suffixes_SN:
  fixes P :: "('f,string) lp_cut_program"
    and s es :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes sn: "SN_on (lp_cut_mgu_source P) {s}"
    and suffix: "\<And>n. SN_on (lp_cut_mgu_source P) {drop n es}"
  shows "SN_on (lp_cut_mgu_source P) {s@es}"
proof -
  have all: "\<forall>es. (\<forall>n. SN_on (lp_cut_mgu_source P) {drop n es}) \<longrightarrow>
      SN_on (lp_cut_mgu_source P) {s@es}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s es :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
    assume ih: "\<And>u. (s,u)\<in>lp_cut_mgu_source P \<Longrightarrow>
      \<forall>es. (\<forall>n. SN_on (lp_cut_mgu_source P) {drop n es}) \<longrightarrow>
      SN_on (lp_cut_mgu_source P) {u@es}"
      and tails: "\<forall>n. SN_on (lp_cut_mgu_source P) {drop n es}"
    show "SN_on (lp_cut_mgu_source P) {s@es}"
    proof (cases "s=[]")
      case True then show ?thesis using tails[rule_format, of 0] by simp
    next
      case False
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix t assume "(s@es,t)\<in>lp_cut_mgu_source P"
        then obtain u n where step: "(s,u)\<in>lp_cut_mgu_source P"
          and t: "t=u@drop n es" using lpc_mgu_source_append_suffix[OF False] by blast
        show "SN_on (lp_cut_mgu_source P) {t}"
          using ih[OF step, rule_format, of "drop n es"] tails
          by (simp add: t drop_drop)
      qed
    qed
  qed
  show ?thesis using all suffix by blast
qed

theorem lpc_mgu_singleton_stack_SN:
  assumes "\<And>e. e\<in>set es \<Longrightarrow> SN_on (lp_cut_mgu_source P) {[e]}"
  shows "SN_on (lp_cut_mgu_source P) {es}"
  using assms
proof (induct es rule: length_induct)
  case (1 es)
  show ?case
  proof (cases es)
    case Nil
    show ?thesis unfolding Nil
      by (rule step_reflects_SN_on) (auto elim: lp_cut_mgu_source.cases)
  next
    case (Cons e ss)
    have first: "SN_on (lp_cut_mgu_source P) {[e]}" using "1.prems" Cons by simp
    have tails: "SN_on (lp_cut_mgu_source P) {drop n ss}" for n
      by (rule "1.hyps"[rule_format]) (use Cons "1.prems" in \<open>auto dest: in_set_dropD\<close>)
    show ?thesis using lpc_mgu_append_all_suffixes_SN[OF first tails] Cons by simp
  qed
qed


end

