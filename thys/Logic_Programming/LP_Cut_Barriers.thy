theory LP_Cut_Barriers
  imports LP_Cut_Source
begin

fun lp_cut_is_barrier where
  "lp_cut_is_barrier (LPCBarrier m) = True"
| "lp_cut_is_barrier e = False"

abbreviation lp_cut_barriers where
  "lp_cut_barriers es \<equiv> list_all lp_cut_is_barrier es"

lemma lp_cut_prune_append:
  "lp_cut_prune m (es@bs) =
    (if LPCBarrier m\<in>set es then lp_cut_prune m es@bs else lp_cut_prune m bs)"
  by (induct es) (auto split: lp_cut_entry.splits if_splits)

lemma lp_cut_barriers_prune:
  "lp_cut_barriers bs \<Longrightarrow> lp_cut_barriers (lp_cut_prune m bs)"
  by (induct bs) (auto split: lp_cut_entry.splits if_splits)

lemma lp_cut_prune_absent:
  "LPCBarrier m\<notin>set es \<Longrightarrow> lp_cut_prune m es=[]"
  by (induct es) (auto split: lp_cut_entry.splits)

lemma lp_cut_admin_append_barriers:
  assumes "s\<noteq>[]" "lp_cut_barriers bs" "lp_cut_admin (s@bs)=Some t"
  shows "\<exists>u cs. lp_cut_admin s=Some u \<and> lp_cut_barriers cs \<and> t=u@cs"
  using assms
proof (induct s rule: lp_cut_admin.induct)
  case (5 g gs es)
  show ?case using 5 lp_cut_barriers_prune[of bs]
    by (cases g) (auto simp: lp_cut_prune_append lp_cut_prune_absent split: if_splits)
qed auto

lemma lp_cut_source_append_barriers:
  assumes ne: "s\<noteq>[]" and bs: "lp_cut_barriers bs"
    and step: "(s@bs,t)\<in>lp_cut_source P"
  shows "\<exists>u cs. (s,u)\<in>lp_cut_source P \<and> lp_cut_barriers cs \<and> t=u@cs"
proof -
  obtain e es where s: "s=e#es" using ne by (cases s) auto
  from step show ?thesis
  proof cases
    case admin
    show ?thesis using lp_cut_admin_append_barriers[OF ne bs admin]
      by (blast intro: lp_cut_source.admin)
  qed (use bs in \<open>force simp: s lp_cut_fresh_def append_assoc
    intro: lp_cut_source.case_call lp_cut_source.resolve lp_cut_source.backtrack
      lp_cut_source.unify lp_cut_source.unify_fail lp_cut_source.meta lp_cut_source.meta_unlowerable\<close>)+
qed

lemma lp_cut_barriers_SN:
  "lp_cut_barriers bs \<Longrightarrow> SN_on (lp_cut_source P) {bs}"
proof (induct bs)
  case Nil
  show ?case by (rule step_reflects_SN_on) (auto elim: lp_cut_source.cases)
next
  case (Cons b bs)
  obtain m where b: "b=LPCBarrier m" using Cons.prems by (cases b) auto
  have tail: "SN_on (lp_cut_source P) {bs}" using Cons by simp
  show ?case by (rule step_reflects_SN_on)
    (use tail in \<open>auto simp: b elim: lp_cut_source.cases\<close>)
qed

theorem lp_cut_append_barriers_SN:
  fixes P :: "('f,'v) lp_cut_program"
    and s bs :: "('f lp_cut_symbol,'w) lp_iterm lp_cut_entry list"
  assumes sn: "SN_on (lp_cut_source P) {s}" and barriers: "lp_cut_barriers bs"
  shows "SN_on (lp_cut_source P) {s@bs}"
proof -
  have all: "\<forall>bs. lp_cut_barriers bs \<longrightarrow> SN_on (lp_cut_source P) {s@bs}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s bs :: "('f lp_cut_symbol,'w) lp_iterm lp_cut_entry list"
    assume ih: "\<And>t. (s,t)\<in>lp_cut_source P \<Longrightarrow>
      \<forall>cs. lp_cut_barriers cs \<longrightarrow> SN_on (lp_cut_source P) {t@cs}"
      and bs: "lp_cut_barriers bs"
    show "SN_on (lp_cut_source P) {s@bs}"
    proof (cases "s=[]")
      case True then show ?thesis using lp_cut_barriers_SN[OF bs, of P] by simp
    next
      case False
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix t assume step: "(s@bs,t)\<in>lp_cut_source P"
        obtain u cs where src: "(s,u)\<in>lp_cut_source P"
          and bar: "lp_cut_barriers cs" and shape: "t=u@cs"
          using lp_cut_source_append_barriers[OF False bs step] by blast
        show "SN_on (lp_cut_source P) {t}" using ih[OF src] bar shape by blast
      qed
    qed
  qed
  show ?thesis using all barriers by blast
qed

end
