theory LP_Cut_Domain_NO_Pending
  imports LP_Cut_Domain_NO_Pumping
begin

context cut_runtime_domain
begin


lemma no_admin_pending:
  assumes "lp_cut_admin s = Some t" "lpc_no_suffix_safe s"
  shows "lp_cut_admin (s @ bs) = Some (t @ bs)"
  using assms
  by (induct s rule: lp_cut_admin.induct)
    (auto split: lp_cut_goal.splits)

lemma no_source_pending:
  assumes step: "(s,t) \<in> mgu_source P"
    and safe: "lpc_no_suffix_safe s"
    and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "(s @ bs,t @ bs) \<in> mgu_source P"
  using step fresh safe
proof (cases rule: mgu_source.cases)
  case admin
  show ?thesis using no_admin_pending[OF admin safe]
    by (rule mgu_source.admin)
qed (force simp: lp_cut_fresh_def append_assoc
  intro: mgu_source.case_call mgu_source.resolve mgu_source.backtrack
    mgu_source.unify mgu_source.unify_fail mgu_source.meta
    )+

lemma no_path_pending:
  assumes path: "no_path P s ts"
    and safe: "\<And>u. u \<in> set (s#ts) \<Longrightarrow> lpc_no_suffix_safe u"
    and fresh: "\<And>u. u \<in> set ts \<Longrightarrow>
      (\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "no_path P (s @ bs) (map (\<lambda>u. u @ bs) ts)"
  using assms
proof (induct ts arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have step: "(s,t) \<in> mgu_source P" using Cons.prems(1) by simp
  have safe_s: "lpc_no_suffix_safe s" using Cons.prems(2)[of s] by simp
  have fresh_t: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
    using Cons.prems(3)[of t] by simp
  have head: "(s @ bs,t @ bs) \<in> mgu_source P"
    by (rule no_source_pending[OF step safe_s fresh_t])
  have tail: "no_path P (t @ bs) (map (\<lambda>u. u @ bs) ts)"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case using head tail by simp
qed

lemma no_path_progress:
  "no_path P s (t#ts) \<Longrightarrow>
    (s,last (t#ts)) \<in> (mgu_source P)\<^sup>+"
  by (induct ts arbitrary: s t)
    (auto intro: trancl_trans r_into_trancl)

lemma no_safe_scopes:
  "lpc_no_suffix_safe (map (lp_cut_scope_entry r) s) = lpc_no_suffix_safe s"
  by (cases s rule: lpc_no_suffix_safe.cases) auto

theorem no_pending_pump:
  assumes program: "lp_cut_source_program P"
    and path: "no_path P s (t#ts)"
    and closes: "last (t#ts) = s @ extra"
    and safe: "\<And>u. u \<in> set (s#t#ts) \<Longrightarrow> lpc_no_suffix_safe u"
    and core: "\<And>r. map (lp_cut_scope_entry r) s = s"
  shows "\<not> SN_on (mgu_source P) {s @ bs}"
proof -
  have repeat: "\<exists>cs. (s @ bs,s @ cs) \<in> (mgu_source P)\<^sup>+" for bs
  proof -
    let ?S = "\<Union>e\<in>set bs. lp_cut_entry_scopes e"
    let ?N = "Suc (Lattices_Big.linorder_class.Max (insert (0::nat) ?S))"
    let ?r = "\<lambda>m. ?N + m"
    have bound: "m < ?N" if "m \<in> ?S" for m
    proof -
      have finite: "finite (insert (0::nat) ?S)" using no_scopes_finite[of bs] by simp
      have member: "m \<in> insert (0::nat) ?S" using that by simp
      show ?thesis using Max_ge[OF finite member] by simp
    qed
    have outside: "?r m \<notin> ?S" for m using bound[of "?r m"] by arith
    have fresh: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter> ?S = {}"
      if "u \<in> set (map (map (lp_cut_scope_entry ?r)) (t#ts))" for u
      using that outside by (auto simp: lp_cut_scope_entry_scopes)
    have injective: "inj ?r" by (simp add: inj_on_def)
    have renamed: "no_path P s (map (map (lp_cut_scope_entry ?r)) (t#ts))"
      using no_path_scopes[OF path injective program] core by simp
    have renamed_safe: "lpc_no_suffix_safe u"
      if "u \<in> set (s # map (map (lp_cut_scope_entry ?r)) (t#ts))" for u
      using that safe by (auto simp: no_safe_scopes)
    have lifted: "no_path P (s @ bs)
      (map (\<lambda>u. u @ bs) (map (map (lp_cut_scope_entry ?r)) (t#ts)))"
      by (rule no_path_pending[OF renamed renamed_safe fresh])
    have progress: "(s @ bs,
      last (map (\<lambda>u. u @ bs) (map (map (lp_cut_scope_entry ?r)) (t#ts))))
      \<in> (mgu_source P)\<^sup>+"
    proof -
      obtain v vs where eq: "map (\<lambda>u. u @ bs)
        (map (map (lp_cut_scope_entry ?r)) (t#ts)) = v#vs" by simp
      show ?thesis using no_path_progress[of P "s @ bs" v vs] lifted eq by metis
    qed
    have last_eq: "last (map (\<lambda>u. u @ bs) (map (map (lp_cut_scope_entry ?r)) (t#ts))) =
      s @ (map (lp_cut_scope_entry ?r) extra @ bs)"
    proof -
      have ne: "t#ts \<noteq> []" by simp
      have inner: "last (map (map (lp_cut_scope_entry ?r)) (t#ts)) =
        s @ map (lp_cut_scope_entry ?r) extra"
        using last_map[OF ne, of "map (lp_cut_scope_entry ?r)"]
        by (simp only: closes map_append core)
      have nonempty: "map (map (lp_cut_scope_entry ?r)) (t#ts) \<noteq> []" by simp
      show ?thesis using last_map[OF nonempty, of "\<lambda>u. u @ bs"]
        by (simp only: inner append_assoc)
    qed
    show ?thesis using progress by (auto simp only: last_eq)
  qed
  let ?X = "{s @ cs |cs. True}"
  have member: "s @ bs \<in> ?X" by blast
  have successor: "\<forall>u\<in>?X. \<exists>v\<in>?X. (u,v) \<in> (mgu_source P)\<^sup>+"
    using repeat by blast
  show ?thesis using lower_set_imp_not_SN_on[OF member successor] SN_on_trancl by blast
qed

end
end
