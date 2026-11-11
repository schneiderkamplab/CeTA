theory LP_Source_Pending_Pumping
 imports LP_Source_Barrier_Pumping LP_Cut_NO_Pending
begin

text \<open>The existing pending-stack pump is shared with source relations that
include checked builtin steps. Nonempty targets exclude uncaught errors, which
can discard the entire stack. No executed cut may cross the retained suffix.\<close>

locale lp_pending_execution = lp_barrier_execution R
 for R :: "'a lp_cut_entry list rel" +
 assumes pending: "(s,t)\<in>R \<Longrightarrow> t\<noteq>[] \<Longrightarrow> lpc_no_suffix_safe s \<Longrightarrow>
   (\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
   (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {} \<Longrightarrow>
   (s @ bs,t @ bs)\<in>R"
begin

lemma path_pending:
  assumes path: "path s ts"
    and safe: "\<And>u. u \<in> set (s#ts) \<Longrightarrow> u\<noteq>[] \<and> lpc_no_suffix_safe u"
    and fresh: "\<And>u. u \<in> set ts \<Longrightarrow>
      (\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "path (s @ bs) (map (\<lambda>u. u @ bs) ts)"
  using assms
proof (induct ts arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have step: "(s,t) \<in> R" using Cons.prems(1) by simp
  have safe_s: "lpc_no_suffix_safe s" using Cons.prems(2)[of s] by simp
  have fresh_t: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
    using Cons.prems(3)[of t] by simp
  have head: "(s @ bs,t @ bs) \<in> R"
    by (rule pending[OF step _ safe_s fresh_t]) (use Cons.prems(2)[of t] in simp)
  have tail: "path (t @ bs) (map (\<lambda>u. u @ bs) ts)"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case using head tail by simp
qed

lemma path_progress:
  "path s (t#ts) \<Longrightarrow>
    (s,last (t#ts)) \<in> (R)\<^sup>+"
  by (induct ts arbitrary: s t)
    (auto intro: trancl_trans r_into_trancl)

theorem pending_pump:
  assumes path: "path s (t#ts)"
    and closes: "last (t#ts) = s @ extra"
    and safe: "\<And>u. u \<in> set (s#t#ts) \<Longrightarrow> u\<noteq>[] \<and> lpc_no_suffix_safe u"
    and core: "\<And>r. map (lp_cut_scope_entry r) s = s"
  shows "\<not> SN_on (R) {s @ bs}"
proof -
  have repeat: "\<exists>cs. (s @ bs,s @ cs) \<in> (R)\<^sup>+" for bs
  proof -
    let ?S = "\<Union>e\<in>set bs. lp_cut_entry_scopes e"
    let ?N = "Suc (Lattices_Big.linorder_class.Max (insert (0::nat) ?S))"
    let ?r = "\<lambda>m. ?N + m"
    have bound: "m < ?N" if "m \<in> ?S" for m
    proof -
      have finite: "finite (insert (0::nat) ?S)" using lpc_no_scopes_finite[of bs] by simp
      have member: "m \<in> insert (0::nat) ?S" using that by simp
      show ?thesis using Max_ge[OF finite member] by simp
    qed
    have outside: "?r m \<notin> ?S" for m using bound[of "?r m"] by arith
    have fresh: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter> ?S = {}"
      if "u \<in> set (map (map (lp_cut_scope_entry ?r)) (t#ts))" for u
      using that outside by (auto simp: lp_cut_scope_entry_scopes)
    have injective: "inj ?r" by (simp add: inj_on_def)
    have renamed: "path s (map (map (lp_cut_scope_entry ?r)) (t#ts))"
      using path_scopes[OF path injective] core by simp
    have renamed_safe: "u\<noteq>[] \<and> lpc_no_suffix_safe u"
      if "u \<in> set (s # map (map (lp_cut_scope_entry ?r)) (t#ts))" for u
      using that safe by (auto simp: lpc_no_safe_scopes)
    have lifted: "path (s @ bs)
      (map (\<lambda>u. u @ bs) (map (map (lp_cut_scope_entry ?r)) (t#ts)))"
      by (rule path_pending[OF renamed renamed_safe fresh])
    have progress: "(s @ bs,
      last (map (\<lambda>u. u @ bs) (map (map (lp_cut_scope_entry ?r)) (t#ts))))
      \<in> (R)\<^sup>+"
    proof -
      obtain v vs where eq: "map (\<lambda>u. u @ bs)
        (map (map (lp_cut_scope_entry ?r)) (t#ts)) = v#vs" by simp
      show ?thesis using path_progress[of "s @ bs" v vs] lifted eq by metis
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
  have successor: "\<forall>u\<in>?X. \<exists>v\<in>?X. (u,v) \<in> (R)\<^sup>+"
    using repeat by blast
  show ?thesis using lower_set_imp_not_SN_on[OF member successor] SN_on_trancl by blast
qed

end

lemma lpc_source_pending_execution:
 assumes "lp_cut_source_program P"
 shows "lp_pending_execution (lp_cut_mgu_source P)"
 by (rule lp_pending_execution.intro[OF lpc_source_barrier_execution[OF assms]])
   (unfold_locales; rule lpc_no_source_pending; assumption)

end
