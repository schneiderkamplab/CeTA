theory LP_Source_Barrier_Pumping
  imports LP_Cut_NO_Pumping
begin

locale lp_barrier_execution =
  fixes R :: "'a lp_cut_entry list rel"
  assumes scoped: "(s,t)\<in>R \<Longrightarrow> inj r \<Longrightarrow>
    (map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>R"
    and extend: "(s,t)\<in>R \<Longrightarrow> lp_cut_barriers bs \<Longrightarrow>
      (\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {} \<Longrightarrow>
      \<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and> (s@bs,t@cs)\<in>R"
begin

fun path where
  "path s [] = True"
| "path s (t#ts) = ((s,t) \<in> R \<and> path t ts)"

lemma path_extend:
  assumes path: "path s ts" and barriers: "lp_cut_barriers bs"
    and fresh: "\<And>t. t \<in> set ts \<Longrightarrow>
      (\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "\<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and>
    (s @ bs, last (s#ts) @ cs) \<in> (R)\<^sup>*"
  using path barriers fresh
proof (induct ts arbitrary: s bs)
  case Nil then show ?case by auto
next
  case (Cons t ts)
  have step: "(s,t) \<in> R" using Cons.prems(1) by simp
  have fresh_t: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}" using Cons.prems(3)[of t] by simp
  obtain ds where ds: "lp_cut_barriers ds" "set ds \<subseteq> set bs"
    "(s @ bs,t @ ds) \<in> R"
    using extend[OF step Cons.prems(2) fresh_t] by blast
  have fresh: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set ds. lp_cut_entry_scopes e) = {}" if "u \<in> set ts" for u
    using Cons.prems(3)[of u] ds(2) that by auto
  obtain cs where cs: "lp_cut_barriers cs" "set cs \<subseteq> set ds"
    "(t @ ds,last (t#ts) @ cs) \<in> (R)\<^sup>*"
    using Cons.hyps[OF _ ds(1) fresh] Cons.prems(1) by auto
  have joined: "(s @ bs,last (t#ts) @ cs) \<in> (R)\<^sup>*"
    using ds(3) cs(3) by (meson rtrancl_trans r_into_rtrancl)
  have subset: "set cs \<subseteq> set bs" using ds(2) cs(2) by blast
  show ?case by (rule exI[of _ cs]) (use cs(1) subset joined in simp)
qed

lemma path_extend_progress:
  assumes path: "path s (t#ts)" and barriers: "lp_cut_barriers bs"
    and fresh: "\<And>u. u \<in> set (t#ts) \<Longrightarrow>
      (\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "\<exists>cs. lp_cut_barriers cs \<and>
    (s @ bs,last (t#ts) @ cs) \<in> (R)\<^sup>+"
proof -
  have step: "(s,t) \<in> R" using path by simp
  have fresh_t: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}" using fresh[of t] by simp
  obtain ds where ds: "lp_cut_barriers ds" "set ds \<subseteq> set bs"
    "(s @ bs,t @ ds) \<in> R"
    using extend[OF step barriers fresh_t] by blast
  have fresh_tail: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set ds. lp_cut_entry_scopes e) = {}" if "u \<in> set ts" for u
    using fresh[of u] ds(2) that by auto
  have tail: "path t ts" using path by simp
  obtain cs where "lp_cut_barriers cs"
    "(t @ ds,last (t#ts) @ cs) \<in> (R)\<^sup>*"
    using path_extend[OF tail ds(1) fresh_tail] by blast
  then show ?thesis using ds(3) by (meson rtrancl_into_trancl2)
qed

lemma path_scopes:
  assumes "path s ts" "inj r"
  shows "path (map (lp_cut_scope_entry r) s)
    (map (map (lp_cut_scope_entry r)) ts)"
  using assms by (induct ts arbitrary: s)
    (auto intro: scoped)

text \<open>A nonempty source path may return to the same active core with
additional trailing barriers. Each iteration renames all allocated scopes
above the existing stack, so the next iteration is a genuine source execution.
The core must be invariant under scope renaming, not merely equal after
discarding a changing active cut scope.\<close>

theorem barrier_pump:
  assumes path: "path s (t#ts)"
    and closes: "last (t#ts) = s @ extra"
    and extra: "lp_cut_barriers extra"
    and core: "\<And>r. map (lp_cut_scope_entry r) s = s"
    and barriers: "lp_cut_barriers bs"
  shows "\<not> SN_on (R) {s @ bs}"
proof -
  have repeat: "\<exists>cs. lp_cut_barriers cs \<and>
    (s @ bs,s @ cs) \<in> (R)\<^sup>+"
    if "lp_cut_barriers bs" for bs
  proof -
    note suffix_barriers = that
    let ?S = "\<Union>e\<in>set bs. lp_cut_entry_scopes e"
    let ?N = "Suc (Lattices_Big.linorder_class.Max (insert (0::nat) ?S))"
    let ?r = "\<lambda>m. ?N + m"
    have bound: "m < ?N" if "m \<in> ?S" for m
    proof -
      have finite: "finite (insert (0::nat) ?S)" using lpc_no_scopes_finite[of bs] by simp
      have member: "m \<in> insert (0::nat) ?S" using that by simp
      show ?thesis using Max_ge[OF finite member] by simp
    qed
    have outside: "?r m \<notin> ?S" for m
      using bound[of "?r m"] by arith
    have fresh: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter> ?S = {}"
      if "u \<in> set (map (map (lp_cut_scope_entry ?r)) (t#ts))" for u
      using that outside by (auto simp: lp_cut_scope_entry_scopes)
    have injective: "inj ?r" by (simp add: inj_on_def)
    have renamed: "path s
      (map (lp_cut_scope_entry ?r) t # map (map (lp_cut_scope_entry ?r)) ts)"
      using path_scopes[OF path injective] core by simp
    obtain ds where ds: "lp_cut_barriers ds"
      "(s @ bs,last (map (map (lp_cut_scope_entry ?r)) (t#ts)) @ ds)
        \<in> (R)\<^sup>+"
      using path_extend_progress[OF renamed suffix_barriers] fresh by auto
    have map_barrier: "lp_cut_is_barrier (lp_cut_scope_entry ?r e) = lp_cut_is_barrier e" for e
      by (cases e) simp_all
    have mapped_extra: "lp_cut_barriers (map (lp_cut_scope_entry ?r) extra)"
      using extra
    proof (induct extra)
      case Nil then show ?case by simp
    next
      case (Cons e es)
      have head: "lp_cut_is_barrier (lp_cut_scope_entry ?r e)"
        using Cons.prems by (cases e) auto
      show ?case using Cons head by simp
    qed
    have nonempty: "t#ts \<noteq> []" by simp
    have last_eq: "last (map (map (lp_cut_scope_entry ?r)) (t#ts)) =
      s @ map (lp_cut_scope_entry ?r) extra"
      using last_map[OF nonempty, of "map (lp_cut_scope_entry ?r)"]
      by (simp only: closes map_append core)
    show ?thesis by (rule exI[of _ "map (lp_cut_scope_entry ?r) extra @ ds"])
      (use ds mapped_extra in \<open>simp only: last_eq append_assoc list_all_append\<close>)
  qed
  let ?X = "{s @ cs |cs. lp_cut_barriers cs}"
  have member: "s @ bs \<in> ?X" using barriers by auto
  have successor: "\<forall>u\<in>?X. \<exists>v\<in>?X. (u,v) \<in> (R)\<^sup>+"
    using repeat by blast
  show ?thesis using lower_set_imp_not_SN_on[OF member successor] SN_on_trancl by blast
qed

end


text \<open>The ordinary LP-with-cut source satisfies the same contract.
The Prolog instance adds builtin steps without changing stack or scope rules.\<close>
lemma lpc_source_barrier_execution:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
  shows "lp_barrier_execution (lp_cut_mgu_source P)"
proof
  fix s t and r :: "nat \<Rightarrow> nat"
  assume step: "(s,t)\<in>lp_cut_mgu_source P" and inj: "inj r"
  show "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>lp_cut_mgu_source P"
    by (rule lpc_mgu_scope_source[OF step inj program])
next
  fix s t and bs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assume step: "(s,t)\<in>lp_cut_mgu_source P" and bar: "lp_cut_barriers bs"
    and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter> (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  show "\<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and> (s @ bs,t @ cs)\<in>lp_cut_mgu_source P"
    by (rule lpc_no_source_extend[OF step bar fresh])
qed

end
