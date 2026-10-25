theory LP_Cut_NO_Pumping
  imports LP_Cut_NO_Barriers
begin

lemma lpc_no_path_scopes:
  assumes "lpc_no_path P s ts" "inj r" "lp_cut_source_program P"
  shows "lpc_no_path P (map (lp_cut_scope_entry r) s)
    (map (map (lp_cut_scope_entry r)) ts)"
  using assms by (induct ts arbitrary: s)
    (auto intro: lpc_mgu_scope_source)

lemma lpc_no_scopes_finite:
  "finite (\<Union>e\<in>set bs. lp_cut_entry_scopes e)"
proof -
  have goals: "finite (lp_cut_goal_scopes g)" for g :: "'a lp_cut_goal"
    by (cases g) simp_all
  have entries: "finite (lp_cut_entry_scopes e)" for e :: "'a lp_cut_entry"
    by (cases e) (auto intro: goals)
  show ?thesis by (auto intro: entries)
qed

text \<open>A nonempty source path may return to the same active core with
additional trailing barriers. Each iteration renames all allocated scopes
above the existing stack, so the next iteration is a genuine source execution.
The core must be invariant under scope renaming, not merely equal after
discarding a changing active cut scope.\<close>

theorem lpc_no_barrier_pump:
  assumes program: "lp_cut_source_program P"
    and path: "lpc_no_path P s (t#ts)"
    and closes: "last (t#ts) = s @ extra"
    and extra: "lp_cut_barriers extra"
    and core: "\<And>r. map (lp_cut_scope_entry r) s = s"
    and barriers: "lp_cut_barriers bs"
  shows "\<not> SN_on (lp_cut_mgu_source P) {s @ bs}"
proof -
  have repeat: "\<exists>cs. lp_cut_barriers cs \<and>
    (s @ bs,s @ cs) \<in> (lp_cut_mgu_source P)\<^sup>+"
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
    have renamed: "lpc_no_path P s
      (map (lp_cut_scope_entry ?r) t # map (map (lp_cut_scope_entry ?r)) ts)"
      using lpc_no_path_scopes[OF path injective program] core by simp
    obtain ds where ds: "lp_cut_barriers ds"
      "(s @ bs,last (map (map (lp_cut_scope_entry ?r)) (t#ts)) @ ds)
        \<in> (lp_cut_mgu_source P)\<^sup>+"
      using lpc_no_path_extend_progress[OF renamed suffix_barriers] fresh by auto
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
  have successor: "\<forall>u\<in>?X. \<exists>v\<in>?X. (u,v) \<in> (lp_cut_mgu_source P)\<^sup>+"
    using repeat by blast
  show ?thesis using lower_set_imp_not_SN_on[OF member successor] SN_on_trancl by blast
qed

end
