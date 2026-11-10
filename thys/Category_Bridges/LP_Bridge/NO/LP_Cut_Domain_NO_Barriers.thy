theory LP_Cut_Domain_NO_Barriers
  imports LP_Cut_Domain_NO_Steps
begin

context cut_runtime_domain
begin


lemma no_admin_extend:
  assumes step: "lp_cut_admin s=Some t" and barriers: "lp_cut_barriers bs"
  shows "\<exists>suffix. lp_cut_barriers suffix \<and> set suffix \<subseteq> set bs \<and>
    lp_cut_admin (s @ bs) = Some (t @ suffix)"
  using step barriers
proof (induct s rule: lp_cut_admin.induct)
  case (5 g gs es)
  have subset: "set (lp_cut_prune m bs) \<subseteq> set bs" for m
    by (induct bs) (auto split: lp_cut_entry.splits if_splits)
  show ?case using 5 subset lp_cut_barriers_prune[of bs]
    by (cases g) (auto simp: lp_cut_prune_append lp_cut_prune_absent split: if_splits)
qed auto

lemma no_source_extend:
  assumes step: "(s,t)\<in>mgu_source P"
    and barriers: "lp_cut_barriers bs"
    and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "\<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and>
    (s @ bs,t @ cs) \<in> mgu_source P"
  using step fresh
proof (cases rule: mgu_source.cases)
  case admin
  show ?thesis using no_admin_extend[OF admin barriers]
    by (blast intro: mgu_source.admin)
qed (use barriers in \<open>force simp: lp_cut_fresh_def append_assoc
  intro: mgu_source.case_call mgu_source.resolve mgu_source.backtrack
    mgu_source.unify mgu_source.unify_fail mgu_source.meta
    \<close>)+

fun no_path where
  "no_path P s [] = True"
| "no_path P s (t#ts) = ((s,t) \<in> mgu_source P \<and> no_path P t ts)"

lemma no_path_extend:
  assumes path: "no_path P s ts" and barriers: "lp_cut_barriers bs"
    and fresh: "\<And>t. t \<in> set ts \<Longrightarrow>
      (\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "\<exists>cs. lp_cut_barriers cs \<and> set cs \<subseteq> set bs \<and>
    (s @ bs, last (s#ts) @ cs) \<in> (mgu_source P)\<^sup>*"
  using path barriers fresh
proof (induct ts arbitrary: s bs)
  case Nil then show ?case by auto
next
  case (Cons t ts)
  have step: "(s,t) \<in> mgu_source P" using Cons.prems(1) by simp
  have fresh_t: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}" using Cons.prems(3)[of t] by simp
  obtain ds where ds: "lp_cut_barriers ds" "set ds \<subseteq> set bs"
    "(s @ bs,t @ ds) \<in> mgu_source P"
    using no_source_extend[OF step Cons.prems(2) fresh_t] by blast
  have fresh: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set ds. lp_cut_entry_scopes e) = {}" if "u \<in> set ts" for u
    using Cons.prems(3)[of u] ds(2) that by auto
  obtain cs where cs: "lp_cut_barriers cs" "set cs \<subseteq> set ds"
    "(t @ ds,last (t#ts) @ cs) \<in> (mgu_source P)\<^sup>*"
    using Cons.hyps[OF _ ds(1) fresh] Cons.prems(1) by auto
  have joined: "(s @ bs,last (t#ts) @ cs) \<in> (mgu_source P)\<^sup>*"
    using ds(3) cs(3) by (meson rtrancl_trans r_into_rtrancl)
  have subset: "set cs \<subseteq> set bs" using ds(2) cs(2) by blast
  show ?case by (rule exI[of _ cs]) (use cs(1) subset joined in simp)
qed

lemma no_path_extend_progress:
  assumes path: "no_path P s (t#ts)" and barriers: "lp_cut_barriers bs"
    and fresh: "\<And>u. u \<in> set (t#ts) \<Longrightarrow>
      (\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
      (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
  shows "\<exists>cs. lp_cut_barriers cs \<and>
    (s @ bs,last (t#ts) @ cs) \<in> (mgu_source P)\<^sup>+"
proof -
  have step: "(s,t) \<in> mgu_source P" using path by simp
  have fresh_t: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}" using fresh[of t] by simp
  obtain ds where ds: "lp_cut_barriers ds" "set ds \<subseteq> set bs"
    "(s @ bs,t @ ds) \<in> mgu_source P"
    using no_source_extend[OF step barriers fresh_t] by blast
  have fresh_tail: "(\<Union>e\<in>set u. lp_cut_entry_scopes e) \<inter>
    (\<Union>e\<in>set ds. lp_cut_entry_scopes e) = {}" if "u \<in> set ts" for u
    using fresh[of u] ds(2) that by auto
  have tail: "no_path P t ts" using path by simp
  obtain cs where "lp_cut_barriers cs"
    "(t @ ds,last (t#ts) @ cs) \<in> (mgu_source P)\<^sup>*"
    using no_path_extend[OF tail ds(1) fresh_tail] by blast
  then show ?thesis using ds(3) by (meson rtrancl_into_trancl2)
qed

end
end
