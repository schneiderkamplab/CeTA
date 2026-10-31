theory Sparse_Tiling_Removal
  imports "Sparse_Tiling_Construction.Sparse_Tiling_Termination"
begin

text \<open>Sparse RFC rule removal (Algorithm 5.4 of Geser, Hofbauer and
Waldmann, FSCD 2019). Retain every rule with an accepted redex, while the
original system supplies the forward-closure coverage obligations.\<close>

definition sparse_live_rule_condition :: "nat \<Rightarrow> 'a list set \<Rightarrow> ('a list \<times> 'a list) set \<Rightarrow> ('a list \<times> 'a list) set \<Rightarrow> bool" where
  "sparse_live_rule_condition n T R K \<longleftrightarrow>
    (\<forall>p l r y. length p = n \<and> p \<in> sparse_states T \<and> (l,r) \<in> R \<and>
      length y = n \<and> sparse_accept T p (l @ y) \<longrightarrow> (l,r) \<in> K)"

lemma sparse_kept_step:
  assumes live: "sparse_live_rule_condition (length q) T R K"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and border: "length z = length q"
    and accepted: "sparse_accept T q (s @ z)"
    and step: "(s,t) \<in> sparse_word_step R"
  shows "(s,t) \<in> sparse_word_step K"
proof -
  obtain u v l r where rule: "(l,r) \<in> R" and s: "s = u @ l @ v" and t: "t = u @ r @ v"
    using step unfolding sparse_word_step_def by blast
  let ?y = "take (length q) (v @ z)"
  let ?tail = "drop (length q) (v @ z)"
  have width: "length ?y = length q" using border by simp
  have source: "sparse_accept T q (u @ l @ ?y @ ?tail)"
    using accepted by (simp only: s append_assoc append_take_drop_id)
  have local: "sparse_accept T (sparse_run q u) (l @ ?y)"
    using source unfolding sparse_accept_def
    by (simp only: sparse_path_context[OF width] set_append) blast
  have state: "sparse_run q u \<in> sparse_states T"
    by (rule sparse_accept_start[OF _ local]) (use proper[OF rule] in simp)
  have kept: "(l,r) \<in> K"
    using live rule width local state sparse_run_length[of q u]
    unfolding sparse_live_rule_condition_def by blast
  show ?thesis using sparse_word_stepI[OF kept, of u v] by (simp only: s t)
qed

lemma sparse_removal_sound:
  assumes normal: "sparse_tile_condition (length q) T R S"
    and suffix: "sparse_suffix_condition T R z"
    and initial: "\<And>l r. (l,r) \<in> R \<Longrightarrow> sparse_accept T q (r @ z)"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and border: "length z = length q"
    and live: "sparse_live_rule_condition (length q) T R K"
    and target: "SN (sparse_word_step K)"
  shows "SN (sparse_word_step R)"
proof -
  let ?L = "{w. sparse_accept T q (w @ z)}"
  have closed: "\<And>x y. x \<in> ?L \<Longrightarrow> (x,y) \<in> sparse_word_step R \<Longrightarrow> y \<in> ?L"
    using sparse_bordered_step[OF normal _ border] proper by blast
  have simulate: "\<And>x y. x \<in> ?L \<Longrightarrow> (x,y) \<in> sparse_word_step R \<Longrightarrow> (x,y) \<in> sparse_word_step K"
    using sparse_kept_step[OF live _ border] proper by blast
  have restricted: "SN_on (sparse_word_step K) ((\<lambda>w. w) ` ?L)"
    using target unfolding SN_on_def by blast
  have local: "SN_on (sparse_word_step R) ?L"
    by (rule sparse_local_simulation_SN[OF closed simulate restricted])
  have inclusion: "sparse_rfc R \<subseteq> ?L"
    using sparse_rfc_accepted[OF _ normal suffix _ border] initial proper by blast
  have "SN_on (sparse_word_step R) (sparse_rfc R)"
    using local inclusion unfolding SN_on_def by blast
  then show ?thesis by (rule sparse_rfc_termination) (meson proper)
qed

definition sparse_check_live_rules :: "nat \<Rightarrow> 'a list list \<Rightarrow> ('a list \<times> 'a list) list \<Rightarrow> ('a list \<times> 'a list) list \<Rightarrow> bool" where
  "sparse_check_live_rules n ts rs kept \<longleftrightarrow>
    list_all (\<lambda>p. list_all (\<lambda>(l,r). list_all (\<lambda>y.
      sparse_accept (set ts) p (l @ y) \<longrightarrow> (l,r) \<in> set kept)
      (sparse_contexts ts (sparse_run p l) n)) rs)
      (remdups (map butlast ts))"

lemma sparse_check_live_rules_condition:
  assumes checked: "sparse_check_live_rules n ts rs kept"
  shows "sparse_live_rule_condition n (set ts) (set rs) (set kept)"
  unfolding sparse_live_rule_condition_def
proof (intro allI impI)
  fix p l r y
  assume facts: "length p = n \<and> p \<in> sparse_states (set ts) \<and> (l,r) \<in> set rs \<and>
    length y = n \<and> sparse_accept (set ts) p (l @ y)"
  have state: "p \<in> set (remdups (map butlast ts))"
    using facts by (auto simp: sparse_states_def)
  have context_member: "y \<in> set (sparse_contexts ts (sparse_run p l) n)"
    using facts by (simp add: sparse_contexts_correct)
  show "(l,r) \<in> set kept"
    using checked facts state context_member unfolding sparse_check_live_rules_def list_all_iff
    by (fastforce split: prod.splits)
qed

definition sparse_check_removal where
  "sparse_check_removal q z ts rs ss kept \<longleftrightarrow>
    sparse_check_coverage q z ts rs ss \<and> set kept \<subseteq> set rs \<and>
    sparse_check_live_rules (length q) ts rs kept"

lemma sparse_check_removal_sound:
  assumes checked: "sparse_check_removal q z ts rs ss kept"
    and target: "SN (sparse_word_step (set kept))"
  shows "SN (sparse_word_step (set rs))"
proof (rule sparse_removal_sound[where q=q and z=z and T="set ts" and S="set ss"])
  show "sparse_tile_condition (length q) (set ts) (set rs) (set ss)"
    using checked sparse_check_tiles_condition
    unfolding sparse_check_removal_def sparse_check_coverage_def by blast
next
  show "sparse_suffix_condition (set ts) (set rs) z"
    using checked sparse_check_suffixes_condition
    unfolding sparse_check_removal_def sparse_check_coverage_def by blast
next
  fix l r
  assume "(l,r) \<in> set rs"
  then show "sparse_accept (set ts) q (r @ z)" using checked
    by (auto simp only: sparse_check_removal_def sparse_check_coverage_def list_all_iff split: prod.splits)
next
  fix l r
  assume "(l,r) \<in> set rs"
  then show "l \<noteq> []" using checked
    by (auto simp only: sparse_check_removal_def sparse_check_coverage_def sparse_check_tiles_def list_all_iff split: prod.splits)
next
  show "length z = length q" using checked
    unfolding sparse_check_removal_def sparse_check_coverage_def by blast
next
  show "sparse_live_rule_condition (length q) (set ts) (set rs) (set kept)"
    using checked sparse_check_live_rules_condition unfolding sparse_check_removal_def by blast
next
  show "SN (sparse_word_step (set kept))" by (rule target)
qed

lemma sparse_removal_empty_residual:
  "sparse_check_removal [0::nat] [4]
    [[1,2],[1,3],[2,2],[2,3],[0,1],[0,2],[3,4]]
    [([3,3],[2,3]),([2,1],[1,3])] [] []"
  by eval

lemma sparse_removal_false_empty_rejected:
  "\<not> sparse_check_removal [0::nat] [0] [[0,0]] [([0],[])]
    [([[0,0],[0,0]],[[0,0]])] []"
  by eval

lemma sparse_live_missing_rule_rejected:
  "\<not> sparse_check_live_rules 1 [[0::nat,0]] [([0],[])] []"
  by eval

lemma sparse_live_retained_rule:
  "sparse_check_live_rules 1 [[0::nat,0]] [([0],[])] [([0],[])]"
  by eval

export_code sparse_check_live_rules sparse_check_removal checking SML
end
