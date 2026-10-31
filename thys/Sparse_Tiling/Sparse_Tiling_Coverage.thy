theory Sparse_Tiling_Coverage
  imports Sparse_Tiling_Check
begin

inductive_set sparse_rfc :: "('a list \<times> 'a list) set \<Rightarrow> 'a list set" for R where
  rhs: "(l,r) \<in> R \<Longrightarrow> r \<in> sparse_rfc R"
| rewrite: "w \<in> sparse_rfc R \<Longrightarrow> (w,v) \<in> sparse_word_step R \<Longrightarrow> v \<in> sparse_rfc R"
| overlap: "u @ a \<in> sparse_rfc R \<Longrightarrow> (a @ b,r) \<in> R \<Longrightarrow>
    a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow> u @ r \<in> sparse_rfc R"

definition sparse_suffix_condition where
  "sparse_suffix_condition T R z \<longleftrightarrow>
    (\<forall>p a b r. p \<in> sparse_states T \<and> (a @ b,r) \<in> R \<and> a \<noteq> [] \<and> b \<noteq> [] \<and>
      sparse_accept T p (a @ z) \<longrightarrow> sparse_accept T p (r @ z))"

lemma sparse_suffix_closed:
  assumes condition: "sparse_suffix_condition T R z"
    and rule: "(a @ b,r) \<in> R" and a: "a \<noteq> []" and b: "b \<noteq> []"
    and accepted: "sparse_accept T q ((u @ a) @ z)"
  shows "sparse_accept T q ((u @ r) @ z)"
proof -
  have local: "sparse_accept T (sparse_run q u) (a @ z)"
    and prefix: "sparse_accept T q u" using accepted by (simp_all add: append_assoc)
  have state: "sparse_run q u \<in> sparse_states T"
    by (rule sparse_accept_start[OF _ local]) (use a in simp)
  have "sparse_accept T (sparse_run q u) (r @ z)"
    using condition state rule a b local unfolding sparse_suffix_condition_def by blast
  then show ?thesis using prefix by (simp add: append_assoc)
qed

lemma sparse_rfc_accepted:
  assumes initial: "\<And>l r. (l,r) \<in> R \<Longrightarrow> sparse_accept T q (r @ z)"
    and normal: "sparse_tile_condition (length q) T R S"
    and suffix: "sparse_suffix_condition T R z"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and border: "length z = length q"
    and member: "w \<in> sparse_rfc R"
  shows "sparse_accept T q (w @ z)"
  using member
proof induction
  case (rhs l r)
  then show ?case by (rule initial)
next
  case (rewrite w v)
  have result: "sparse_accept T q (v @ z) \<and>
    (sparse_path q (w @ z), sparse_path q (v @ z)) \<in> sparse_word_step S"
    by (rule sparse_bordered_step[OF normal _ border rewrite.hyps(2) rewrite.IH]) (meson proper)
  then show ?case by blast
next
  case (overlap u a b r)
  show ?case by (rule sparse_suffix_closed[OF suffix overlap.hyps(2-4) overlap.IH])
qed

lemma sparse_rfc_local_termination:
  assumes normal: "sparse_tile_condition (length q) T R S"
    and suffix: "sparse_suffix_condition T R z"
    and initial: "\<And>l r. (l,r) \<in> R \<Longrightarrow> sparse_accept T q (r @ z)"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and border: "length z = length q"
    and target: "SN (sparse_word_step S)"
  shows "SN_on (sparse_word_step R) (sparse_rfc R)"
proof -
  have local: "SN_on (sparse_word_step R) {w. sparse_accept T q (w @ z)}"
    by (rule sparse_local_termination[OF normal _ border target]) (meson proper)
  have inclusion: "sparse_rfc R \<subseteq> {w. sparse_accept T q (w @ z)}"
    proof
    fix w
    assume member: "w \<in> sparse_rfc R"
    have "sparse_accept T q (w @ z)"
      by (rule sparse_rfc_accepted[OF _ normal suffix _ border member]) (meson initial proper)+
    then show "w \<in> {w. sparse_accept T q (w @ z)}" by simp
  qed
  show ?thesis using local inclusion unfolding SN_on_def by blast
qed

definition sparse_check_suffixes where
  "sparse_check_suffixes ts rs z \<longleftrightarrow>
    list_all (\<lambda>p. list_all (\<lambda>(l,r).
      list_all (\<lambda>i. sparse_accept (set ts) p (take i l @ z) \<longrightarrow>
        sparse_accept (set ts) p (r @ z)) [1..<length l]) rs)
      (remdups (map butlast ts))"

lemma sparse_check_suffixes_condition:
  assumes checked: "sparse_check_suffixes ts rs z"
  shows "sparse_suffix_condition (set ts) (set rs) z"
  unfolding sparse_suffix_condition_def
proof (intro allI impI)
  fix p a b r
  assume facts: "p \<in> sparse_states (set ts) \<and> (a @ b,r) \<in> set rs \<and>
    a \<noteq> [] \<and> b \<noteq> [] \<and> sparse_accept (set ts) p (a @ z)"
  have state: "p \<in> set (remdups (map butlast ts))"
    using facts by (auto simp: sparse_states_def)
  have rule: "(a @ b,r) \<in> set rs" using facts by blast
  have positive: "0 < length a" "0 < length b" using facts by auto
  have index: "length a \<in> set [1..<length (a @ b)]"
    using positive by (simp only: set_upt atLeastLessThan_iff length_append; arith)
  have per_state: "\<forall>lr\<in>set rs. case lr of (l,r) \<Rightarrow>
    (\<forall>i\<in>set [1..<length l]. sparse_accept (set ts) p (take i l @ z) \<longrightarrow>
      sparse_accept (set ts) p (r @ z))"
    using checked state unfolding sparse_check_suffixes_def list_all_iff by blast
  have per_rule: "\<forall>i\<in>set [1..<length (a @ b)].
    sparse_accept (set ts) p (take i (a @ b) @ z) \<longrightarrow> sparse_accept (set ts) p (r @ z)"
    using bspec[OF per_state rule] by (simp only: case_prod_conv)
  have selected: "sparse_accept (set ts) p (take (length a) (a @ b) @ z) \<longrightarrow>
    sparse_accept (set ts) p (r @ z)"
    by (rule bspec[OF per_rule index])
  show "sparse_accept (set ts) p (r @ z)" using selected facts by simp
qed

definition sparse_check_coverage where
  "sparse_check_coverage q z ts rs ss \<longleftrightarrow>
    length z = length q \<and> sparse_check_tiles (length q) ts rs ss \<and>
    sparse_check_suffixes ts rs z \<and>
    list_all (\<lambda>(l,r). sparse_accept (set ts) q (r @ z)) rs"

lemma sparse_check_coverage_sound:
  assumes checked: "sparse_check_coverage q z ts rs ss"
    and target: "SN (sparse_word_step (set ss))"
  shows "SN_on (sparse_word_step (set rs)) (sparse_rfc (set rs))"
proof (rule sparse_rfc_local_termination[where q=q and z=z and T="set ts" and S="set ss"])
  show "sparse_tile_condition (length q) (set ts) (set rs) (set ss)"
    using checked sparse_check_tiles_condition unfolding sparse_check_coverage_def by blast
next
  show "sparse_suffix_condition (set ts) (set rs) z"
    using checked sparse_check_suffixes_condition unfolding sparse_check_coverage_def by blast
next
  fix l r
  assume "(l,r) \<in> set rs"
  then show "sparse_accept (set ts) q (r @ z)" using checked
    by (auto simp only: sparse_check_coverage_def list_all_iff split: prod.splits)
next
  fix l r
  assume "(l,r) \<in> set rs"
  then show "l \<noteq> []" using checked
    by (auto simp only: sparse_check_coverage_def sparse_check_tiles_def list_all_iff split: prod.splits)
next
  show "length z = length q" using checked unfolding sparse_check_coverage_def by blast
next
  show "SN (sparse_word_step (set ss))" by (rule target)
qed

lemma sparse_coverage_example:
  "sparse_check_coverage [0::nat] [4]
    [[1,2],[1,3],[2,2],[2,3],[0,1],[0,2],[3,4]]
    [([3,3],[2,3]),([2,1],[1,3])] []"
  by eval

lemma sparse_coverage_missing_suffix_tile:
  "\<not> sparse_check_coverage [0::nat] [4]
    [[1,2],[1,3],[2,3],[0,1],[0,2],[3,4]]
    [([3,3],[2,3]),([2,1],[1,3])] []"
  by eval

lemma sparse_coverage_missing_initial_tile:
  "\<not> sparse_check_coverage [0::nat] [4]
    [[1,2],[1,3],[2,2],[2,3],[0,2],[3,4]]
    [([3,3],[2,3]),([2,1],[1,3])] []"
  by eval

export_code sparse_check_coverage checking SML

end
