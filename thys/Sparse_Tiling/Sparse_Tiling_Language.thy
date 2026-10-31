theory Sparse_Tiling_Language
  imports Sparse_Tiling_Paths
begin

definition sparse_accept where
  "sparse_accept T q w \<longleftrightarrow> set (sparse_path q w) \<subseteq> T"

definition sparse_states where "sparse_states T = butlast ` T"

lemma sparse_accept_start:
  assumes "w \<noteq> []" and "sparse_accept T q w"
  shows "q \<in> sparse_states T"
proof -
  obtain a v where w: "w = a # v" using assms(1) by (cases w) auto
  have tile: "q @ [a] \<in> T" using assms(2) by (simp add: sparse_accept_def w)
  have "butlast (q @ [a]) \<in> butlast ` T" by (rule imageI[OF tile])
  then show ?thesis by (simp add: sparse_states_def)
qed

lemma sparse_accept_context:
  assumes width: "length y = length q"
    and source: "sparse_accept T q (u @ l @ y @ v)"
    and reduct: "sparse_accept T (sparse_run q u) (r @ y)"
  shows "sparse_accept T q (u @ r @ y @ v)"
  using source reduct
  unfolding sparse_accept_def
  by (simp only: sparse_path_context[OF width] set_append) blast

definition sparse_tile_condition where
  "sparse_tile_condition n T R S \<longleftrightarrow>
    (\<forall>p l r y. length p = n \<and> p \<in> sparse_states T \<and> (l,r) \<in> R \<and>
      length y = n \<and> sparse_accept T p (l @ y) \<longrightarrow>
      sparse_accept T p (r @ y) \<and> (sparse_path p (l @ y), sparse_path p (r @ y)) \<in> S)"

lemma sparse_context_closed:
  assumes condition: "sparse_tile_condition (length q) T R S"
    and rule: "(l,r) \<in> R" and nonempty: "l \<noteq> []"
    and width: "length y = length q"
    and source: "sparse_accept T q (u @ l @ y @ v)"
  shows "sparse_accept T q (u @ r @ y @ v) \<and>
    (sparse_path q (u @ l @ y @ v), sparse_path q (u @ r @ y @ v)) \<in> sparse_word_step S"
proof -
  have local: "sparse_accept T (sparse_run q u) (l @ y)"
    using source unfolding sparse_accept_def
    by (simp only: sparse_path_context[OF width] set_append) blast
  have state: "sparse_run q u \<in> sparse_states T"
    by (rule sparse_accept_start[OF _ local]) (use nonempty in simp)
  have checked: "sparse_accept T (sparse_run q u) (r @ y) \<and>
    (sparse_path (sparse_run q u) (l @ y), sparse_path (sparse_run q u) (r @ y)) \<in> S"
    using condition rule width local state unfolding sparse_tile_condition_def by auto
  show ?thesis
    using sparse_accept_context[OF width source checked[THEN conjunct1]]
      sparse_path_rewrite_simulation[OF width checked[THEN conjunct2]] by blast
qed

lemma sparse_bordered_step:
  assumes condition: "sparse_tile_condition (length q) T R S"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and border: "length z = length q"
    and step: "(s,t) \<in> sparse_word_step R"
    and accepted: "sparse_accept T q (s @ z)"
  shows "sparse_accept T q (t @ z) \<and>
    (sparse_path q (s @ z), sparse_path q (t @ z)) \<in> sparse_word_step S"
proof -
  obtain u v l r where rule: "(l,r) \<in> R" and s: "s = u @ l @ v" and t: "t = u @ r @ v"
    using step unfolding sparse_word_step_def by blast
  let ?y = "take (length q) (v @ z)"
  let ?tail = "drop (length q) (v @ z)"
  have width: "length ?y = length q" using border by simp
  have source: "sparse_accept T q (u @ l @ ?y @ ?tail)"
    using accepted by (simp only: s append_assoc append_take_drop_id)
  have result: "sparse_accept T q (u @ r @ ?y @ ?tail) \<and>
    (sparse_path q (u @ l @ ?y @ ?tail), sparse_path q (u @ r @ ?y @ ?tail)) \<in> sparse_word_step S"
    by (rule sparse_context_closed[OF condition rule proper[OF rule] width source])
  from result show ?thesis by (simp only: s t append_assoc append_take_drop_id)
qed

lemma sparse_local_termination:
  assumes condition: "sparse_tile_condition (length q) T R S"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and border: "length z = length q"
    and target: "SN (sparse_word_step S)"
  shows "SN_on (sparse_word_step R) {w. sparse_accept T q (w @ z)}"
proof -
  have transfer: "\<And>x y. sparse_accept T q (x @ z) \<Longrightarrow> (x,y) \<in> sparse_word_step R \<Longrightarrow>
    sparse_accept T q (y @ z) \<and> (sparse_path q (x @ z), sparse_path q (y @ z)) \<in> sparse_word_step S"
  proof -
    fix x y
    assume accepted: "sparse_accept T q (x @ z)" and step: "(x,y) \<in> sparse_word_step R"
    show "sparse_accept T q (y @ z) \<and> (sparse_path q (x @ z), sparse_path q (y @ z)) \<in> sparse_word_step S"
      by (rule sparse_bordered_step[OF condition _ border step accepted]) (meson proper)
  qed
  show ?thesis
  proof (rule sparse_local_simulation_SN[where label="\<lambda>w. sparse_path q (w @ z)"])
    fix x y
    assume "x \<in> {w. sparse_accept T q (w @ z)}" and "(x,y) \<in> sparse_word_step R"
    then show "y \<in> {w. sparse_accept T q (w @ z)}" using transfer by blast
  next
    fix x y
    assume "x \<in> {w. sparse_accept T q (w @ z)}" and "(x,y) \<in> sparse_word_step R"
    then show "(sparse_path q (x @ z), sparse_path q (y @ z)) \<in> sparse_word_step S" using transfer by blast
  next
    show "SN_on (sparse_word_step S) ((\<lambda>w. sparse_path q (w @ z)) ` {w. sparse_accept T q (w @ z)})"
      using target unfolding SN_on_def by blast
  qed
qed

end
