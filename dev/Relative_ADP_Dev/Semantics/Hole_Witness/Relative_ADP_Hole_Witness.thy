theory Relative_ADP_Hole_Witness
  imports Relative_ADP_Hole_Descendant_Dev.Relative_ADP_Hole_Descendant
begin

inductive concrete_hole_witness ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow>
    ('f, 'v) mctxt \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool"
  for l r p C where
  outside:
    "h \<in> hole_poss C \<Longrightarrow> h \<bottom> p \<Longrightarrow>
     concrete_hole_witness l r p C h h []"
| moved:
    "alpha \<in> var_poss r \<Longrightarrow>
     p @ rhs_predecessor l r alpha @ beta \<in> hole_poss C \<Longrightarrow>
     concrete_hole_witness l r p C
       (p @ alpha @ beta) (p @ rhs_predecessor l r alpha @ beta) []"
| split:
    "alpha \<in> var_poss r \<Longrightarrow> h \<in> hole_poss C \<Longrightarrow>
     p @ rhs_predecessor l r alpha = h @ beta \<Longrightarrow>
     concrete_hole_witness l r p C (p @ alpha) h beta"

lemma concrete_hole_witness_total:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and length: "num_holes C = length holes"
    and source: "fill_holes C holes = s"
    and p_context: "p \<in> poss_mctxt C"
    and redex: "s |_ p = l \<cdot> sigma"
    and q_hole:
      "q \<in> hole_poss
        (mreplace_at C p (rhs_origin_mctxt l r p C))"
  shows "\<exists>h beta. concrete_hole_witness l r p C q h beta"
proof -
  have C_prefix: "C \<le> mctxt_of_term s"
    using fill_holes_suffix[OF length] source by simp
  have p_all: "p \<in> all_poss_mctxt C"
    using p_context unfolding all_poss_mctxt_conv by blast
  have p: "p \<in> poss s"
  proof -
    have "p \<in> all_poss_mctxt (mctxt_of_term s)"
      by (rule subsetD[OF all_poss_mctxt_mono[OF C_prefix] p_all])
    then show ?thesis by simp
  qed
  from hole_pos_mreplace_at_disj[OF p_context q_hole]
  show ?thesis
  proof
    assume outside: "q \<in> hole_poss C \<and> q \<bottom> p"
    have "concrete_hole_witness l r p C q q []"
      by (rule concrete_hole_witness.outside) (use outside in blast)+
    then show ?thesis by blast
  next
    assume inside: "\<exists>a. q = p @ a \<and>
      a \<in> hole_poss (rhs_origin_mctxt l r p C)"
    then obtain a where q: "q = p @ a"
      and a_hole: "a \<in> hole_poss (rhs_origin_mctxt l r p C)"
      by blast
    from rhs_origin_mctxt_hole_root[OF nd C_prefix p redex a_hole]
    show ?thesis
    proof
      assume "\<exists>alpha beta.
        alpha \<in> var_poss r \<and> a = alpha @ beta \<and>
        p @ rhs_predecessor l r alpha @ beta \<in> hole_poss C"
      then obtain alpha beta where alpha: "alpha \<in> var_poss r"
        and a: "a = alpha @ beta"
        and old: "p @ rhs_predecessor l r alpha @ beta \<in> hole_poss C"
        by blast
      have "concrete_hole_witness l r p C q
        (p @ rhs_predecessor l r alpha @ beta) []"
        unfolding q a by (rule concrete_hole_witness.moved[OF alpha old])
      then show ?thesis by blast
    next
      assume "\<exists>alpha h beta.
        alpha \<in> var_poss r \<and> a = alpha \<and>
        h \<in> hole_poss C \<and>
        p @ rhs_predecessor l r alpha = h @ beta"
      then obtain alpha h beta where alpha: "alpha \<in> var_poss r"
        and a: "a = alpha" and h: "h \<in> hole_poss C"
        and source_pos: "p @ rhs_predecessor l r alpha = h @ beta"
        by blast
      have "concrete_hole_witness l r p C q h beta"
        unfolding q a
        by (rule concrete_hole_witness.split[OF alpha h source_pos])
      then show ?thesis by blast
    qed
  qed
qed

lemma concrete_hole_witness_old_hole:
  assumes "concrete_hole_witness l r p C q h beta"
  shows "h \<in> hole_poss C"
  using assms by cases auto

lemma concrete_hole_witness_target_hole_shape:
  assumes "concrete_hole_witness l r p C q h beta"
  shows "q = h \<or> p \<le>\<^sub>p q"
  using assms by cases auto

lemma concrete_hole_witness_cases_disj:
  assumes witness: "concrete_hole_witness l r p C q h beta"
  shows
    "(q = h \<and> beta = [] \<and> h \<in> hole_poss C \<and> h \<bottom> p) \<or>
     (\<exists>alpha tail.
       alpha \<in> var_poss r \<and>
       q = p @ alpha @ tail \<and>
       h = p @ rhs_predecessor l r alpha @ tail \<and>
       beta = [] \<and> h \<in> hole_poss C) \<or>
     (\<exists>alpha.
       alpha \<in> var_poss r \<and>
       q = p @ alpha \<and>
       h \<in> hole_poss C \<and>
       p @ rhs_predecessor l r alpha = h @ beta)"
  using witness by cases auto

end
