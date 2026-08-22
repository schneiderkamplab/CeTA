theory Relative_ADP_Context_State
  imports Relative_ADP_Carrier_Dev.Relative_ADP_Carrier
begin

lemma context_pos_above_or_parallel_hole:
  assumes ctxt_pos: "p \<in> poss_mctxt C" and hole: "q \<in> hole_poss C"
  shows "p <\<^sub>p q \<or> parallel_pos p q"
  using assms
proof (induct C arbitrary: p q)
  case (MFun f Cs)
  then show ?case
  proof (cases p)
    case Nil
    with MFun show ?thesis
      by (auto simp: strict_prefix_def)
  next
    case (Cons i p')
    have q_nonempty: "q \<noteq> []"
      using MFun(3) by (auto simp: hole_poss_simp)
    then obtain j q' where q: "q = j # q'"
      by (cases q) auto
    have j: "j < length Cs" and q': "q' \<in> hole_poss (Cs ! j)"
      using MFun(3) unfolding q by (auto simp: hole_poss_simp)
    from MFun(2)[unfolded Cons] have i: "i < length Cs"
      and p': "p' \<in> poss_mctxt (Cs ! i)" by auto
    show ?thesis
    proof (cases "i = j")
      case True
      have q_i: "q' \<in> hole_poss (Cs ! i)" using q' True by simp
      have "p' <\<^sub>p q' \<or> parallel_pos p' q'"
        by (rule MFun(1)[OF nth_mem[OF i] p' q_i])
      then show ?thesis unfolding Cons q True by auto
    next
      case False
      then show ?thesis unfolding Cons q by simp
    qed
  qed
qed auto

lemma parallel_pos_append_right:
  assumes "parallel_pos p q"
  shows "parallel_pos p (q @ r)"
  using assms
  by (induct p q rule: list_induct2'') auto

lemma context_pos_above_or_parallel_below_hole:
  assumes ctxt_pos: "p \<in> poss_mctxt C"
    and hole: "q \<in> hole_poss C"
  shows "p <\<^sub>p (q @ r) \<or> parallel_pos p (q @ r)"
proof -
  from context_pos_above_or_parallel_hole[OF ctxt_pos hole]
  show ?thesis
  proof
    assume "p <\<^sub>p q"
    then show ?thesis
      unfolding strict_prefix_def by auto
  next
    assume "parallel_pos p q"
    then show ?thesis using parallel_pos_append_right by blast
  qed
qed

definition relative_context_origin_state ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) mctxt \<Rightarrow> ('f, 'v) term list \<Rightarrow> bool" where
  "relative_context_origin_state R B D s t C holes \<longleftrightarrow>
    num_holes C = length holes \<and>
    fill_holes C holes = t \<and>
    (\<forall>p \<in> poss_mctxt C. \<forall>q \<in> poss_mctxt C.
      p \<in> adp_defined_positions D t \<longrightarrow>
      q \<in> adp_defined_positions D t \<longrightarrow>
      weak_pair_origin_trace R B D s t [] [] p q)"

lemma initial_relative_context_origin_state:
  assumes "is_Fun s"
    and defined: "[] \<in> adp_defined_positions D s"
  shows "relative_context_origin_state R B D s s
    (root_hole_mctxt s) (root_hole_terms s)"
  unfolding relative_context_origin_state_def
  using root_hole_num_holes root_hole_fill
    root_hole_context_positions[OF assms(1)] defined
  by (auto intro: weak_pair_origin_trace.refl)

end
