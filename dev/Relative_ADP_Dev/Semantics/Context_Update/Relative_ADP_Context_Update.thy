theory Relative_ADP_Context_Update
  imports Relative_ADP_RHS_Context_Dev.Relative_ADP_RHS_Context
begin

lemma poss_mctxt_mreplace_at_disj:
  assumes redex: "p \<in> poss_mctxt C"
    and target: "q \<in> poss_mctxt (mreplace_at C p E)"
  shows
    "(q \<in> poss_mctxt C \<and>
      (q <\<^sub>p p \<or> parallel_pos q p)) \<or>
     (\<exists>a. q = p @ a \<and> a \<in> poss_mctxt E)"
  using assms
proof (induct p arbitrary: C q)
  case Nil
  then show ?case by auto
next
  case (Cons i p)
  from Cons.prems(1) obtain f Cs where C: "C = MFun f Cs"
    and i: "i < length Cs" and p: "p \<in> poss_mctxt (Cs ! i)"
    by (cases C) auto
  have replace:
    "mreplace_at C (i # p) E =
      MFun f (Cs[i := mreplace_at (Cs ! i) p E])"
    unfolding C using i by (simp add: upd_conv_take_nth_drop)
  show ?case
  proof (cases q)
    case Nil
    then show ?thesis unfolding C
      by (auto simp: strict_prefix_def)
  next
    case (Cons j q')
    from Cons.prems(2)[unfolded replace Cons]
    have j: "j < length Cs"
      and q_target:
        "q' \<in> poss_mctxt
          ((Cs[i := mreplace_at (Cs ! i) p E]) ! j)"
      by auto
    show ?thesis
    proof (cases "j = i")
      case True
      have q_replaced: "q' \<in> poss_mctxt (mreplace_at (Cs ! i) p E)"
        using q_target i unfolding True by simp
      from Cons.hyps[OF p q_replaced]
      show ?thesis
      proof
        assume outside:
          "q' \<in> poss_mctxt (Cs ! i) \<and>
           (q' <\<^sub>p p \<or> parallel_pos q' p)"
        have q_source: "q \<in> poss_mctxt C"
          unfolding C Cons True using i outside by auto
        have relation:
          "q <\<^sub>p (i # p) \<or> parallel_pos q (i # p)"
          unfolding Cons True using outside by auto
        show ?thesis using q_source relation by blast
      next
        assume inside: "\<exists>a. q' = p @ a \<and> a \<in> poss_mctxt E"
        then obtain a where q': "q' = p @ a" and a: "a \<in> poss_mctxt E"
          by blast
        have "q = (i # p) @ a" unfolding Cons True q' by simp
        then show ?thesis using a by blast
      qed
    next
      case False
      have q_child: "q' \<in> poss_mctxt (Cs ! j)"
        using q_target i j False by simp
      have q_source: "q \<in> poss_mctxt C"
        unfolding C Cons using j q_child by auto
      have parallel: "parallel_pos q (i # p)"
        unfolding Cons using False by simp
      show ?thesis using q_source parallel by blast
    qed
  qed
qed

lemma poss_mctxt_mreplace_at_cases:
  assumes redex: "p \<in> poss_mctxt C"
    and target: "q \<in> poss_mctxt (mreplace_at C p E)"
  obtains (outside)
      "q \<in> poss_mctxt C"
      "q <\<^sub>p p \<or> parallel_pos q p"
    | (inside) a where
      "q = p @ a"
      "a \<in> poss_mctxt E"
  using poss_mctxt_mreplace_at_disj[OF redex target] that by blast

end
