theory Relative_ADP_Root_Base_State
  imports Relative_ADP_Target_Decomposition_Dev.Relative_ADP_Target_Decomposition
begin

lemma relative_context_origin_state_root_base:
  assumes state: "relative_context_origin_state R B D s t C holes"
    and rule: "(l, r) \<in> B"
    and nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p_context: "p \<in> poss_mctxt C"
    and p_defined: "p \<in> adp_defined_positions D t"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
  defines "C' \<equiv> mreplace_at C p (rhs_origin_mctxt l r p C)"
    and "t' \<equiv> replace_at t p (r \<cdot> sigma)"
    and "holes' \<equiv> unfill_holes
      (mreplace_at C p (rhs_origin_mctxt l r p C))
      (replace_at t p (r \<cdot> sigma))"
  shows "relative_context_origin_state R B D s t' C' holes'"
proof -
  from state have length: "num_holes C = length holes"
    and source: "fill_holes C holes = t"
    unfolding relative_context_origin_state_def by blast+
  have p: "p \<in> poss t" by (rule fun_poss_imp_poss[OF p_fun])
  have prefix: "C' \<le> mctxt_of_term t'"
    unfolding C'_def t'_def
    by (rule concrete_target_context_prefix[
          OF nondup length source p_context redex])
  have new_length: "num_holes C' = length holes'"
    unfolding holes'_def C'_def t'_def
    using length_unfill_holes[OF prefix] unfolding C'_def t'_def by simp
  have target: "fill_holes C' holes' = replace_at t p (r \<cdot> sigma)"
    unfolding holes'_def C'_def t'_def
    using fill_unfill_holes[OF prefix] unfolding C'_def t'_def by simp
  have transfer:
    "base_context_pair_transfer l r p sigma D t
      (fill_holes C' holes') C C'"
  proof -
    have direct: "base_context_pair_transfer l r p sigma D t
      (replace_at t p (r \<cdot> sigma)) C
      (mreplace_at C p (rhs_origin_mctxt l r p C))"
      by (rule concrete_base_context_pair_transfer[
            OF nondup p p_context p_defined redex])
    show ?thesis using direct target unfolding C'_def by simp
  qed
  have result: "relative_context_origin_state R B D s
    (fill_holes C' holes') C' holes'"
    by (rule relative_context_origin_state_outer_base[
          OF state rule nondup p_fun redex target new_length transfer])
  show ?thesis using result target unfolding t'_def by simp
qed

end
