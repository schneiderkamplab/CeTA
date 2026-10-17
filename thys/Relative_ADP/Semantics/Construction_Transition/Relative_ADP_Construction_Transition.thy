theory Relative_ADP_Construction_Transition
  imports Relative_ADP_Carrier_Step_Dev.Relative_ADP_Carrier_Step
begin

lemma relative_carrier_origin_state_inner_update:
  fixes u :: "('f, 'v) term"
  assumes state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
    and i: "i < length holes"
    and beta: "beta \<in> poss (holes ! i)"
    and origin': "relative_context_origin_state R B D s t' C
      (holes[i := replace_at (holes ! i) beta u])"
  shows "relative_carrier_origin_state R B D s t' C
    (holes[i := replace_at (holes ! i) beta u]) owners locations
    (carriers[owners ! i := replace_at (carriers ! (owners ! i))
      (locations ! i @ beta) u])"
proof -
  from state have cover: "carrier_cover holes owners locations carriers"
    unfolding relative_carrier_origin_state_def by blast
  have cover': "carrier_cover
      (holes[i := replace_at (holes ! i) beta u]) owners locations
      (carriers[owners ! i := replace_at (carriers ! (owners ! i))
        (locations ! i @ beta) u])"
    by (rule carrier_cover_inner_update[OF cover i beta])
  show ?thesis
    unfolding relative_carrier_origin_state_def using origin' cover' by blast
qed

lemma relative_carrier_origin_state_inner_strict:
  assumes state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
    and i: "i < length holes"
    and beta: "beta \<in> poss (holes ! i)"
    and rule: "(l, r) \<in> R"
    and p: "p = hole_poss' C ! i @ beta"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and target: "fill_holes C
      (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)]) =
      replace_at t p (r \<cdot> sigma)"
  shows "relative_carrier_origin_state R B D s
    (fill_holes C
      (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])) C
    (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])
    owners locations
    (carriers[owners ! i := replace_at (carriers ! (owners ! i))
      (locations ! i @ beta) (r \<cdot> sigma)])"
proof -
  from state have origin: "relative_context_origin_state R B D s t C holes"
    unfolding relative_carrier_origin_state_def by blast
  have origin': "relative_context_origin_state R B D s
      (fill_holes C
        (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])) C
      (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])"
    by (rule relative_context_origin_state_inner_strict[
          OF origin i rule p p_fun redex target])
  show ?thesis
    by (rule relative_carrier_origin_state_inner_update[
          OF state i beta origin'])
qed

lemma relative_carrier_origin_state_inner_base:
  assumes state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
    and i: "i < length holes"
    and beta: "beta \<in> poss (holes ! i)"
    and rule: "(l, r) \<in> B"
    and targets: "origin_root_targets 2 D r A"
    and nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p = hole_poss' C ! i @ beta"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and target: "fill_holes C
      (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)]) =
      replace_at t p (r \<cdot> sigma)"
  shows "relative_carrier_origin_state R B D s
    (fill_holes C
      (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])) C
    (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])
    owners locations
    (carriers[owners ! i := replace_at (carriers ! (owners ! i))
      (locations ! i @ beta) (r \<cdot> sigma)])"
proof -
  from state have origin: "relative_context_origin_state R B D s t C holes"
    unfolding relative_carrier_origin_state_def by blast
  have origin': "relative_context_origin_state R B D s
      (fill_holes C
        (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])) C
      (holes[i := replace_at (holes ! i) beta (r \<cdot> sigma)])"
    by (rule relative_context_origin_state_inner_base[
          OF origin i rule targets nondup p p_fun redex target])
  show ?thesis
    by (rule relative_carrier_origin_state_inner_update[
          OF state i beta origin'])
qed

end
