theory Relative_ADP_Prefix
  imports Relative_ADP_Base_Dev.Relative_ADP_Base
begin

lemma nonroot_step_extends_root_origin_trace:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and trace: "weak_pair_origin_trace R B D s t [] [] [] []"
    and step: "(t, u) \<in> nrrstep (R \<union> B)"
  shows "weak_pair_origin_trace R B D s u [] [] [] []"
proof -
  from step obtain C l r sigma where C: "C \<noteq> Hole"
    and rule: "(l, r) \<in> R \<union> B"
    and t: "t = C\<langle>l \<cdot> sigma\<rangle>" and u: "u = C\<langle>r \<cdot> sigma\<rangle>"
    by (elim nrrstepE) blast
  let ?p = "hole_pos C"
  have p_ne: "?p \<noteq> []" using C by (cases C) auto
  have p_poss: "?p \<in> poss t" unfolding t by simp
  from wf rule obtain f ls where l: "l = Fun f ls"
    using wf_trs_imp_lhs_Fun by blast
  have p_fun: "?p \<in> fun_poss t"
  proof (rule poss_is_Fun_fun_poss[OF p_poss])
    show "is_Fun (t |_ ?p)" unfolding t l by simp
  qed
  have redex: "t |_ ?p = l \<cdot> sigma" unfolding t by simp
  have outside: "[] <\<^sub>p ?p" unfolding less_pos_def' using p_ne by auto
  from rule show ?thesis
  proof
    assume main: "(l, r) \<in> R"
    have "weak_pair_origin_trace R B D s
        (replace_at t ?p (r \<cdot> sigma)) [] [] [] []"
      by (rule weak_pair_origin_trace.strict_prefix[
            OF trace main p_fun redex disjI1[OF outside] disjI1[OF outside]])
    then show ?thesis unfolding t u by simp
  next
    assume base: "(l, r) \<in> B"
    have targets: "origin_root_targets 2 D r {}" by simp
    have nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
      using nd base unfolding nonduplicating_trs_def by blast
    have edge: "origin_edge l r ?p sigma {} (covering_vrf l r) [] []"
      by (rule origin_edge.preserved[OF disjI1[OF outside]])
    have "weak_pair_origin_trace R B D s
        (replace_at t ?p (r \<cdot> sigma)) [] [] [] []"
      by (rule weak_pair_origin_trace.step[
            OF trace base targets nondup p_fun redex edge edge])
    then show ?thesis unfolding t u by simp
  qed
qed

lemma nonroot_steps_root_origin_trace:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and steps: "(s, t) \<in> (nrrstep (R \<union> B))\<^sup>*"
  shows "weak_pair_origin_trace R B D s t [] [] [] []"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  show ?case by (rule weak_pair_origin_trace.refl)
next
  case (step t u)
  show ?case by (rule nonroot_step_extends_root_origin_trace[
        OF wf nd step.hyps(3) step.hyps(2)])
qed

lemma Tinf_nrrsteps_local:
  assumes minimal: "s \<in> Tinf (relstep R B)"
    and steps: "(s, t) \<in> (nrrstep (R \<union> B))\<^sup>*"
    and target: "\<not> SN_on (relstep R B) {t}"
  shows "t \<in> Tinf (relstep R B)"
  using steps minimal
proof (induct rule: converse_rtrancl_induct)
  case base
  then show ?case .
next
  case (step s u)
  have nr_subset: "nrrstep (R \<union> B) \<subseteq> rstep R \<union> rstep B"
  proof
    fix xy
    assume "xy \<in> nrrstep (R \<union> B)"
    then have "xy \<in> rstep (R \<union> B)"
      unfolding rstep_iff_rrstep_or_nrrstep by auto
    then show "xy \<in> rstep R \<union> rstep B"
      unfolding rstep_union .
  qed
  have u_t: "(u, t) \<in> (rstep R \<union> rstep B)\<^sup>*"
    by (rule subsetD[OF rtrancl_mono[OF nr_subset] step.hyps(2)])
  have u_nt: "\<not> SN_on (relstep R B) {u}"
  proof
    assume u_sn: "SN_on (relstep R B) {u}"
    from steps_preserve_SN_on_relto[OF u_t u_sn]
    show False using target by simp
  qed
  have u_minimal: "u \<in> Tinf (relstep R B)"
    by (rule Tinf_nrrstep[OF step.prems step.hyps(1) u_nt])
  show ?case by (rule step.hyps(3)[OF u_minimal])
qed

end
