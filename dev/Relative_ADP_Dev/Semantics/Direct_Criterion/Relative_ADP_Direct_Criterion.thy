theory Relative_ADP_Direct_Criterion
  imports Relative_ADP_Carrier_Run_Dev.Relative_ADP_Carrier_Run
begin

lemma adp_step_case_context:
  assumes q: "q \<in> poss sh"
    and local: "sh |_ q = s"
    and step: "adp_step_case P at_sharp s t"
  shows "adp_step_case P at_sharp sh (replace_at sh q t)"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  have p_poss: "p \<in> poss s"
    by (rule fun_poss_imp_poss[OF adp_stepI(4)])
  have qp_fun: "q @ p \<in> fun_poss sh"
  proof (rule poss_is_Fun_fun_poss)
    show "q @ p \<in> poss sh"
      using q p_poss local by (simp only: poss_append_poss)
    from fun_poss_fun_conv[OF adp_stepI(4)] obtain f ts where
      at: "s |_ p = Fun f ts" by blast
    show "is_Fun (sh |_ (q @ p))"
      using subt_at_append[OF q, of p] local at by simp
  qed
  have sharp:
      "at_sharp = (q @ p \<in> sharp_positions sh)"
    using sharp_positions_below_iff[OF q, of p] local adp_stepI(5)
    by simp
  have redex:
      "erase_adp_term (sh |_ (q @ p)) = erase_adp_term l \<cdot> sigma"
    using subt_at_append[OF q, of p] local adp_stepI(6) by simp
  have annotations: "A =
      (if at_sharp then sharp_positions r else {}) \<union>
      transported_annotations phi l (sh |_ (q @ p))"
    using subt_at_append[OF q, of p] local adp_stepI(7) by simp
  have nested:
      "replace_at sh q t =
        replace_at sh (q @ p)
          (annotate_term A (erase_adp_term r \<cdot> sigma))"
  proof -
    have target: "t = replace_at s p
        (annotate_term A (erase_adp_term r \<cdot> sigma))"
      by (rule adp_stepI(8))
    have p_local: "p \<in> poss (sh |_ q)" using local p_poss by simp
    show ?thesis
      unfolding target local[symmetric]
      by (rule carrier_replace_at_append[OF q p_local, symmetric])
  qed
  show ?thesis
    by (rule adp_step_case.adp_stepI[
          where l = l and r = r and phi = phi and p = "q @ p"
            and sigma = sigma and A = A,
          OF adp_stepI(1-3) qp_fun sharp redex annotations nested])
qed

lemma adp_step_context:
  assumes q: "q \<in> poss sh"
    and local: "sh |_ q = s"
    and step: "(s, t) \<in> adp_step P"
  shows "(sh, replace_at sh q t) \<in> adp_step P"
  using step
  unfolding adp_step_def adp_step_case_rel_def
  using adp_step_case_context[OF q local] by blast

lemma adp_steps_context:
  assumes q: "q \<in> poss sh"
    and local: "sh |_ q = s"
    and steps: "(s, t) \<in> (adp_step P)\<^sup>*"
  shows "(sh, replace_at sh q t) \<in> (adp_step P)\<^sup>*"
  using steps q local
proof (induct arbitrary: sh rule: rtrancl_induct)
  case base
  have target: "replace_at sh q s = sh"
    unfolding base.prems(2)[symmetric]
    by (simp add: ctxt_supt_id[OF base.prems(1)])
  show ?case unfolding target by simp
next
  case (step t u)
  let ?th = "replace_at sh q t"
  have prefix: "(sh, ?th) \<in> (adp_step P)\<^sup>*"
    by (rule step.hyps(3)[OF step.prems])
  have q_after: "q \<in> poss ?th"
    by (rule replace_at_below_poss[OF step.prems(1)]) simp
  have at_q: "?th |_ q = t"
    by (rule replace_at_subt_at[OF step.prems(1)])
  have last: "(?th, replace_at ?th q u) \<in> adp_step P"
    by (rule adp_step_context[OF q_after at_q step.hyps(2)])
  have target: "replace_at ?th q u = replace_at sh q u"
  proof -
    have ctxt: "ctxt_of_pos_term q ?th = ctxt_of_pos_term q sh"
      by (rule ctxt_of_pos_term_replace_at_below[
            OF step.prems(1), where p' = q]) simp
    show ?thesis using ctxt by simp
  qed
  have combined: "(sh, replace_at ?th q u) \<in> (adp_step P)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF prefix last])
  show ?case using combined target by simp
qed

lemma adp_productive_block_context:
  assumes q: "q \<in> poss sh"
    and local: "sh |_ q = s"
    and block: "(s, t) \<in> adp_productive_block_rel P Q"
  shows "(sh, replace_at sh q t) \<in> adp_productive_block_rel P Q"
proof -
  from block obtain u where weak:
      "(s, u) \<in> (adp_step (P \<union> Q))\<^sup>*"
    and strict: "(u, t) \<in> adp_step_case_rel P True"
    unfolding adp_productive_block_rel_def by blast
  let ?uh = "replace_at sh q u"
  have weak_context: "(sh, ?uh) \<in> (adp_step (P \<union> Q))\<^sup>*"
    by (rule adp_steps_context[OF q local weak])
  have q_after: "q \<in> poss ?uh"
    by (rule replace_at_below_poss[OF q]) simp
  have at_q: "?uh |_ q = u" by (rule replace_at_subt_at[OF q])
  have strict_context:
      "(?uh, replace_at ?uh q t) \<in> adp_step_case_rel P True"
    using strict adp_step_case_context[OF q_after at_q]
    unfolding adp_step_case_rel_def by blast
  have target: "replace_at ?uh q t = replace_at sh q t"
  proof -
    have ctxt: "ctxt_of_pos_term q ?uh = ctxt_of_pos_term q sh"
      by (rule ctxt_of_pos_term_replace_at_below[OF q, where p' = q]) simp
    show ?thesis using ctxt by simp
  qed
  have lifted: "(sh, replace_at ?uh q t) \<in>
      adp_productive_block_rel P Q"
    unfolding adp_productive_block_rel_def
    by (rule relcompI[OF weak_context strict_context])
  show ?thesis using lifted unfolding target .
qed

lemma relative_carrier_origin_state_base_step:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and D: "D = adp_defined_symbols (R \<union> B)"
    and state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
    and step: "(t, u) \<in> rstep B"
  obtains C' holes' owners' locations' carriers' where
    "relative_carrier_origin_state R B D s u C' holes'
      owners' locations' carriers'"
    "(carriers, carriers') \<in> (listrel1 (rstep B))\<^sup>*"
proof -
  have wfB: "wf_trs B" using wf unfolding wf_trs_def by blast
  have defs: "adp_defined_symbols (R \<union> B) \<subseteq> D"
    unfolding D by simp
  obtain l r p sigma where rule: "(l, r) \<in> B"
    and p: "p \<in> poss t"
    and p_defined: "p \<in> adp_defined_positions D t"
    and redex: "t |_ p = l \<cdot> sigma"
    and u: "u = replace_at t p (r \<cdot> sigma)"
    by (rule weak_rstep_has_defined_event[OF step wfB defs]) blast
  have nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
    using nd rule unfolding nonduplicating_trs_def by blast
  have p_fun: "p \<in> fun_poss t"
    using adp_defined_positions_fun_poss p_defined by blast
  from state have length: "num_holes C = length holes"
    and source: "fill_holes C holes = t"
    and cover: "carrier_cover holes owners locations carriers"
    unfolding relative_carrier_origin_state_def
      relative_context_origin_state_def by blast+
  have t_source:
      "t = (ctxt_of_pos_term p t)\<langle>l \<cdot> sigma\<rangle>"
    using sym[OF ctxt_supt_id[OF p]] redex by simp
  have raw: "(fill_holes C holes, u) \<in>
      rstep_r_p_s' B (l, r) p sigma"
    unfolding source u
    using rule p t_source by (auto intro!: rstep_r_p_s'I)
  consider (outer) "p \<in> poss_mctxt C"
    | (inner) i ti where
        "i < length holes"
        "u = fill_holes C (holes[i := ti])"
        "(holes ! i, ti) \<in>
          rstep_r_p_s' B (l, r) (pos_diff p (hole_poss' C ! i)) sigma"
        "hole_poss' C ! i \<le>\<^sub>p p"
    using relative_adp_filled_rewrite_cases[OF length raw] by metis
  then show thesis
  proof cases
    case outer
    obtain parents tails where state':
        "relative_carrier_origin_state R B D s u
          (mreplace_at C p (rhs_origin_mctxt l r p C))
          (unfill_holes
            (mreplace_at C p (rhs_origin_mctxt l r p C)) u)
          (refined_carrier_owners owners parents)
          (refined_carrier_locations locations parents tails) carriers"
      using relative_carrier_origin_state_root_base[
        OF state rule nondup outer(1) p_defined p_fun redex]
      unfolding u by blast
    have carriers: "(carriers, carriers) \<in> (listrel1 (rstep B))\<^sup>*"
      by simp
    show thesis by (rule that[OF state' carriers])
  next
    case (inner i ti)
    let ?beta = "pos_diff p (hole_poss' C ! i)"
    have local_raw: "(holes ! i, ti) \<in>
        rstep_r_p_s' B (l, r) ?beta sigma"
      by (rule inner(3))
    have beta_poss: "?beta \<in> poss (holes ! i)"
      using local_raw by (auto simp: rstep_r_p_s'.simps)
    have local_redex: "holes ! i |_ ?beta = l \<cdot> sigma"
      using local_raw by (auto simp: rstep_r_p_s'.simps)
    have ti: "ti = replace_at (holes ! i) ?beta (r \<cdot> sigma)"
      using local_raw by (auto simp: rstep_r_p_s'.simps)
    from wfB rule obtain f ls where lhs: "l = Fun f ls"
      using wf_trs_imp_lhs_Fun by blast
    have beta: "?beta \<in> fun_poss (holes ! i)"
      by (rule poss_is_Fun_fun_poss[OF beta_poss])
         (use local_redex lhs in simp)
    have p_split: "p = hole_poss' C ! i @ ?beta"
      using inner(4) by simp
    let ?carriers' = "carriers[owners ! i :=
      replace_at (carriers ! (owners ! i))
        (locations ! i @ ?beta) (r \<cdot> sigma)]"
    have target: "fill_holes C
        (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)]) =
        replace_at t p (r \<cdot> sigma)"
      using inner(2) ti u by simp
    have state_fill: "relative_carrier_origin_state R B D s
        (fill_holes C
          (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)])) C
        (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)])
        owners locations ?carriers'"
      by (rule relative_carrier_origin_state_inner_base[
        where A = "{}" and p = p,
        OF state inner(1) fun_poss_imp_poss[OF beta] rule
          origin_root_targets_empty nondup p_split p_fun redex target])
    have state': "relative_carrier_origin_state R B D s u C
        (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)])
        owners locations ?carriers'"
      using state_fill inner(2) ti by simp
    have carrier_step: "(carriers, ?carriers') \<in> listrel1 (rstep B)"
      by (rule carrier_list_inner_rewrite[
        OF cover inner(1) beta rule local_redex])
    have carrier_steps:
        "(carriers, ?carriers') \<in> (listrel1 (rstep B))\<^sup>*"
      by (rule r_into_rtrancl[OF carrier_step])
    show thesis by (rule that[OF state' carrier_steps])
  qed
qed

lemma relative_carrier_origin_state_base_steps:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and D: "D = adp_defined_symbols (R \<union> B)"
    and state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
    and steps: "(t, u) \<in> (rstep B)\<^sup>*"
  shows "\<exists>C' holes' owners' locations' carriers'.
    relative_carrier_origin_state R B D s u C' holes'
      owners' locations' carriers' \<and>
    (carriers, carriers') \<in> (listrel1 (rstep B))\<^sup>*"
  using steps state
proof (induct arbitrary: C holes owners locations carriers
    rule: rtrancl_induct)
  case base
  show ?case
    by (intro exI[of _ C] exI[of _ holes] exI[of _ owners]
        exI[of _ locations] exI[of _ carriers])
       (use base.prems in simp)
next
  case (step t u)
  obtain C1 holes1 owners1 locations1 carriers1 where state1:
      "relative_carrier_origin_state R B D s t C1 holes1
        owners1 locations1 carriers1"
    and carriers1:
      "(carriers, carriers1) \<in> (listrel1 (rstep B))\<^sup>*"
    using step.hyps(3)[OF step.prems] by blast
  obtain C2 holes2 owners2 locations2 carriers2 where state2:
      "relative_carrier_origin_state R B D s u C2 holes2
        owners2 locations2 carriers2"
    and carriers2:
      "(carriers1, carriers2) \<in> (listrel1 (rstep B))\<^sup>*"
    by (rule relative_carrier_origin_state_base_step[
      OF wf nd D state1 step.hyps(2)])
  have carriers:
      "(carriers, carriers2) \<in> (listrel1 (rstep B))\<^sup>*"
    by (rule rtrancl_trans[OF carriers1 carriers2])
  show ?case
    by (intro exI[of _ C2] exI[of _ holes2] exI[of _ owners2]
        exI[of _ locations2] exI[of _ carriers2])
       (rule conjI[OF state2 carriers])
qed

lemma filled_defined_position_cases:
  assumes length: "num_holes C = length holes"
    and source: "fill_holes C holes = t"
    and defined: "p \<in> adp_defined_positions D t"
  obtains (outer) "p \<in> poss_mctxt C"
    | (inner) i beta where
        "i < length holes"
        "beta \<in> poss (holes ! i)"
        "p = hole_poss' C ! i @ beta"
proof -
  have p_poss: "p \<in> poss t"
    using defined unfolding adp_defined_positions_def by blast
  let ?l = "t |_ p"
  have t_context: "t = (ctxt_of_pos_term p t)\<langle>?l\<rangle>"
    by (rule sym, rule ctxt_supt_id[OF p_poss])
  have raw: "(fill_holes C holes, t) \<in>
      rstep_r_p_s' {(?l, ?l)} (?l, ?l) p Var"
    unfolding source
    using t_context hole_pos_ctxt_of_pos_term[OF p_poss]
    by (auto intro!: rstep_r_p_s'I)
  consider (outer') "p \<in> poss_mctxt C"
    | (inner') i ti where
        "i < length holes"
        "(holes ! i, ti) \<in> rstep_r_p_s' {(?l, ?l)} (?l, ?l)
          (pos_diff p (hole_poss' C ! i)) Var"
        "hole_poss' C ! i \<le>\<^sub>p p"
    using rewrite_cases[OF length raw] by metis
  then show thesis
  proof cases
    case outer'
    show thesis by (rule outer[OF outer'])
  next
    case (inner' i ti)
    let ?beta = "pos_diff p (hole_poss' C ! i)"
    have beta: "?beta \<in> poss (holes ! i)"
      using inner'(2) by (auto simp: rstep_r_p_s'.simps)
    have split: "p = hole_poss' C ! i @ ?beta"
      using inner'(3) by simp
    show thesis by (rule inner[OF inner'(1) beta split])
  qed
qed

lemma relative_carrier_origin_state_strict_step:
  assumes wf: "wf_trs (R \<union> B)"
    and D: "D = adp_defined_symbols (R \<union> B)"
    and state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
    and carrier_sn: "\<And>j. j < length carriers \<Longrightarrow>
      SN_on (relstep R B) {carriers ! j}"
    and step: "(t, u) \<in> rstep R"
    and target_nt: "\<not> SN_on (relstep R B) {u}"
  obtains (inner) C' holes' carriers' where
      "relative_carrier_origin_state R B D s u C' holes'
        owners locations carriers'"
      "(carriers, carriers') \<in> listrel1 (rstep R)"
    | (productive) p q' q l r A phi sigma where
      "weak_pair_origin_trace R B D s t [] [] p q'"
      "(l, r) \<in> R"
      "origin_root_targets 1 D r A"
      "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
      "p \<in> fun_poss t"
      "t |_ p = l \<cdot> sigma"
      "u = replace_at t p (r \<cdot> sigma)"
      "origin_edge l r p sigma A phi q' q"
      "q \<in> adp_defined_positions D u"
      "u |_ q \<in> Tinf (relstep R B)"
proof -
  have wfR: "wf_trs R" using wf unfolding wf_trs_def by blast
  have defs: "adp_defined_symbols (B \<union> R) \<subseteq> D"
    unfolding D by (simp add: Un_commute)
  obtain l r p sigma where rule: "(l, r) \<in> R"
    and p_poss: "p \<in> poss t"
    and p_defined: "p \<in> adp_defined_positions D t"
    and redex: "t |_ p = l \<cdot> sigma"
    and u: "u = replace_at t p (r \<cdot> sigma)"
    and vars: "vars_term r \<subseteq> vars_term l"
    by (rule weak_rstep_has_defined_event[OF step wfR defs]) blast
  from wfR rule obtain f ls where lhs: "l = Fun f ls"
    using wf_trs_imp_lhs_Fun by blast
  have p_fun: "p \<in> fun_poss t"
    by (rule poss_is_Fun_fun_poss[OF p_poss]) (use redex lhs in simp)
  have t_source: "t = (ctxt_of_pos_term p t)\<langle>l \<cdot> sigma\<rangle>"
    using sym[OF ctxt_supt_id[OF p_poss]] redex by simp
  from state have length: "num_holes C = length holes"
    and source: "fill_holes C holes = t"
    and cover: "carrier_cover holes owners locations carriers"
    and origin: "relative_context_origin_state R B D s t C holes"
    unfolding relative_carrier_origin_state_def
      relative_context_origin_state_def by blast+
  have raw: "(fill_holes C holes, u) \<in>
      rstep_r_p_s' R (l, r) p sigma"
    unfolding source u
    using rule p_poss redex t_source
    by (auto intro!: rstep_r_p_s'I simp: hole_pos_ctxt_of_pos_term)
  consider (outer) "p \<in> poss_mctxt C"
    | (inner') i ti where
        "i < length holes"
        "u = fill_holes C (holes[i := ti])"
        "(holes ! i, ti) \<in>
          rstep_r_p_s' R (l, r) (pos_diff p (hole_poss' C ! i)) sigma"
        "hole_poss' C ! i \<le>\<^sub>p p"
    using relative_adp_filled_rewrite_cases[OF length raw] by metis
  then show thesis
  proof cases
    case outer
    obtain v where uv: "u \<unrhd> v" and minimal: "v \<in> Tinf (relstep R B)"
      using not_SN_imp_subt_Tinf[OF target_nt] by blast
    obtain q where q_poss: "q \<in> poss u" and q_at: "u |_ q = v"
      using supteq_imp_subt_at[OF uv] by blast
    have q_minimal: "u |_ q \<in> Tinf (relstep R B)"
      using minimal q_at by simp
    have q_root_defined: "[] \<in> adp_defined_positions D (u |_ q)"
      unfolding D by (rule Tinf_root_is_adp_defined[OF wf q_minimal])
    have q_defined: "q \<in> adp_defined_positions D u"
      by (rule adp_defined_root_subterm_imp_position[OF q_poss q_root_defined])
    have q_nonterm: "q \<in> nonterminating_defined_positions R B D u"
      unfolding nonterminating_defined_positions_def
      using q_defined q_minimal unfolding Tinf_def by blast
    obtain A phi q' where targets: "origin_root_targets 1 D r A"
      and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
      and q'_nonterm: "q' \<in> nonterminating_defined_positions R B D t"
      and edge: "origin_edge l r p sigma A phi q' q"
    proof (rule strict_rewrite_pulls_back_target[
          OF rule vars p_poss p_defined redex])
      show "q \<in> nonterminating_defined_positions R B D
          (replace_at t p (r \<cdot> sigma))"
        using q_nonterm unfolding u .
    qed
    have q'_defined: "q' \<in> adp_defined_positions D t"
      and q'_nt: "\<not> SN_on (relstep R B) {t |_ q'}"
      using q'_nonterm unfolding nonterminating_defined_positions_def by blast+
    have q'_context: "q' \<in> poss_mctxt C"
    proof -
      consider (ctx) "q' \<in> poss_mctxt C"
        | (hole) i beta where
            "i < length holes" "beta \<in> poss (holes ! i)"
            "q' = hole_poss' C ! i @ beta"
        using filled_defined_position_cases[OF length source q'_defined]
        by metis
      then show ?thesis
      proof cases
        case ctx
        then show ?thesis .
      next
        case (hole i beta)
      note i_hole = hole(1) and beta_hole = hole(2) and split_hole = hole(3)
      from carrier_coverD[OF cover i_hole] have owner:
          "owners ! i < length carriers"
        and location: "locations ! i \<in> poss (carriers ! (owners ! i))"
        and carrier_hole: "holes ! i =
          carriers ! (owners ! i) |_ locations ! i" by blast+
      have beta_carrier: "beta \<in> poss
          (carriers ! (owners ! i) |_ locations ! i)"
        using beta_hole carrier_hole by simp
      have position: "locations ! i @ beta \<in>
          poss (carriers ! (owners ! i))"
        using location beta_carrier by (simp only: poss_append_poss)
      have length': "length holes = num_holes C" using length by simp
      have i_num: "i < num_holes C" using i_hole length by simp
      have hole_pos: "hole_poss' C ! i \<in> poss t"
        unfolding source[symmetric]
        by (rule hole_poss_in_poss_fill_holes[OF length i_num])
      have t_append: "t |_ (hole_poss' C ! i @ beta) =
          t |_ hole_poss' C ! i |_ beta"
        by (rule subt_at_append[OF hole_pos])
      have at_position: "carriers ! (owners ! i) |_
          (locations ! i @ beta) = t |_ q'"
        using subt_at_append[OF location, of beta] source carrier_hole split_hole
          subt_at_fill_holes[OF length' i_num] t_append by simp
      have subterm: "carriers ! (owners ! i) \<unrhd> t |_ q'"
        using subt_at_imp_supteq[OF position] at_position by simp
      have "SN_on (relstep R B) {t |_ q'}"
        by (rule subterm_preserves_SN_on_relstep[
          OF carrier_sn[OF owner] subterm])
      with q'_nt show ?thesis by contradiction
      qed
    qed
    have trace: "weak_pair_origin_trace R B D s t [] [] p q'"
      using origin outer q'_context p_defined q'_defined
      unfolding relative_context_origin_state_def by blast
    show thesis by (rule productive[OF trace rule targets valid p_fun redex
      u edge q_defined q_minimal])
  next
    case (inner' i ti)
    let ?beta = "pos_diff p (hole_poss' C ! i)"
    have local_raw: "(holes ! i, ti) \<in>
        rstep_r_p_s' R (l, r) ?beta sigma" by (rule inner'(3))
    have beta: "?beta \<in> poss (holes ! i)"
      using local_raw by (auto simp: rstep_r_p_s'.simps)
    have local_redex: "holes ! i |_ ?beta = l \<cdot> sigma"
      using local_raw by (auto simp: rstep_r_p_s'.simps)
    have ti: "ti = replace_at (holes ! i) ?beta (r \<cdot> sigma)"
      using local_raw by (auto simp: rstep_r_p_s'.simps)
    have beta_fun: "?beta \<in> fun_poss (holes ! i)"
      by (rule poss_is_Fun_fun_poss[OF beta])
         (use local_redex lhs in simp)
    have split: "p = hole_poss' C ! i @ ?beta"
      using inner'(4) by simp
    let ?carriers' = "carriers[owners ! i :=
      replace_at (carriers ! (owners ! i))
        (locations ! i @ ?beta) (r \<cdot> sigma)]"
    have state': "relative_carrier_origin_state R B D s u C
        (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)])
        owners locations ?carriers'"
    proof -
      have updated: "relative_carrier_origin_state R B D s
          (fill_holes C
            (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)])) C
          (holes[i := replace_at (holes ! i) ?beta (r \<cdot> sigma)])
          owners locations ?carriers'"
        by (rule relative_carrier_origin_state_inner_strict[
          OF state inner'(1) beta rule split p_fun redex])
           (use inner'(2) ti u in simp)
      show ?thesis using updated inner'(2) ti by simp
    qed
    have carrier_step: "(carriers, ?carriers') \<in> listrel1 (rstep R)"
      by (rule carrier_list_inner_rewrite[
        OF cover inner'(1) beta_fun rule local_redex])
    show thesis by (rule inner[OF state' carrier_step])
  qed
qed

definition relative_root_origin_witness ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> bool" where
  "relative_root_origin_witness R B D s \<longleftrightarrow>
    (\<exists>t u p q' q l r A phi sigma.
      weak_pair_origin_trace R B D s t [] [] p q' \<and>
      (l, r) \<in> R \<and>
      origin_root_targets 1 D r A \<and>
      valid_vrf (plain_adp_term l, plain_adp_term r) phi \<and>
      p \<in> fun_poss t \<and>
      t |_ p = l \<cdot> sigma \<and>
      u = replace_at t p (r \<cdot> sigma) \<and>
      origin_edge l r p sigma A phi q' q \<and>
      q \<in> adp_defined_positions D u \<and>
      u |_ q \<in> Tinf (relstep R B))"

theorem relative_root_origin_productive_direct:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
  shows "relative_root_origin_productive R B
    (adp_defined_symbols (R \<union> B))"
proof (unfold relative_root_origin_productive_def, intro allI impI)
  fix s
  let ?D = "adp_defined_symbols (R \<union> B)"
  let ?M = "(listrel1 (rstep B))\<^sup>* O listrel1 (rstep R) O
    (listrel1 (rstep B))\<^sup>*"
  assume minimal: "s \<in> Tinf (relstep R B)"
    and defined: "[] \<in> adp_defined_positions ?D s"
  let ?carriers = "root_hole_terms s"
  have D_eq: "?D = adp_defined_symbols (R \<union> B)" by simp
  have fun_s: "is_Fun s"
    using defined unfolding adp_defined_positions_def by auto
  have state0: "relative_carrier_origin_state R B ?D s s
      (root_hole_mctxt s) (root_hole_terms s)
      (initial_carrier_owners (root_hole_terms s))
      (initial_carrier_locations (root_hole_terms s)) ?carriers"
    by (rule initial_relative_carrier_origin_state[OF fun_s defined])
  have components0: "\<And>x. x \<in> set ?carriers \<Longrightarrow>
      SN_on (relstep R B) {x}"
    using initial_carriers_relterminating[OF minimal] by blast
  have product: "SN_on ?M {?carriers}"
    by (rule initial_carriers_finite_product_relterminating[OF minimal])
  have reverse_product:
      "SN_on {(y, z). (z, y) \<in> converse ?M} {?carriers}"
    using product by auto
  have carrier_acc: "?carriers \<in> Wellfounded.acc (converse ?M)"
    by (rule SN_on_imp_acc[OF reverse_product])
  have recurse: "\<And>carriers.
      carriers \<in> Wellfounded.acc (converse ?M) \<Longrightarrow>
      (\<forall>t C holes owners locations.
        relative_carrier_origin_state R B ?D s t C holes
          owners locations carriers \<longrightarrow>
        \<not> SN_on (relstep R B) {t} \<longrightarrow>
        (\<forall>x \<in> set carriers. SN_on (relstep R B) {x}) \<longrightarrow>
        relative_root_origin_witness R B ?D s)"
  proof -
    fix carriers
    assume acc: "carriers \<in> Wellfounded.acc (converse ?M)"
    from acc show "\<forall>t C holes owners locations.
        relative_carrier_origin_state R B ?D s t C holes
          owners locations carriers \<longrightarrow>
        \<not> SN_on (relstep R B) {t} \<longrightarrow>
        (\<forall>x \<in> set carriers. SN_on (relstep R B) {x}) \<longrightarrow>
        relative_root_origin_witness R B ?D s"
    proof (induct rule: acc.induct)
      case (accI carriers)
      show ?case
      proof (intro allI impI)
        fix t C holes owners locations
        assume state: "relative_carrier_origin_state R B ?D s t C holes
            owners locations carriers"
          and t_nt: "\<not> SN_on (relstep R B) {t}"
          and components: "\<forall>x \<in> set carriers.
            SN_on (relstep R B) {x}"
        obtain n a b where weak_pow: "(t, a) \<in> (rstep B) ^^ n"
          and strict: "(a, b) \<in> rstep R"
          and b_nt: "\<not> SN_on (relstep R B) {b}"
          using not_SN_on_rel_succ[OF t_nt] by blast
        have weak: "(t, a) \<in> (rstep B)\<^sup>*"
          by (rule relpow_imp_rtrancl[OF weak_pow])
        obtain C1 holes1 owners1 locations1 carriers1 where state1:
            "relative_carrier_origin_state R B ?D s a C1 holes1
              owners1 locations1 carriers1"
          and carrier_weak:
            "(carriers, carriers1) \<in> (listrel1 (rstep B))\<^sup>*"
          using relative_carrier_origin_state_base_steps[
            OF wf nd D_eq state weak] by blast
        have components1: "\<And>x. x \<in> set carriers1 \<Longrightarrow>
            SN_on (relstep R B) {x}"
          by (rule carrier_components_SN_after_steps[
              OF _ carrier_weak]) (use components in auto)
        have indexed1: "\<And>j. j < length carriers1 \<Longrightarrow>
            SN_on (relstep R B) {carriers1 ! j}"
          by (rule components1) simp
        consider (inner) C2 holes2 carriers2 where
            "relative_carrier_origin_state R B ?D s b C2 holes2
              owners1 locations1 carriers2"
            "(carriers1, carriers2) \<in> listrel1 (rstep R)"
          | (productive) p q' q l r A phi sigma where
            "weak_pair_origin_trace R B ?D s a [] [] p q'"
            "(l, r) \<in> R"
            "origin_root_targets 1 ?D r A"
            "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
            "p \<in> fun_poss a"
            "a |_ p = l \<cdot> sigma"
            "b = replace_at a p (r \<cdot> sigma)"
            "origin_edge l r p sigma A phi q' q"
            "q \<in> adp_defined_positions ?D b"
            "b |_ q \<in> Tinf (relstep R B)"
          by (rule relative_carrier_origin_state_strict_step[
              OF wf D_eq state1 indexed1 strict b_nt])
        then show "relative_root_origin_witness R B ?D s"
        proof cases
          case (productive p q' q l r A phi sigma)
          show ?thesis
            unfolding relative_root_origin_witness_def
            using productive by blast
        next
          case (inner C2 holes2 carriers2)
          have carrier_strict_star:
              "(carriers1, carriers2) \<in> (listrel1 (rstep R))\<^sup>*"
            by (rule r_into_rtrancl[OF inner(2)])
          have components2: "\<And>x. x \<in> set carriers2 \<Longrightarrow>
              SN_on (relstep R B) {x}"
            by (rule carrier_components_SN_after_steps[
                OF components1 carrier_strict_star]) auto
          have measure: "(carriers, carriers2) \<in> ?M"
            using carrier_weak inner(2)
            by (auto simp: relcomp_unfold)
          have descent: "(carriers2, carriers) \<in> converse ?M"
            using measure by simp
          have ih: "\<forall>t C holes owners locations.
              relative_carrier_origin_state R B ?D s t C holes
                owners locations carriers2 \<longrightarrow>
              \<not> SN_on (relstep R B) {t} \<longrightarrow>
              (\<forall>x \<in> set carriers2.
                SN_on (relstep R B) {x}) \<longrightarrow>
              relative_root_origin_witness R B ?D s"
            by (rule accI.hyps[OF descent])
          show ?thesis using ih inner(1) b_nt components2 by blast
        qed
      qed
    qed
  qed
  have witness: "relative_root_origin_witness R B ?D s"
    using recurse[OF carrier_acc] state0 minimal components0
    unfolding Tinf_def by blast
  show "\<exists>t u p q' q l r A phi sigma.
      weak_pair_origin_trace R B ?D s t [] [] p q' \<and>
      (l, r) \<in> R \<and>
      origin_root_targets 1 ?D r A \<and>
      valid_vrf (plain_adp_term l, plain_adp_term r) phi \<and>
      p \<in> fun_poss t \<and>
      t |_ p = l \<cdot> sigma \<and>
      u = replace_at t p (r \<cdot> sigma) \<and>
      origin_edge l r p sigma A phi q' q \<and>
      q \<in> adp_defined_positions ?D u \<and>
      u |_ q \<in> Tinf (relstep R B)"
    using witness unfolding relative_root_origin_witness_def .
qed

theorem canonical_relative_adp_chain_criterion_direct:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and not_sn: "\<not> SN_rel (rstep R) (rstep B)"
  shows "\<not> adp_problem_SN (canonical_relative_adp_problem R B)"
  by (rule relative_root_origin_chain_criterion[
        OF wf relative_root_origin_productive_direct[OF wf nd] not_sn])

theorem canonical_relative_adp_SN_imp_relative_SN:
  assumes wf: "wf_trs (R \<union> B)"
    and nd: "nonduplicating_trs B"
    and adp: "adp_problem_SN (canonical_relative_adp_problem R B)"
  shows "SN_rel (rstep R) (rstep B)"
proof (rule ccontr)
  assume "\<not> SN_rel (rstep R) (rstep B)"
  then have "\<not> adp_problem_SN (canonical_relative_adp_problem R B)"
    by (rule canonical_relative_adp_chain_criterion_direct[OF wf nd])
  with adp show False by contradiction
qed

end
