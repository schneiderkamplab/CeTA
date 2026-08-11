theory Relative_ADP_Carrier_Run
  imports Relative_ADP_Construction_Transition_Dev.Relative_ADP_Construction_Transition
begin

lemma initial_carriers_relterminating:
  assumes minimal: "s \<in> Tinf (relstep R B)"
    shows "\<forall>t \<in> set (root_hole_terms s).
    SN_on (relstep R B) {t}"
proof (cases s)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  show ?thesis
  proof (intro ballI)
    fix t
    assume t: "t \<in> set (root_hole_terms s)"
    have proper: "s \<rhd> t" using t unfolding Fun by auto
    from minimal have terminating_proper:
      "\<forall>u. s \<rhd> u \<longrightarrow> SN_on (relstep R B) {u}"
      unfolding Tinf_def by simp
    show "SN_on (relstep R B) {t}"
      by (rule terminating_proper[THEN spec, THEN mp, OF proper])
  qed
qed

lemma SN_on_listrel1_of_components:
  assumes components:
    "\<And>t. t \<in> set ss \<Longrightarrow> SN_on (relstep R B) {t}"
  shows "SN_on (listrel1 (relstep R B)) {ss}"
proof -
  have acc_components:
    "set ss \<subseteq> Wellfounded.acc (converse (relstep R B))"
  proof
    fix t
    assume "t \<in> set ss"
    then have "SN_on (relstep R B) {t}" by (rule components)
    then have "SN_on {(y, z). (z, y) \<in> converse (relstep R B)} {t}"
      by auto
    then show "t \<in> Wellfounded.acc (converse (relstep R B))"
      by (rule SN_on_imp_acc)
  qed
  have ss_components:
    "ss \<in> lists (Wellfounded.acc (converse (relstep R B)))"
    using acc_components
    unfolding in_lists_conv_set
    by blast
  have ss_acc : "ss \<in> Wellfounded.acc (listrel1 (converse (relstep R B)))"
    by (rule lists_accD[OF ss_components])
  from acc_imp_SN_on[OF ss_acc]
  show ?thesis by (simp add: listrel1_converse)
qed

lemma SN_rel_on_listrel1_of_components:
  assumes SN: "\<And>x. x \<in> set ss \<Longrightarrow> SN_rel_on R S {x}"
  shows "SN_rel_on (listrel1 R) (listrel1 S) {ss}"
proof (unfold SN_rel_on_ideriv, intro notI)
  assume "\<exists>as. ideriv (listrel1 R) (listrel1 S) as \<and> as 0 \<in> {ss}"
  then obtain as where deriv:
      "ideriv (listrel1 R) (listrel1 S) as"
    and initial: "as 0 = ss" by blast
  have steps: "\<And>i. (as i, as (Suc i)) \<in>
      listrel1 R \<union> listrel1 S"
    using deriv unfolding ideriv_def by blast
  have lengths: "\<And>i. length (as i) = length (as 0)"
  proof -
    fix i
    show "length (as i) = length (as 0)"
    proof (induct i)
      case 0 show ?case by simp
    next
      case (Suc i)
      from steps[of i] have "length (as i) = length (as (Suc i))"
        by (auto dest: listrel1_eq_len)
      with Suc show ?case by simp
    qed
  qed
  have strict_positions:
      "INFM i. \<exists>k < length (as 0).
        (as i ! k, as (Suc i) ! k) \<in> R"
  proof -
    have strict: "INFM i. (as i, as (Suc i)) \<in> listrel1 R"
      using deriv unfolding ideriv_def by blast
    show ?thesis
      using strict
    proof (rule INFM_mono)
      fix i
      assume "(as i, as (Suc i)) \<in> listrel1 R"
      then obtain y k where component: "(as i ! k, y) \<in> R"
        and k: "k < length (as i)"
        and update: "as (Suc i) = list_update (as i) k y"
        unfolding listrel1_iff_update by blast
      have target: "as (Suc i) ! k = y" using k update by simp
      show "\<exists>k<length (as 0).
          (as i ! k, as (Suc i) ! k) \<in> R"
        using component k target lengths[of i]
        by (intro exI[of _ k]) auto
    qed
  qed
  have distributed:
      "(INFM i. \<exists>k\<in>{..<length (as 0)}.
          (as i ! k, as (Suc i) ! k) \<in> R) =
       (\<exists>k\<in>{..<length (as 0)}.
          INFM i. (as i ! k, as (Suc i) ! k) \<in> R)"
    by (rule INFM_finite_Bex_distrib) simp
  have strict_positions_set:
      "INFM i. \<exists>k\<in>{..<length (as 0)}.
        (as i ! k, as (Suc i) ! k) \<in> R"
    using strict_positions
  proof (rule INFM_mono)
    fix i
    assume "\<exists>k<length (as 0).
      (as i ! k, as (Suc i) ! k) \<in> R"
    then show "\<exists>k\<in>{..<length (as 0)}.
      (as i ! k, as (Suc i) ! k) \<in> R" by blast
  qed
  from distributed[THEN iffD1, OF strict_positions_set]
  obtain k where k: "k < length (as 0)"
    and strict: "INFM i. (as i ! k, as (Suc i) ! k) \<in> R"
    by blast
  let ?component = "\<lambda>i. as i ! k"
  have component_steps: "\<And>i. (?component i, ?component (Suc i))
      \<in> R \<union> S\<^sup>="
  proof -
    fix i
    from steps[of i] show "(?component i, ?component (Suc i))
        \<in> R \<union> S\<^sup>="
    proof
      assume step: "(as i, as (Suc i)) \<in> listrel1 R"
      then obtain y j where rel: "(as i ! j, y) \<in> R"
        and j: "j < length (as i)"
        and update: "as (Suc i) = list_update (as i) j y"
        unfolding listrel1_iff_update by blast
      show ?thesis
      proof (cases "j = k")
        case True
        with rel j update show ?thesis by simp
      next
        case False
        with update show ?thesis by simp
      qed
    next
      assume step: "(as i, as (Suc i)) \<in> listrel1 S"
      then obtain y j where rel: "(as i ! j, y) \<in> S"
        and j: "j < length (as i)"
        and update: "as (Suc i) = list_update (as i) j y"
        unfolding listrel1_iff_update by blast
      show ?thesis
      proof (cases "j = k")
        case True
        with rel j update show ?thesis by simp
      next
        case False
        with update show ?thesis by simp
      qed
    qed
  qed
  have "ideriv R (S\<^sup>=) ?component"
    unfolding ideriv_def using component_steps strict by blast
  moreover have "SN_rel_on R (S\<^sup>=) {ss ! k}"
  proof (simp add: SN_rel_on_Id)
    show "SN_rel_on R S {ss ! k}"
      by (rule SN) (use k initial in simp)
  qed
  moreover have "?component 0 \<in> {ss ! k}"
    using initial by simp
  ultimately show False unfolding SN_rel_on_ideriv by blast
qed

lemma initial_carriers_finite_product_relterminating:
  assumes minimal: "s \<in> Tinf (relstep R B)"
  shows "SN_on ((listrel1 (rstep B))\<^sup>* O listrel1 (rstep R) O
    (listrel1 (rstep B))\<^sup>*) {root_hole_terms s}"
proof -
  have components:
    "\<And>t. t \<in> set (root_hole_terms s) \<Longrightarrow>
      SN_on (relstep R B) {t}"
    using initial_carriers_relterminating[OF minimal] by blast
  have product: "SN_rel_on (listrel1 (rstep R)) (listrel1 (rstep B))
      {root_hole_terms s}"
  proof (rule SN_rel_on_listrel1_of_components)
    fix t
    assume "t \<in> set (root_hole_terms s)"
    then have "SN_on (relstep R B) {t}" by (rule components)
    then show "SN_rel_on (rstep R) (rstep B) {t}"
      unfolding SN_rel_on_def .
  qed
  show ?thesis using product unfolding SN_rel_on_def .
qed

lemma carrier_components_SN_after_steps:
  assumes components: "\<And>x. x \<in> set xs \<Longrightarrow>
      SN_on (relstep R B) {x}"
    and steps: "(xs, ys) \<in> (listrel1 X)\<^sup>*"
    and X: "X \<subseteq> rstep R \<union> rstep B"
  shows "\<And>y. y \<in> set ys \<Longrightarrow> SN_on (relstep R B) {y}"
  using steps components
proof (induct arbitrary: rule: rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step ys zs)
  from step.hyps(2) obtain z i where rel: "(ys ! i, z) \<in> X"
    and i: "i < length ys" and zs: "zs = ys[i := z]"
    unfolding listrel1_iff_update by blast
  have ys_components: "\<And>x. x \<in> set ys \<Longrightarrow>
      SN_on (relstep R B) {x}"
  proof -
    fix x
    assume "x \<in> set ys"
    then show "SN_on (relstep R B) {x}"
      by (rule step.hyps(3)[OF _ step.prems(2)])
  qed
  have old_sn: "SN_on (relstep R B) {ys ! i}"
    by (rule ys_components) (use i in simp)
  have z_sn: "SN_on (relstep R B) {z}"
    by (rule step_preserves_SN_on_relto[OF subsetD[OF X rel] old_sn])
  show ?case
  proof (cases "y = z")
    case True
    then show ?thesis by (rule ssubst) (rule z_sn)
  next
    case False
    have "y \<in> insert z (set ys)"
      using set_update_subset_insert[of ys i z] step.prems(1) zs by blast
    with False have "y \<in> set ys" by blast
    then show ?thesis by (rule ys_components)
  qed
qed

lemma carrier_inner_rewrite:
  assumes cover: "carrier_cover holes owners locations carriers"
    and i: "i < length holes"
    and beta: "beta \<in> fun_poss (holes ! i)"
    and rule: "(l, r) \<in> X"
    and redex: "holes ! i |_ beta = l \<cdot> sigma"
  shows "(carriers ! (owners ! i),
      replace_at (carriers ! (owners ! i))
        (locations ! i @ beta) (r \<cdot> sigma)) \<in> rstep X"
proof -
  from carrier_coverD[OF cover i] have owner:
      "owners ! i < length carriers"
    and location: "locations ! i \<in> poss (carriers ! (owners ! i))"
    and hole: "holes ! i =
      carriers ! (owners ! i) |_ locations ! i" by blast+
  have beta_poss: "beta \<in> poss (holes ! i)"
    by (rule fun_poss_imp_poss[OF beta])
  have position: "locations ! i @ beta \<in>
      poss (carriers ! (owners ! i))"
    using location beta_poss hole by (simp only: poss_append_poss)
  have carrier_redex:
      "carriers ! (owners ! i) |_ (locations ! i @ beta) = l \<cdot> sigma"
    using subt_at_append[OF location, of beta] hole redex by simp
  show ?thesis
  proof (rule rstep.rstep[where
      C = "ctxt_of_pos_term (locations ! i @ beta)
        (carriers ! (owners ! i))" and \<sigma> = sigma and l = l and r = r])
    show "(l, r) \<in> X" by (rule rule)
    show "carriers ! (owners ! i) =
        (ctxt_of_pos_term (locations ! i @ beta)
          (carriers ! (owners ! i)))\<langle>l \<cdot> sigma\<rangle>"
      using ctxt_supt_id[OF position] carrier_redex by simp
    show "replace_at (carriers ! (owners ! i)) (locations ! i @ beta)
        (r \<cdot> sigma) =
        (ctxt_of_pos_term (locations ! i @ beta)
          (carriers ! (owners ! i)))\<langle>r \<cdot> sigma\<rangle>"
      by simp
  qed
qed

lemma carrier_list_inner_rewrite:
  assumes cover: "carrier_cover holes owners locations carriers"
    and i: "i < length holes"
    and beta: "beta \<in> fun_poss (holes ! i)"
    and rule: "(l, r) \<in> X"
    and redex: "holes ! i |_ beta = l \<cdot> sigma"
  shows "(carriers,
      carriers[owners ! i := replace_at (carriers ! (owners ! i))
        (locations ! i @ beta) (r \<cdot> sigma)]) \<in>
    listrel1 (rstep X)"
proof -
  from carrier_coverD[OF cover i] have owner:
    "owners ! i < length carriers" by blast
  have step: "(carriers ! (owners ! i),
      replace_at (carriers ! (owners ! i))
        (locations ! i @ beta) (r \<cdot> sigma)) \<in> rstep X"
    by (rule carrier_inner_rewrite[OF cover i beta rule redex])
  show ?thesis
    unfolding listrel1_iff_update
    by (rule exI[of _ "replace_at (carriers ! (owners ! i))
          (locations ! i @ beta) (r \<cdot> sigma)"],
        rule exI[of _ "owners ! i"])
       (use step owner in simp)
qed

end
