theory Relative_ADP_Chain_Criterion
  imports
    Relative_ADP_Semantics_Dev.Relative_ADP_Semantics
    First_Order_Terms.Term_Impl
begin

text \<open>
  The sound direction of the relative annotated dependency-pair chain criterion is
  developed here, outside the stable semantics theory.  The formulation below
  makes the two obligations from Theorem 23 explicit: each source rewrite step is
  represented by a concrete rule/position/substitution witness, and an origin
  choice records the variable-repositioning function and the at-most-one/two
  function positions selected at the contracted root.
\<close>

type_synonym ('f, 'v) rewrite_event =
  "(('f, 'v) rule \<times> pos) \<times> ('f, 'v) subst"

definition valid_rewrite_event ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) rewrite_event \<Rightarrow>
    ('f, 'v) term \<Rightarrow> bool" where
  "valid_rewrite_event R s event t \<longleftrightarrow>
    (case event of ((lr, p), sigma) \<Rightarrow>
      lr \<in> R \<and> p \<in> poss s \<and> s |_ p = fst lr \<cdot> sigma \<and>
      t = replace_at s p (snd lr \<cdot> sigma))"

lemma valid_rewrite_event_imp_rstep:
  assumes "valid_rewrite_event R s event t"
  shows "(s, t) \<in> rstep R"
proof (cases event)
  case (Pair a sigma)
  then obtain lr p where a: "a = (lr, p)" by (cases a)
  from assms have step:
    "lr \<in> R" "p \<in> poss s" "s |_ p = fst lr \<cdot> sigma"
    "t = replace_at s p (snd lr \<cdot> sigma)"
    unfolding valid_rewrite_event_def Pair a by auto
  show ?thesis
    by (rule rstep_r_p_s_imp_rstep[where r = lr and p = p and \<sigma> = sigma])
       (use step in \<open>auto simp: rstep_r_p_s_def'\<close>)
qed

lemma rstep_has_valid_rewrite_event:
  assumes "(s, t) \<in> rstep R"
  obtains event where "valid_rewrite_event R s event t"
proof -
  from assms obtain l r p sigma where
    "(s, t) \<in> rstep_r_p_s R (l, r) p sigma"
    by (auto simp: rstep_iff_rstep_r_p_s)
  then have
    "(l, r) \<in> R" "p \<in> poss s" "s |_ p = l \<cdot> sigma"
    "t = replace_at s p (r \<cdot> sigma)"
    unfolding rstep_r_p_s_def' by auto
  then show thesis
    by (intro that[of "(((l, r), p), sigma)"])
       (auto simp: valid_rewrite_event_def)
qed

definition origin_root_targets ::
  "nat \<Rightarrow> 'f set \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set \<Rightarrow> bool" where
  "origin_root_targets n D r A \<longleftrightarrow>
    A \<subseteq> adp_defined_positions D r \<and>
    card A \<le> min n (card (adp_defined_positions D r))"

lemma origin_root_targets_empty [simp]:
  "origin_root_targets n D r {}"
  unfolding origin_root_targets_def by simp

lemma origin_root_targets_extend:
  assumes targets: "origin_root_targets n D r A"
  obtains C where
    "A \<subseteq> C"
    "C \<subseteq> adp_defined_positions D r"
    "card C = min n (card (adp_defined_positions D r))"
proof -
  let ?U = "adp_defined_positions D r"
  let ?k = "min n (card ?U)"
  from targets have AU: "A \<subseteq> ?U" and cardA: "card A \<le> ?k"
    unfolding origin_root_targets_def by auto
  have finiteA: "finite A" by (rule finite_subset[OF AU]) simp
  have room: "?k - card A \<le> card (?U - A)"
  proof -
    have kU: "?k \<le> card ?U" by simp
    have "card (?U - A) = card ?U - card A"
      by (rule card_Diff_subset[OF finiteA AU])
    with kU show ?thesis by simp
  qed
  obtain B where Bcard: "card B = ?k - card A" and BU: "B \<subseteq> ?U - A"
    using obtain_subset_with_card_n[OF room] by blast
  let ?C = "A \<union> B"
  have disjoint: "A \<inter> B = {}" using BU by auto
  have finiteB: "finite B" by (rule finite_subset[OF BU]) simp
  have Ccard: "card ?C = ?k"
    using cardA finiteA finiteB disjoint Bcard by (simp add: card_Un_disjoint)
  show thesis
    by (rule that[of ?C]) (use AU BU Ccard in auto)
qed

lemma origin_root_targets_has_canonical_adp:
  assumes rule: "(l, r) \<in> R"
    and targets: "origin_root_targets n D r A"
  obtains C where
    "A \<subseteq> C"
    "(plain_adp_term l, annotate_term C r) \<in> canonical_adps n D R"
proof -
  obtain C where AC: "A \<subseteq> C" and CU: "C \<subseteq> adp_defined_positions D r"
    and cardC: "card C = min n (card (adp_defined_positions D r))"
    using origin_root_targets_extend[OF targets] by blast
  have "(plain_adp_term l, annotate_term C r) \<in> canonical_adps n D R"
    using rule CU cardC unfolding canonical_adps_def by blast
  with AC show thesis by (rule that)
qed

text \<open>
  The next lemma is the local non-duplication obligation used in the paper's
  origin graph: every variable occurrence in the right-hand side must receive a
  distinct predecessor occurrence in the left-hand side.  Its proof is kept as
  the first isolated milestone of the chain-criterion development.
\<close>

definition covers_rhs_variables ::
  "('f, 'v) rule \<Rightarrow> (pos \<Rightarrow> pos option) \<Rightarrow> bool" where
  "covers_rhs_variables lr phi \<longleftrightarrow>
    valid_vrf (plain_adp_term (fst lr), plain_adp_term (snd lr)) phi \<and>
    (\<forall>q \<in> var_poss (snd lr). \<exists>p \<in> var_poss (fst lr). phi p = Some q)"

definition variable_occurrences ::
  "('f, 'v) term \<Rightarrow> 'v \<Rightarrow> pos set" where
  "variable_occurrences t x = {p \<in> var_poss t. t |_ p = Var x}"

lemma mset_vars_term_list [simp]:
  "mset (vars_term_list t) = vars_term_ms t"
proof (induct t)
  case (Var x)
  then show ?case by (simp add: vars_term_list.simps)
next
  case (Fun f ts)
  have maps:
    "map (mset \<circ> vars_term_list) ts = map vars_term_ms ts"
    using Fun by (intro map_cong) auto
  have "mset (vars_term_list (Fun f ts)) =
      sum_list (map (mset \<circ> vars_term_list) ts)"
    by (simp add: vars_term_list.simps mset_concat comp_def)
  also have "... = sum_list (map vars_term_ms ts)" by (simp add: maps)
  also have "... = sum_mset (mset (map vars_term_ms ts))"
    by (rule sym, rule sum_mset_sum_list)
  also have "... = sum_mset (image_mset vars_term_ms (mset ts))" by simp
  also have "... = vars_term_ms (Fun f ts)" by simp
  finally show ?case .
qed

lemma map_variable_at_var_poss:
  "map (\<lambda>p. the_Var (t |_ p)) (var_poss_list t) = vars_term_list t"
proof (rule nth_equalityI)
  show "length (map (\<lambda>p. the_Var (t |_ p)) (var_poss_list t)) =
      length (vars_term_list t)"
    by (simp add: length_var_poss_list)
  fix i
  assume i: "i < length (map (\<lambda>p. the_Var (t |_ p)) (var_poss_list t))"
  then have i': "i < length (vars_term_list t)"
    by (simp add: length_var_poss_list)
  have at: "t |_ var_poss_list t ! i = Var (vars_term_list t ! i)"
    using vars_term_list_var_poss_list[OF i'] by simp
  show "map (\<lambda>p. the_Var (t |_ p)) (var_poss_list t) ! i = vars_term_list t ! i"
    using i at by simp
qed

lemma finite_variable_occurrences [simp]:
  "finite (variable_occurrences t x)"
  unfolding variable_occurrences_def by (rule finite_subset[OF _ finite_var_poss]) auto

lemma card_variable_occurrences:
  "card (variable_occurrences t x) = count (vars_term_ms t) x"
proof -
  have dist: "distinct (var_poss_list t)" by (rule distinct_var_poss_list)
  have set_filter:
    "set (filter (\<lambda>p. the_Var (t |_ p) = x) (var_poss_list t)) =
      variable_occurrences t x"
    unfolding variable_occurrences_def
    using var_poss_iff by force
  have "card (variable_occurrences t x) =
      length (filter (\<lambda>p. the_Var (t |_ p) = x) (var_poss_list t))"
    unfolding set_filter[symmetric]
    by (rule distinct_card) (rule distinct_filter[OF dist])
  also have "... = count (mset (map (\<lambda>p. the_Var (t |_ p))
      (var_poss_list t))) x"
  proof -
    have "length (filter (\<lambda>p. the_Var (t |_ p) = x) ps) =
        count (mset (map (\<lambda>p. the_Var (t |_ p)) ps)) x" for ps
      by (induct ps) auto
    then show ?thesis .
  qed
  also have "... = count (vars_term_ms t) x"
    by (simp add: map_variable_at_var_poss)
  finally show ?thesis .
qed

definition variable_predecessor ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> 'v \<Rightarrow> pos \<Rightarrow> pos" where
  "variable_predecessor l r x =
    (SOME f. inj_on f (variable_occurrences r x) \<and>
      f ` variable_occurrences r x \<subseteq> variable_occurrences l x)"

lemma variable_predecessor_exists:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
  shows "inj_on (variable_predecessor l r x) (variable_occurrences r x) \<and>
    variable_predecessor l r x ` variable_occurrences r x
      \<subseteq> variable_occurrences l x"
proof -
  have card: "card (variable_occurrences r x) \<le> card (variable_occurrences l x)"
    using mset_subset_eq_count[OF nd, of x]
    by (simp add: card_variable_occurrences)
  have "\<exists>f. inj_on f (variable_occurrences r x) \<and>
      f ` variable_occurrences r x \<subseteq> variable_occurrences l x"
    using card finite_variable_occurrences
    by (simp add: inj_on_iff_card_le)
  then show ?thesis
    unfolding variable_predecessor_def by (rule someI_ex)
qed

definition rhs_predecessor ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos" where
  "rhs_predecessor l r q = variable_predecessor l r (the_Var (r |_ q)) q"

lemma rhs_predecessor_properties:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and q: "q \<in> var_poss r"
  shows "rhs_predecessor l r q \<in> var_poss l"
    and "l |_ rhs_predecessor l r q = r |_ q"
proof -
  have "\<exists>x. q \<in> poss r \<and> r |_ q = Var x"
    using q unfolding var_poss_iff by assumption
  then obtain x where rq: "r |_ q = Var x" by blast
  have qx: "q \<in> variable_occurrences r x"
    using q rq unfolding variable_occurrences_def by simp
  have image_mem:
    "variable_predecessor l r x q \<in>
      variable_predecessor l r x ` variable_occurrences r x"
    by (rule imageI[OF qx])
  have image_sub:
    "variable_predecessor l r x ` variable_occurrences r x
      \<subseteq> variable_occurrences l x"
    using variable_predecessor_exists[OF nd, of x] by simp
  have px: "variable_predecessor l r x q \<in> variable_occurrences l x"
    by (rule subsetD[OF image_sub image_mem])
  then show "rhs_predecessor l r q \<in> var_poss l"
    unfolding rhs_predecessor_def rq by (simp add: variable_occurrences_def)
  from px show "l |_ rhs_predecessor l r q = r |_ q"
    unfolding rhs_predecessor_def rq variable_occurrences_def by simp
qed

lemma rhs_predecessor_inj_on:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
  shows "inj_on (rhs_predecessor l r) (var_poss r)"
proof (rule inj_onI)
  fix q1 q2
  assume q1: "q1 \<in> var_poss r" and q2: "q2 \<in> var_poss r"
    and eq: "rhs_predecessor l r q1 = rhs_predecessor l r q2"
  have ex1: "\<exists>x. q1 \<in> poss r \<and> r |_ q1 = Var x"
    using q1 unfolding var_poss_iff by assumption
  have ex2: "\<exists>x. q2 \<in> poss r \<and> r |_ q2 = Var x"
    using q2 unfolding var_poss_iff by assumption
  obtain x1 where r1: "r |_ q1 = Var x1" using ex1 by blast
  obtain x2 where r2: "r |_ q2 = Var x2" using ex2 by blast
  have p1: "l |_ rhs_predecessor l r q1 = Var x1"
    using rhs_predecessor_properties(2)[OF nd q1] unfolding r1 .
  have p2: "l |_ rhs_predecessor l r q2 = Var x2"
    using rhs_predecessor_properties(2)[OF nd q2] unfolding r2 .
  from p1 p2 eq have x: "x1 = x2" by simp
  have q1x: "q1 \<in> variable_occurrences r x1"
    using q1 r1 unfolding variable_occurrences_def by simp
  have q2x: "q2 \<in> variable_occurrences r x1"
    using q2 r2 x unfolding variable_occurrences_def by simp
  have inj: "inj_on (variable_predecessor l r x1) (variable_occurrences r x1)"
    using variable_predecessor_exists[OF nd] by simp
  have pred_eq:
    "variable_predecessor l r x1 q1 = variable_predecessor l r x1 q2"
    using eq unfolding rhs_predecessor_def r1 r2 x by simp
  show "q1 = q2"
    by (rule inj_onD[OF inj pred_eq q1x q2x])
qed

definition covering_vrf ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos option" where
  "covering_vrf l r p =
    (if \<exists>q \<in> var_poss r. rhs_predecessor l r q = p
     then Some (SOME q. q \<in> var_poss r \<and> rhs_predecessor l r q = p)
     else None)"

lemma covering_vrf_selected:
  assumes ex: "\<exists>q \<in> var_poss r. rhs_predecessor l r q = p"
  obtains q where
    "covering_vrf l r p = Some q"
    "q \<in> var_poss r"
    "rhs_predecessor l r q = p"
proof -
  let ?P = "\<lambda>q. q \<in> var_poss r \<and> rhs_predecessor l r q = p"
  have "\<exists>q. ?P q" using ex by blast
  then have chosen: "?P (SOME q. ?P q)" by (rule someI_ex)
  show thesis
    by (rule that[of "SOME q. ?P q"])
       (use ex chosen in \<open>auto simp: covering_vrf_def\<close>)
qed

lemma covering_vrf_covers:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and q: "q \<in> var_poss r"
  shows "covering_vrf l r (rhs_predecessor l r q) = Some q"
proof -
  have ex: "\<exists>q' \<in> var_poss r. rhs_predecessor l r q' = rhs_predecessor l r q"
    using q by blast
  obtain q' where selected:
    "covering_vrf l r (rhs_predecessor l r q) = Some q'"
    "q' \<in> var_poss r"
    "rhs_predecessor l r q' = rhs_predecessor l r q"
    using covering_vrf_selected[OF ex] by blast
  have "q' = q"
    by (rule inj_onD[OF rhs_predecessor_inj_on[OF nd] selected(3) selected(2) q])
  with selected(1) show ?thesis by simp
qed

lemma plain_adp_term_var_poss [simp]:
  "var_poss (plain_adp_term t) = var_poss t"
  by (induct t) auto

lemma plain_adp_term_subt_at:
  assumes "p \<in> poss t"
  shows "plain_adp_term t |_ p = plain_adp_term (t |_ p)"
  using assms by (induct p arbitrary: t) (case_tac t; auto)+

lemma covering_vrf_at_lhs_position:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p: "p \<in> var_poss l"
  shows "case covering_vrf l r p of None \<Rightarrow> True
      | Some q \<Rightarrow>
          q \<in> var_poss r \<and>
          plain_adp_term l |_ p = plain_adp_term r |_ q"
proof (cases "\<exists>q \<in> var_poss r. rhs_predecessor l r q = p")
  case False
  then show ?thesis by (simp add: covering_vrf_def)
next
  case True
  obtain q where selected:
    "covering_vrf l r p = Some q" "q \<in> var_poss r"
    "rhs_predecessor l r q = p"
    using covering_vrf_selected[OF True] by blast
  have lp: "l |_ p = r |_ q"
    using rhs_predecessor_properties(2)[OF nd selected(2)] selected(3) by simp
  have pp: "p \<in> poss l" using p by (rule var_poss_imp_poss)
  have qp: "q \<in> poss r" using selected(2) by (rule var_poss_imp_poss)
  show ?thesis
    unfolding selected(1)
    using selected(2) lp plain_adp_term_subt_at[OF pp]
      plain_adp_term_subt_at[OF qp]
    by simp
qed

lemma covering_vrf_valid:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
  shows "valid_vrf (plain_adp_term l, plain_adp_term r) (covering_vrf l r)"
  unfolding valid_vrf_def fst_conv snd_conv plain_adp_term_var_poss
proof (intro ballI)
  fix p
  assume p: "p \<in> var_poss l"
  from covering_vrf_at_lhs_position[OF nd p]
  show "case covering_vrf l r p of None \<Rightarrow> True
      | Some q \<Rightarrow> q \<in> var_poss r \<and>
          plain_adp_term l |_ p = plain_adp_term r |_ q"
    by assumption
qed

theorem nonduplicating_rule_has_covering_vrf:
  assumes nd: "vars_term_ms r \<subseteq># vars_term_ms l"
  shows "covers_rhs_variables (l, r) (covering_vrf l r)"
  unfolding covers_rhs_variables_def fst_conv snd_conv
proof (intro conjI covering_vrf_valid[OF nd] ballI)
  fix q
  assume q: "q \<in> var_poss r"
  let ?p = "rhs_predecessor l r q"
  have "?p \<in> var_poss l" by (rule rhs_predecessor_properties(1)[OF nd q])
  moreover have "covering_vrf l r ?p = Some q"
    by (rule covering_vrf_covers[OF nd q])
  ultimately show "\<exists>p \<in> var_poss l. covering_vrf l r p = Some q" by blast
qed

end
