theory Relative_ADP_Com_Reduction_Pair
  imports
    Relative_ADP_Derelatification_Dev.Relative_ADP_Derelatification
begin

datatype 'f adp_com_symbol =
    ADP_Symbol "'f adp_symbol"
  | Com0
  | Com2

fun adp_combine_terms ::
  "('f adp_com_symbol, 'v) term list \<Rightarrow>
   ('f adp_com_symbol, 'v) term" where
  "adp_combine_terms [] = Fun Com0 []"
| "adp_combine_terms [t] = t"
| "adp_combine_terms (t # u # ts) =
    Fun Com2 [t, adp_combine_terms (u # ts)]"

definition relative_adp_annotation_summary ::
  "('f, 'v) adp \<Rightarrow> ('f adp_com_symbol, 'v) term" where
  "relative_adp_annotation_summary pair = adp_combine_terms
    (map (map_funs_term ADP_Symbol)
      (annotated_rhs_subterms_list pair))"

definition adp_com_monotone ::
  "(('f adp_com_symbol, 'v) term \<times>
     ('f adp_com_symbol, 'v) term) set \<Rightarrow> bool" where
  "adp_com_monotone S \<longleftrightarrow> (\<forall>s1 s2 t.
    (s1,s2) \<in> S \<longrightarrow>
      (Fun Com2 [s1,t], Fun Com2 [s2,t]) \<in> S \<and>
      (Fun Com2 [t,s1], Fun Com2 [t,s2]) \<in> S)"

definition adp_com_invariant ::
  "(('f adp_com_symbol, 'v) term \<times>
     ('f adp_com_symbol, 'v) term) set \<Rightarrow> bool" where
  "adp_com_invariant NS \<longleftrightarrow> (\<forall>x y z.
    (Fun Com2 [x,y], Fun Com2 [y,x]) \<in> NS \<and>
    (Fun Com2 [y,x], Fun Com2 [x,y]) \<in> NS \<and>
    (Fun Com2 [x, Fun Com2 [y,z]],
      Fun Com2 [Fun Com2 [x,y],z]) \<in> NS \<and>
    (Fun Com2 [Fun Com2 [x,y],z],
      Fun Com2 [x, Fun Com2 [y,z]]) \<in> NS)"

lemma relative_adp_annotation_summary_empty:
  assumes "annotated_rhs_subterms_list pair = []"
  shows "relative_adp_annotation_summary pair = Fun Com0 []"
  using assms unfolding relative_adp_annotation_summary_def by simp

lemma relative_adp_annotation_summary_singleton:
  assumes "annotated_rhs_subterms_list pair = [t]"
  shows "relative_adp_annotation_summary pair = map_funs_term ADP_Symbol t"
  using assms unfolding relative_adp_annotation_summary_def by simp

lemma relative_adp_annotation_summary_pair:
  assumes "annotated_rhs_subterms_list pair = [s,t]"
  shows "relative_adp_annotation_summary pair =
    Fun Com2 [map_funs_term ADP_Symbol s, map_funs_term ADP_Symbol t]"
  using assms unfolding relative_adp_annotation_summary_def by simp

lemma plain_adp_term_pred_roundtrip:
  assumes "plain_adp_term_pred t"
  shows "plain_adp_term (erase_adp_term t) = t"
  using assms
  by (induction t) (auto simp: list_all_iff map_idI)

lemma relative_adp_flatten_preserves_plain_step:
  assumes step: "adp_step_case A False s t"
  shows "adp_step_case (erase_annotations_adp ` A) False s t"
  using step
proof cases
  case (adp_stepI l r phi p sigma annotations)
  let ?pair = "erase_annotations_adp (l,r)"
  have pair: "?pair \<in> erase_annotations_adp ` A"
    using adp_stepI(1) by blast
  have plain: "plain_adp_term_pred (fst ?pair)"
    unfolding erase_annotations_adp_def by simp
  have valid: "valid_vrf ?pair phi"
    by (rule valid_vrf_erase_annotations_adp[OF adp_stepI(3)])
  have lhs_roundtrip: "plain_adp_term (erase_adp_term l) = l"
    by (rule plain_adp_term_pred_roundtrip[OF adp_stepI(2)])
  have fst_pair: "fst ?pair = l"
    unfolding erase_annotations_adp_def using lhs_roundtrip by simp
  have lhs: "erase_adp_term (s |_ p) =
      erase_adp_term (fst ?pair) \<cdot> sigma"
    using adp_stepI(6) unfolding erase_annotations_adp_def by simp
  have annotation_eq: "annotations =
      (if False then sharp_positions (snd ?pair) else {}) \<union>
        transported_annotations phi (fst ?pair) (s |_ p)"
    using adp_stepI(7) fst_pair by simp
  have target: "t = replace_at s p
      (annotate_term annotations
        (erase_adp_term (snd ?pair) \<cdot> sigma))"
    using adp_stepI(8) unfolding erase_annotations_adp_def by simp
  show ?thesis
    apply (rule adp_step_case.adp_stepI[
      where l="fst ?pair" and r="snd ?pair" and phi=phi and p=p
        and sigma=sigma and A=annotations])
    subgoal using pair by simp
    subgoal by (fact plain)
    subgoal using valid by simp
    subgoal by (fact adp_stepI(4))
    subgoal by (fact adp_stepI(5))
    subgoal by (fact lhs)
    subgoal by (fact annotation_eq)
    subgoal by (fact target)
    done
qed

lemma relative_adp_plain_selected_step_in_residual:
  assumes step: "(s,t) \<in> adp_step_case_rel A False"
  shows "(s,t) \<in> adp_step (erase_annotations_adp ` A)"
proof -
  from step have "adp_step_case A False s t"
    unfolding adp_step_case_rel_def by simp
  then have "adp_step_case (erase_annotations_adp ` A) False s t"
    by (rule relative_adp_flatten_preserves_plain_step)
  then show ?thesis
    unfolding adp_step_def adp_step_case_rel_def by blast
qed

lemma relative_adp_main_without_selected_strict:
  "adp_step_case_rel P True - adp_step_case_rel A True \<subseteq>
    adp_step_case_rel (P - A) True"
proof -
  have "P = (P - A) \<union> (P \<inter> A)" by blast
  then have split: "adp_step_case_rel P True =
      adp_step_case_rel (P - A) True \<union>
      adp_step_case_rel (P \<inter> A) True"
    by (metis adp_step_case_rel_union)
  have "adp_step_case_rel (P \<inter> A) True \<subseteq>
      adp_step_case_rel A True"
    by (rule adp_step_case_rel_mono) blast
  with split show ?thesis by blast
qed

lemma relative_adp_steps_without_selected_strict:
  "adp_step (P \<union> B) - adp_step_case_rel A True \<subseteq>
    adp_step ((P - A) \<union> ((B - A) \<union>
      erase_annotations_adp ` A))"
proof
  fix step
  assume member: "step \<in>
      adp_step (P \<union> B) - adp_step_case_rel A True"
  obtain s t where step_eq: "step = (s,t)" by (cases step)
  from member step_eq obtain at_sharp where original:
      "adp_step_case (P \<union> B) at_sharp s t"
    unfolding adp_step_def adp_step_case_rel_def by auto
  from original obtain l r phi p sigma annotations where
      pair: "(l,r) \<in> P \<union> B"
    and plain: "plain_adp_term_pred l"
    and valid: "valid_vrf (l,r) phi"
    and redex: "p \<in> fun_poss s"
    and at: "at_sharp = (p \<in> sharp_positions s)"
    and lhs: "erase_adp_term (s |_ p) = erase_adp_term l \<cdot> sigma"
    and annotations: "annotations =
      (if at_sharp then sharp_positions r else {}) \<union>
        transported_annotations phi l (s |_ p)"
    and target: "t = replace_at s p
      (annotate_term annotations (erase_adp_term r \<cdot> sigma))"
    by cases blast
  show "step \<in> adp_step ((P - A) \<union> ((B - A) \<union>
      erase_annotations_adp ` A))"
  proof (cases "(l,r) \<in> A")
    case False
    have residual_pair: "(l,r) \<in>
        ((P - A) \<union> ((B - A) \<union> erase_annotations_adp ` A))"
      using pair False by blast
    have "adp_step_case
        ((P - A) \<union> ((B - A) \<union> erase_annotations_adp ` A))
        at_sharp s t"
      by (rule adp_step_case.adp_stepI[
          OF residual_pair plain valid redex at lhs annotations target])
    then show ?thesis unfolding step_eq adp_step_def adp_step_case_rel_def
      by (cases at_sharp) auto
  next
    case True
    have not_strict: "(s,t) \<notin> adp_step_case_rel A True"
      using member step_eq by simp
    have not_at_sharp: "at_sharp = False"
    proof (rule ccontr)
      assume "at_sharp \<noteq> False"
      then have "at_sharp = True" by simp
      moreover have "adp_step_case A at_sharp s t"
        by (rule adp_step_case.adp_stepI[
          OF True plain valid redex at lhs annotations target])
      ultimately have "adp_step_case A True s t" by simp
      with not_strict show False unfolding adp_step_case_rel_def by simp
    qed
    have "adp_step_case A False s t"
      by (rule adp_step_case.adp_stepI[
        OF True plain valid redex], use at lhs annotations target not_at_sharp in simp_all)
    then have "(s,t) \<in> adp_step_case_rel A False"
      unfolding adp_step_case_rel_def by simp
    then have "(s,t) \<in> adp_step (erase_annotations_adp ` A)"
      by (rule relative_adp_plain_selected_step_in_residual)
    moreover have "erase_annotations_adp ` A \<subseteq>
        (P - A) \<union> ((B - A) \<union> erase_annotations_adp ` A)"
      by blast
    ultimately show ?thesis unfolding step_eq
      using adp_step_mono by blast
  qed
qed

theorem relative_adp_com_reduction_pair:
  assumes redpair: "mono_redtriple_order S NS NST"
    and all_weak: "adp_step (P \<union> B) \<subseteq> NS"
    and selected_strict: "adp_step_case_rel A True \<subseteq> S"
    and residual: "adp_problem_SN
      (P - A, (B - A) \<union> erase_annotations_adp ` A)"
  shows "adp_problem_SN (P,B)"
proof (rule ccontr)
  interpret mono_redtriple_order S NS NST by (rule redpair)
  let ?R = "adp_step_case_rel P True"
  let ?W = "adp_step (P \<union> B)"
  let ?D = "adp_step_case_rel A True"
  let ?P' = "P - A"
  let ?B' = "(B - A) \<union> erase_annotations_adp ` A"
  assume not_sn: "\<not> adp_problem_SN (P,B)"
  then obtain terms where deriv: "ideriv ?R ?W terms"
    unfolding adp_problem_SN_def SN_rel_ideriv by auto
  have order_sn: "SN_rel S NS"
    unfolding SN_rel_defs
    by (rule SN_subset[OF compatible_SN'[OF compat_NS_S SN]], regexp)
  have selected_sn: "SN_rel ?D ?W"
    by (rule SN_rel_mono[OF selected_strict all_weak order_sn])
  have no_selected:
      "\<not> ideriv (?D \<inter> (?R \<union> ?W))
        ((?R \<union> ?W) - ?D) terms"
  proof
    assume selected: "ideriv (?D \<inter> (?R \<union> ?W))
        ((?R \<union> ?W) - ?D) terms"
    have "ideriv ?D ?W terms"
    proof (rule ideriv_mono[OF _ _ selected])
      show "?D \<inter> (?R \<union> ?W) \<subseteq> ?D" by blast
      show "(?R \<union> ?W) - ?D \<subseteq> ?W"
        using adp_step_case_rel_subset_adp_step[of P True]
          adp_step_mono[of P "P \<union> B"] by blast
    qed
    with selected_sn show False unfolding SN_rel_ideriv by blast
  qed
  from ideriv_split[OF deriv no_selected]
  obtain i where tail: "ideriv (?R - ?D) (?W - ?D) (shift terms i)"
    by blast
  have strict_tail: "?R - ?D \<subseteq> adp_step_case_rel ?P' True"
    by (rule relative_adp_main_without_selected_strict)
  have weak_tail: "?W - ?D \<subseteq> adp_step (?P' \<union> ?B')"
    by (rule relative_adp_steps_without_selected_strict)
  have "ideriv (adp_step_case_rel ?P' True)
      (adp_step (?P' \<union> ?B')) (shift terms i)"
    by (rule ideriv_mono[OF strict_tail weak_tail tail])
  moreover from residual have
      "\<not> (\<exists>xs. ideriv (adp_step_case_rel ?P' True)
        (adp_step (?P' \<union> ?B')) xs)"
    unfolding adp_problem_SN_def SN_rel_ideriv by simp
  ultimately show False by blast
qed

end
