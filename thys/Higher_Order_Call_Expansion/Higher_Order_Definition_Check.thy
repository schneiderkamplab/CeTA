theory Higher_Order_Definition_Check
  imports Higher_Order_Beta_Instances
begin

definition ho_beta_head_step where
  "ho_beta_head_step t=(case (ho_application_head t,ho_spine_arguments t) of
    (HAbs A b,x#xs) \<Rightarrow> Some (ho_apply_terms (ho_beta_subst x 0 b) xs)
    | _ \<Rightarrow> None)"

primrec ho_beta_head_normal where
  "ho_beta_head_normal 0 t=None"
| "ho_beta_head_normal (Suc n) t=(case ho_beta_head_step t of
    None \<Rightarrow> Some t | Some u \<Rightarrow> ho_beta_head_normal n u)"

lemma ho_beta_head_step_sound:
  assumes checked: "ho_beta_head_step t=Some u"
  shows "ho_step S V R B t u"
proof -
  obtain A b x xs where head: "ho_application_head t=HAbs A b"
    and args: "ho_spine_arguments t=x#xs"
    and eq: "u=ho_apply_terms (ho_beta_subst x 0 b) xs"
    using checked unfolding ho_beta_head_step_def
    by (auto split: prod.splits ho_term.splits list.splits)
  have t: "t=ho_apply_terms (HAbs A b) (x#xs)"
    using ho_spine_reconstruct[of t] head args by simp
  show ?thesis unfolding t eq
    by (simp add: ho_expansion_apply_step[OF ho_step.beta])
qed

lemma ho_beta_head_normal_sound:
  "ho_beta_head_normal n t=Some u \<Longrightarrow> (ho_step S V R B)\<^sup>*\<^sup>* t u"
proof (induction n arbitrary: t u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "ho_beta_head_step t")
    case None
    then show ?thesis using Suc.prems by simp
  next
    case (Some v)
    have tail: "(ho_step S V R B)\<^sup>*\<^sup>* v u"
      by (rule Suc.IH) (use Suc.prems Some in simp)
    show ?thesis
      by (rule converse_rtranclp_into_rtranclp[OF ho_beta_head_step_sound[OF Some] tail])
  qed
qed

definition ho_check_definition_expansion where
  "ho_check_definition_expansion R c e fuel=
    (ho_closed_at 0 e \<and> list_all (\<lambda>(G,l,r).
      ho_application_head (ho_erase_pattern l)=HConst c \<longrightarrow>
      ho_beta_head_normal fuel (ho_apply_terms e (ho_spine_arguments (ho_erase_pattern l)))=
        Some (ho_erase_pattern r)) R)"

context ho_source_neutral_reducibility
begin

theorem ho_check_definition_expansion_roots:
  assumes checked: "ho_check_definition_expansion R c e fuel"
    and split: "xs=ps@qs"
    and root: "ho_root_step S V R B (ho_apply_terms (HConst c) ps) u"
  shows "(ho_step S V R B)\<^sup>*\<^sup>* (ho_apply_terms e xs) (ho_apply_terms u qs)"
proof -
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and li: "ho_instantiate s 0 l=Some (ho_apply_terms (HConst c) ps)"
    and ri: "ho_instantiate s 0 r=Some u"
    using root unfolding ho_root_step_def by blast
  have head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using rule_instance_head_spine(1)[OF member li] by simp
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  have left: "ho_subst s 0 (ho_erase_pattern l)=ho_apply_terms (HConst c) ps"
    using li ho_zero_arity_instantiate[OF zl, of s 0] by simp
  have right: "ho_subst s 0 (ho_erase_pattern r)=u"
    using ri ho_zero_arity_instantiate[OF zr, of s 0] by simp
  let ?ls = "ho_spine_arguments (ho_erase_pattern l)"
  have reconstruct: "ho_apply_terms (HConst c) ?ls=ho_erase_pattern l"
    using ho_spine_reconstruct[of "ho_erase_pattern l"] head by simp
  have mapped: "map (ho_subst s 0) ?ls=ps"
  proof -
    have "ho_apply_terms (HConst c) (map (ho_subst s 0) ?ls)=ho_apply_terms (HConst c) ps"
      using ho_subst_apply_terms[of s 0 "HConst c" ?ls] reconstruct left by simp
    then show ?thesis
      by (metis ho_apply_terms_arguments ho_spine_arguments.simps(4) append_Nil)
  qed
  have closed: "ho_closed_at 0 e" and normal:
    "ho_beta_head_normal fuel (ho_apply_terms e ?ls)=Some (ho_erase_pattern r)"
    using checked member head unfolding ho_check_definition_expansion_def
    by (auto simp: list_all_iff)
  have beta: "(ho_step S G [] [])\<^sup>*\<^sup>* (ho_apply_terms e ?ls) (ho_erase_pattern r)"
    by (rule ho_beta_head_normal_sound[OF normal])
  have inst: "(ho_step S V R B)\<^sup>*\<^sup>* (ho_apply_terms e ps) u"
    using ho_expansion_beta_instances[OF beta, where s=s and V=V and R=R and B=B]
      ho_closed_free_subst[OF closed, of s 0]
    by (simp add: ho_subst_apply_terms mapped right)
  show ?thesis using ho_expansion_apply_steps[OF inst, where xs=qs]
    by (simp add: split)
qed

end

context ho_source_accessible_reducibility
begin

definition ho_expansion_admissible where
  "ho_expansion_admissible b T x=
    (ho_typeof S V B x=Some T \<and> source.strongly_normalizing x \<and>
      (ho_positive_type rank (rank b) T \<longrightarrow> source_candidate T x))"

lemma ho_expansion_admissible_step:
  assumes before: "ho_expansion_admissible b T x" and step: "ho_step S V R B x y"
  shows "ho_expansion_admissible b T y"
proof -
  have ty: "ho_typeof S V B y=Some T"
    by (rule ho_zero_arity_step_type[OF step zero])
      (use before in \<open>simp add: ho_expansion_admissible_def\<close>)
  have sx: "source.strongly_normalizing x"
    using before by (simp add: ho_expansion_admissible_def)
  have sn: "source.strongly_normalizing y"
    by (rule accp_downward[OF sx]) (rule step)
  have candidate: "ho_positive_type rank (rank b) T \<Longrightarrow> source_candidate T y"
    using before source_candidate_reduction[OF _ step]
    unfolding ho_expansion_admissible_def by blast
  show ?thesis using ty sn candidate unfolding ho_expansion_admissible_def by blast
qed

lemma ho_expansion_admissible_arguments_step:
  assumes before: "list_all2 (ho_expansion_admissible b) Ts xs"
    and step: "ho_arguments_step S V R B xs ys"
  shows "list_all2 (ho_expansion_admissible b) Ts ys"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain As A Bs where ts: "Ts=As@A#Bs"
    and pre: "list_all2 (ho_expansion_admissible b) As us"
    and middle: "ho_expansion_admissible b A v"
    and post: "list_all2 (ho_expansion_admissible b) Bs vs"
    using before unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have updated: "ho_expansion_admissible b A w"
    by (rule ho_expansion_admissible_step[OF middle vw])
  show ?thesis unfolding ts ys using pre updated post
    by (auto intro: list_all2_appendI)
qed

theorem source_candidate_checked_expansion:
  assumes symbol: "ho_lookup S c=Some T"
    and args: "list_all2 (ho_expansion_admissible (ho_result_sort T)) (ho_argument_types T) xs"
    and checked: "ho_check_definition_expansion R c e fuel"
    and expanded: "source_candidate (HBase (ho_result_sort T)) (ho_apply_terms e xs)"
  shows "source_candidate (HBase (ho_result_sort T)) (ho_apply_terms (HConst c) xs)"
proof -
  let ?P = "\<lambda>ys. list_all2 (ho_expansion_admissible (ho_result_sort T)) (ho_argument_types T) ys"
  show ?thesis
  proof (rule source_candidate_call_expansion[where P="?P", OF args _ _ _ _ _ expanded])
    fix ys x assume p: "?P ys" and member: "x\<in>set ys"
    obtain A where "ho_expansion_admissible (ho_result_sort T) A x"
      using p member by (metis list_all2_nthD2 in_set_conv_nth)
    then show "source.strongly_normalizing x" by (simp add: ho_expansion_admissible_def)
  next
    fix ys assume p: "?P ys"
    have types: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (ho_argument_types T) ys"
      by (rule list_all2_mono[OF p]) (simp add: ho_expansion_admissible_def)
    show "ho_typeof S V B (ho_apply_terms (HConst c) ys)=Some (HBase (ho_result_sort T))"
      by (rule ho_apply_terms_type[OF _ types]) (use symbol in simp)
  next
    fix ys A x assume p: "?P ys"
      and av: "(A,x)\<in>ho_accessible_arguments rank S V B (ho_apply_terms (HConst c) ys)"
    have types: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (ho_argument_types T) ys"
      by (rule list_all2_mono[OF p]) (simp add: ho_expansion_admissible_def)
    have ty: "ho_typeof S V B (ho_apply_terms (HConst c) ys)=Some (HBase (ho_result_sort T))"
      by (rule ho_apply_terms_type[OF _ types]) (use symbol in simp)
    have av': "x\<in>set ys \<and> ho_typeof S V B x=Some A \<and>
        ho_positive_type rank (rank (ho_result_sort T)) A"
      using av unfolding ho_accessible_arguments_def
      by (simp only: ty option.case ho_type.case ho_apply_terms_head
          ho_application_head.simps ho_term.case ho_apply_terms_arguments ho_spine_arguments.simps
          append_Nil mem_Collect_eq prod.case)
    have member: "x\<in>set ys" and xt: "ho_typeof S V B x=Some A"
      and pos: "ho_positive_type rank (rank (ho_result_sort T)) A"
      using av' by auto
    obtain U where adm: "ho_expansion_admissible (ho_result_sort T) U x"
      using p member by (metis list_all2_nthD2 in_set_conv_nth)
    have "U=A" using adm xt unfolding ho_expansion_admissible_def by simp
    then show "source_candidate A x" using adm pos unfolding ho_expansion_admissible_def by blast
  next
    fix ys zs assume "?P ys" and "ho_arguments_step S V R B ys zs"
    then show "?P zs" by (rule ho_expansion_admissible_arguments_step)
  next
    fix ys ps qs u assume "?P ys" and split: "ys=ps@qs"
      and root: "ho_root_step S V R B (ho_apply_terms (HConst c) ps) u"
    show "(ho_step S V R B)\<^sup>*\<^sup>* (ho_apply_terms e ys) (ho_apply_terms u qs)"
      by (rule ho_check_definition_expansion_roots[OF checked split root])
  qed
qed

end
end
