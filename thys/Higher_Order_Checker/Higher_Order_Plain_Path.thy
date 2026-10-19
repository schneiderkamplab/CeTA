theory Higher_Order_Plain_Path
  imports Higher_Order_Pumping
begin

lemma ho_plain_subst:
  "ho_plain t \<Longrightarrow> (\<And>i. ho_plain (s i)) \<Longrightarrow> ho_plain (ho_subst s 0 t)"
  by (induction t) auto

inductive ho_plain_step for S V R where
  rule: "(G,l,r) \<in> set R \<Longrightarrow> ho_rule_welltyped S (G,l,r) \<Longrightarrow>
    ho_plain_pattern l \<Longrightarrow> ho_plain_pattern r \<Longrightarrow>
    (\<And>i. ho_plain (s i)) \<Longrightarrow> ho_typed_subst S V [] G s \<Longrightarrow>
    ho_plain_step S V R (ho_subst s 0 (ho_erase_pattern l)) (ho_subst s 0 (ho_erase_pattern r))"
| left: "ho_plain_step S V R t u \<Longrightarrow> ho_plain x \<Longrightarrow>
    ho_plain_step S V R (HApp t x) (HApp u x)"
| right: "ho_plain_step S V R t u \<Longrightarrow> ho_plain x \<Longrightarrow>
    ho_plain_step S V R (HApp x t) (HApp x u)"

lemma ho_plain_step_sound:
  "ho_plain_step S V R t u \<Longrightarrow> ho_step S V R [] t u"
  by (induction rule: ho_plain_step.induct)
     (auto intro: ho_step.intros ho_plain_pattern_instance)

lemma ho_plain_step_terms:
  "ho_plain_step S V R t u \<Longrightarrow> ho_plain t \<and> ho_plain u"
  by (induction rule: ho_plain_step.induct)
     (auto intro: ho_plain_subst ho_plain_pattern_erase)

lemma ho_plain_step_subst:
  assumes step: "ho_plain_step S V R t u"
    and q: "ho_typed_subst S V [] V q"
    and qp: "\<And>i. ho_plain (q i)"
  shows "ho_plain_step S V R (ho_subst q 0 t) (ho_subst q 0 u)"
  using step
proof (induction rule: ho_plain_step.induct)
  case (rule G l r s)
  have typed: "ho_typed_subst S V [] G (\<lambda>i. ho_subst q 0 (s i))"
    using rule.hyps(5,6) q unfolding ho_typed_subst_def
    by (auto intro: ho_plain_subst_type[OF _ _ q])
  have "ho_plain_step S V R
    (ho_subst (\<lambda>i. ho_subst q 0 (s i)) 0 (ho_erase_pattern l))
    (ho_subst (\<lambda>i. ho_subst q 0 (s i)) 0 (ho_erase_pattern r))"
    by (rule ho_plain_step.rule[OF rule.hyps(1-4) _ typed])
       (rule ho_plain_subst[OF rule.hyps(5) qp])
  then show ?case
    using ho_plain_pattern_erase[OF rule.hyps(3)] ho_plain_pattern_erase[OF rule.hyps(4)]
    by (simp add: ho_plain_subst_compose)
qed (auto intro: ho_plain_step.intros ho_plain_subst[OF _ qp])

fun ho_plain_context where
  "ho_plain_context HHole = True"
| "ho_plain_context (HCLeft C x) = (ho_plain_context C \<and> ho_plain x)"
| "ho_plain_context (HCRight x C) = (ho_plain x \<and> ho_plain_context C)"

lemma ho_plain_fill_step:
  "ho_plain_context C \<Longrightarrow> ho_plain_step S V R t u \<Longrightarrow>
    ho_plain_step S V R (ho_fill C t) (ho_fill C u)"
  by (induction C) (auto intro: ho_plain_step.intros)

definition ho_plain_relation where
  "ho_plain_relation S V R A = {(t,u). ho_typeof S V [] t = Some A \<and>
    ho_typeof S V [] u = Some A \<and> ho_plain_step S V R t u}"

lemma ho_plain_relation_subset:
  "ho_plain_relation S V R A \<subseteq> ho_relation S V R A"
  by (auto simp: ho_plain_relation_def ho_relation_def dest: ho_plain_step_sound)

theorem ho_plain_path_pumping:
  assumes path: "(t, ho_fill C (ho_subst q 0 t)) \<in> (ho_plain_relation S V R A)^+"
    and typed: "ho_typeof S V [] t = Some A"
      "ho_typeof S V [] (ho_fill C (ho_subst q 0 t)) = Some A"
    and plain: "ho_plain t" "ho_plain_context C"
    and q: "ho_typed_subst S V [] V q"
    and qp: "\<And>i. ho_plain (q i)"
  shows "\<not> wf ((ho_relation S V R A)\<inverse>)"
proof -
  have sub_t: "ho_typeof S V [] (ho_subst q 0 t) = Some A"
    by (rule ho_plain_subst_type[OF plain(1) typed(1) q])
  have mono: "(ho_fill C (ho_subst q 0 x),ho_fill C (ho_subst q 0 y))
      \<in> ho_plain_relation S V R A"
    if pair: "(x,y) \<in> ho_plain_relation S V R A" for x y
  proof -
    have st: "ho_plain_step S V R x y" and tx: "ho_typeof S V [] x=Some A"
      and ty: "ho_typeof S V [] y=Some A"
      using pair unfolding ho_plain_relation_def by auto
    have px: "ho_plain x" and py: "ho_plain y" using ho_plain_step_terms[OF st] by auto
    have sx: "ho_typeof S V [] (ho_subst q 0 x) = Some A"
      by (rule ho_plain_subst_type[OF px tx q])
    have sy: "ho_typeof S V [] (ho_subst q 0 y) = Some A"
      by (rule ho_plain_subst_type[OF py ty q])
    have step: "ho_plain_step S V R (ho_fill C (ho_subst q 0 x)) (ho_fill C (ho_subst q 0 y))"
      by (rule ho_plain_fill_step[OF plain(2) ho_plain_step_subst[OF st q qp]])
    show ?thesis using ho_fill_type[of S V "[]" "ho_subst q 0 x" "ho_subst q 0 t" C]
      ho_fill_type[of S V "[]" "ho_subst q 0 y" "ho_subst q 0 t" C]
      sx sy sub_t typed(2) step by (auto simp: ho_plain_relation_def)
  qed
  have "\<not> wf ((ho_plain_relation S V R A)\<inverse>)"
    by (rule relation_embedding_not_wf[where f="\<lambda>x. ho_fill C (ho_subst q 0 x)", OF path mono])
  then show ?thesis using ho_plain_relation_subset[of S V R A]
    by (meson converse_mono wf_subset)
qed

definition ho_plain_images where
  "ho_plain_images ss i = (if i<length ss then ss!i else HFree i)"

lemma ho_plain_images_plain:
  "list_all ho_plain ss \<Longrightarrow> ho_plain (ho_plain_images ss i)"
  by (auto simp: ho_plain_images_def list_all_iff)

fun ho_check_plain_step where
  "ho_check_plain_step S V R t (HRule i ss) =
    (if i<length R then case R!i of (G,l,r) \<Rightarrow>
      if length ss=length G \<and> ho_rule_welltyped S (G,l,r) \<and>
        ho_plain_pattern l \<and> ho_plain_pattern r \<and> list_all ho_plain ss \<and>
        ho_typed_subst S V [] G (ho_plain_images ss) \<and>
        t=ho_subst (ho_plain_images ss) 0 (ho_erase_pattern l)
      then Some (ho_subst (ho_plain_images ss) 0 (ho_erase_pattern r)) else None
     else None)"
| "ho_check_plain_step S V R t (HLeft p) = (case t of HApp f x \<Rightarrow>
    if ho_plain x then map_option (\<lambda>u. HApp u x) (ho_check_plain_step S V R f p) else None
    | _ \<Rightarrow> None)"
| "ho_check_plain_step S V R t (HRight p) = (case t of HApp f x \<Rightarrow>
    if ho_plain f then map_option (HApp f) (ho_check_plain_step S V R x p) else None
    | _ \<Rightarrow> None)"
| "ho_check_plain_step S V R t _ = None"

lemma ho_check_plain_step_sound:
  "ho_check_plain_step S V R t p=Some u \<Longrightarrow> ho_plain_step S V R t u"
proof (induction p arbitrary: t u)
  case (HRule i ss)
  then show ?case
    by (auto split: if_splits prod.splits;
        metis nth_mem ho_plain_step.rule ho_plain_images_plain)
qed (auto split: ho_term.splits option.splits if_splits intro: ho_plain_step.intros)

fun ho_check_plain_path where
  "ho_check_plain_path S V R A t [] = Some t"
| "ho_check_plain_path S V R A t (p#ps) = (case ho_check_plain_step S V R t p of
    None \<Rightarrow> None | Some u \<Rightarrow>
    if ho_typeof S V [] t=Some A \<and> ho_typeof S V [] u=Some A
    then ho_check_plain_path S V R A u ps else None)"

lemma ho_check_plain_path_sound:
  "ho_check_plain_path S V R A t ps=Some u \<Longrightarrow> (t,u)\<in>(ho_plain_relation S V R A)^*"
  by (induction ps arbitrary: t)
     (auto simp: ho_plain_relation_def split: option.splits if_splits
       intro: converse_rtrancl_into_rtrancl dest: ho_check_plain_step_sound)

definition ho_check_plain_pump where
  "ho_check_plain_pump S V R A t ps C ss \<longleftrightarrow>
    ps\<noteq>[] \<and> ho_plain t \<and> ho_plain_context C \<and> length ss=length V \<and>
    list_all ho_plain ss \<and> ho_typed_subst S V [] V (ho_plain_images ss) \<and>
    ho_typeof S V [] t=Some A \<and>
    ho_typeof S V [] (ho_fill C (ho_subst (ho_plain_images ss) 0 t))=Some A \<and>
    ho_check_plain_path S V R A t ps=Some (ho_fill C (ho_subst (ho_plain_images ss) 0 t))"

theorem ho_check_plain_pump_sound:
  assumes "ho_check_plain_pump S V R A t ps C ss"
  shows "\<not> wf ((ho_relation S V R A)\<inverse>)"
proof -
  obtain p qs where ps: "ps=p#qs"
    using assms unfolding ho_check_plain_pump_def by (cases ps) auto
  obtain u where st: "ho_check_plain_step S V R t p=Some u"
    and types: "ho_typeof S V [] t=Some A" "ho_typeof S V [] u=Some A"
    and rest: "ho_check_plain_path S V R A u qs=Some (ho_fill C (ho_subst (ho_plain_images ss) 0 t))"
    using assms unfolding ho_check_plain_pump_def ps by (auto split: option.splits if_splits)
  have first: "(t,u)\<in>ho_plain_relation S V R A"
    using ho_check_plain_step_sound[OF st] types by (simp add: ho_plain_relation_def)
  have path: "(t,ho_fill C (ho_subst (ho_plain_images ss) 0 t))\<in>(ho_plain_relation S V R A)^+"
    by (rule rtrancl_into_trancl2[OF first ho_check_plain_path_sound[OF rest]])
  show ?thesis by (rule ho_plain_path_pumping[OF path])
    (use assms in \<open>auto simp: ho_check_plain_pump_def intro: ho_plain_images_plain\<close>)
qed

end
