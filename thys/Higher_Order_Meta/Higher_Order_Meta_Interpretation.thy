theory Higher_Order_Meta_Interpretation
  imports Higher_Order_Meta_Instantiation
begin

fun ho_pattern_interpretation where
  "ho_pattern_interpretation S G D I m e (PBound n)=e n"
| "ho_pattern_interpretation S G D I m e (PConst n)=I n"
| "ho_pattern_interpretation S G D I m e (PApp p q)=
    (case ho_typeof S G D (ho_erase_pattern p) of Some (HArrow A C) \<Rightarrow>
      ho_sem_app A C (ho_pattern_interpretation S G D I m e p)
        (ho_pattern_interpretation S G D I m e q) | _ \<Rightarrow> Var 0)"
| "ho_pattern_interpretation S G D I m e (PAbs A p)=
    Abs (ho_pattern_interpretation S G (A#D) I (\<lambda>n. lift (m n) 0) (ho_env_lift e) p)"
| "ho_pattern_interpretation S G D I m e (PMeta n ps)=
    foldl App (m n) (map (ho_pattern_interpretation S G D I m e) ps)"

lemma ho_lower_betas:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> beta\<^sup>*\<^sup>* (ho_lower A t) (ho_lower A u)"
proof (induction A arbitrary: t u)
  case (HBase n)
  then show ?case by simp
next
  case (HArrow A C)
  show ?case unfolding ho_lower.simps
    by (rule HArrow.IH(2)[OF rtrancl_beta_AppL[OF HArrow.prems]])
qed

lemma ho_raise_betas:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> beta\<^sup>*\<^sup>* c d \<Longrightarrow>
    beta\<^sup>*\<^sup>* (ho_raise A t c) (ho_raise A u d)"
proof (induction A arbitrary: t u c d)
  case (HBase n)
  then show ?case by (simp add: ho_add_betas)
next
  case (HArrow A C)
  show ?case unfolding ho_raise.simps
    by (rule rtrancl_beta_Abs; rule HArrow.IH(2);
        intro rtrancl_beta_AppL lift_preserves_beta' HArrow.prems)
qed

lemma ho_sem_app_betas:
  "beta\<^sup>*\<^sup>* f g \<Longrightarrow> beta\<^sup>*\<^sup>* x y \<Longrightarrow>
    beta\<^sup>*\<^sup>* (ho_sem_app A C f x) (ho_sem_app A C g y)"
  unfolding ho_sem_app_def
  by (intro ho_raise_betas rtrancl_beta_App ho_lower_betas)

lemma ho_betas_fold:
  assumes "beta\<^sup>*\<^sup>* f g" "list_all2 (\<lambda>x y. beta\<^sup>*\<^sup>* x y) xs ys"
  shows "beta\<^sup>*\<^sup>* (foldl App f xs) (foldl App g ys)"
  using assms(2,1)
  by (induction arbitrary: f g rule: list_all2_induct) (auto intro: rtrancl_beta_App)

lemma ho_source_interpretation_lift:
  assumes ty: "ho_typeof S V B t=Some A" and closed: "ho_interpretation_closed I"
  shows "ho_source_interpretation S V (C#B) I (ho_env_lift e) (ho_lift 1 0 t)=
    lift (ho_source_interpretation S V B I e t) 0"
proof -
  have compiled: "ho_compile S V (C#B) (ho_lift 1 0 t)=
      ho_expr_rename Suc (ho_compile S V B t)"
    using ho_compile_lift_context[where B="[]" and D="[C]", simplified, OF ty]
    by (simp add: add.commute)
  show ?thesis unfolding ho_source_interpretation_def compiled
    by (simp add: ho_evaluate_rename ho_env_lift_def ho_env_cons_def ho_evaluate_lift[OF closed])
qed

lemma ho_pattern_interpretation_instance:
  assumes pattern: "ho_typeof S G D (ho_erase_pattern p)=Some A"
    and subst: "ho_typed_subst S V B G s"
    and instantiated: "ho_instantiate s (length D) p=Some u"
    and closed: "ho_interpretation_closed I"
    and metas: "\<And>n. n<length G \<Longrightarrow> m n=
      ho_source_interpretation S V (D@B) I e (ho_lift (length D) 0 (s n))"
    and bounds: "\<And>n. n<length D \<Longrightarrow> b n=e n"
  shows "beta\<^sup>*\<^sup>* (ho_pattern_interpretation S G D I m b p)
    (ho_source_interpretation S V (D@B) I e u)"
using pattern instantiated metas bounds
proof (induction p arbitrary: D A u m b e)
  case (PBound n)
  then show ?case by (auto simp: ho_source_interpretation_def split: if_splits)
next
  case (PConst n)
  then show ?case by (auto simp: ho_source_interpretation_def)
next
  case (PApp p q)
  obtain T where p: "ho_typeof S G D (ho_erase_pattern p)=Some (HArrow T A)"
    and q: "ho_typeof S G D (ho_erase_pattern q)=Some T"
    using PApp.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  obtain f x where f: "ho_instantiate s (length D) p=Some f"
    and x: "ho_instantiate s (length D) q=Some x" and u: "u=HApp f x"
    using PApp.prems(2) by (auto split: option.splits)
  have ft: "ho_typeof S V (D@B) f=Some (HArrow T A)"
    by (rule ho_instantiate_type[OF p subst f])
  show ?case unfolding u ho_pattern_interpretation.simps p option.simps ho_type.case
    ho_source_app[OF ft]
    by (rule ho_sem_app_betas[OF PApp.IH(1)[OF p f PApp.prems(3,4)]
      PApp.IH(2)[OF q x PApp.prems(3,4)]])
next
  case (PAbs T p)
  obtain C where p: "ho_typeof S G (T#D) (ho_erase_pattern p)=Some C"
    and a: "A=HArrow T C" using PAbs.prems(1) by (auto split: option.splits)
  obtain v where v: "ho_instantiate s (Suc (length D)) p=Some v" and u: "u=HAbs T v"
    using PAbs.prems(2) by auto
  have vt: "ho_typeof S V (T#(D@B)) v=Some C"
    using ho_instantiate_type[OF p subst] v by simp
  have m: "lift (m n) 0=ho_source_interpretation S V ((T#D)@B) I
      (ho_env_lift e) (ho_lift (length (T#D)) 0 (s n))" if "n<length G" for n
  proof -
    have st: "ho_typeof S V B (s n)=Some (G!n)" using subst that by (simp add: ho_typed_subst_def)
    have lifted: "ho_typeof S V (D@B) (ho_lift (length D) 0 (s n))=Some (G!n)"
      using ho_typeof_lift_context[where B="[]" and D=D, simplified, OF st] .
    have merge: "ho_lift 1 0 (ho_lift (length D) 0 (s n))=ho_lift (Suc (length D)) 0 (s n)"
      using ho_lift_merge_source[where c=0 and k=0 and e="length D" and d=1 and t="s n"] by simp
    show ?thesis using ho_source_interpretation_lift[OF lifted closed, of T e]
      PAbs.prems(3)[OF that]
      by (simp only: length_Cons append_Cons merge)
  qed
  have b: "ho_env_lift b n=ho_env_lift e n" if "n<length (T#D)" for n
    using that PAbs.prems(4) by (cases n) (auto simp: ho_env_lift_def ho_env_cons_def)
  have path: "beta\<^sup>*\<^sup>*
      (ho_pattern_interpretation S G (T#D) I (\<lambda>n. lift (m n) 0) (ho_env_lift b) p)
      (ho_source_interpretation S V ((T#D)@B) I (ho_env_lift e) v)"
    by (rule PAbs.IH[OF p _ m b]) (simp add: v)
  show ?case using rtrancl_beta_Abs[OF path]
    by (simp add: u ho_source_interpretation_def vt)
next
  case (PMeta n ps)
  obtain us where args: "those (map (ho_instantiate s (length D)) ps)=Some us"
    and applied: "ho_meta_apply (ho_lift (length D) 0 (s n)) us=Some u"
    using PMeta.prems(2) by (auto split: option.splits)
  have original: "ho_typeof S G D (foldl HApp (HFree n) (map ho_erase_pattern ps))=Some A"
    using PMeta.prems(1) by simp
  have n: "n<length G" using ho_typed_fold_head[OF original] by (auto split: if_splits)
  have types: "list_all (\<lambda>p. \<exists>T. ho_typeof S G D (ho_erase_pattern p)=Some T) ps"
    using ho_typed_fold_arguments[OF original] by (simp add: list_all_iff)
  have paths: "list_all2 (\<lambda>x y. beta\<^sup>*\<^sup>* x y)
      (map (ho_pattern_interpretation S G D I m b) ps)
      (map (ho_source_interpretation S V (D@B) I e) us)"
    using args types PMeta.IH
  proof (induction ps arbitrary: us)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    then show ?case using PMeta.prems(3,4) by (auto split: option.splits)
  qed
  have argument_paths: "list_all2 (\<lambda>x y. (ho_step S V [] (D@B))\<^sup>*\<^sup>* x y)
      (map (\<lambda>p. ho_subst s (length D) (ho_erase_pattern p)) ps) us"
    using args
    by (induction ps arbitrary: us)
       (auto split: option.splits intro: ho_instantiate_beta_path)
  have typed_start: "ho_typeof S V (D@B)
      (ho_subst s (length D) (foldl HApp (HFree n) (map ho_erase_pattern ps)))=Some A"
    by (rule ho_typeof_free_subst_context[OF original subst])
  have typed: "ho_typeof S V (D@B) (foldl HApp (ho_lift (length D) 0 (s n)) us)=Some A"
    using ho_empty_steps_type[OF ho_empty_steps_fold[OF rtranclp.rtrancl_refl argument_paths]] typed_start
    by (simp add: ho_subst_fold map_map o_def)
  have first: "beta\<^sup>*\<^sup>* (ho_pattern_interpretation S G D I m b (PMeta n ps))
      (foldl App (ho_source_interpretation S V (D@B) I e (ho_lift (length D) 0 (s n)))
        (map (ho_source_interpretation S V (D@B) I e) us))"
    using ho_betas_fold[OF rtranclp.rtrancl_refl paths, of "m n"] PMeta.prems(3)[OF n] by simp
  show ?case by (rule rtranclp_trans[OF first ho_meta_apply_interpretation_path[OF applied typed closed]])
qed

end
