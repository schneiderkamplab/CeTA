theory Higher_Order_Expansion_Closure
  imports Higher_Order_Definition_Check
begin

definition ho_expansion_observation where
  "ho_expansion_observation S G obs recur t=(case ho_typeof S G [] t of
    None \<Rightarrow> False | Some T \<Rightarrow>
      ho_typeof S G [] (ho_apply_terms t (obs T))\<noteq>None \<and>
      recur (ho_apply_terms t (obs T)))"

definition ho_expansion_beta_branch where
  "ho_expansion_beta_branch S G obs recur t=(case
    (ho_typeof S G [] t,ho_application_head t,ho_spine_arguments t) of
    (Some (HBase b),HAbs A body,x#xs) \<Rightarrow>
      list_all (ho_expansion_observation S G obs recur) (x#xs) \<and>
      ho_typeof S G [] (ho_apply_terms (ho_beta_subst x 0 body) xs)=Some (HBase b) \<and>
      recur (ho_apply_terms (ho_beta_subst x 0 body) xs)
    | _ \<Rightarrow> False)"

definition ho_expansion_definition_branch where
  "ho_expansion_definition_branch S G R rank defs obs recur t=(case
    (ho_typeof S G [] t,ho_application_head t) of
    (Some (HBase b),HConst c) \<Rightarrow>
      (case ho_lookup S c of None \<Rightarrow> False | Some T \<Rightarrow>
       (case defs c of None \<Rightarrow> False | Some (e,fuel) \<Rightarrow>
        b=ho_result_sort T \<and>
        list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A)
          (ho_argument_types T) (ho_spine_arguments t) \<and>
        ho_check_definition_expansion R c e fuel \<and>
        ho_typeof S G [] (ho_apply_terms e (ho_spine_arguments t))=Some (HBase b) \<and>
        list_all (ho_expansion_observation S G obs recur) (ho_spine_arguments t) \<and>
        list_all (\<lambda>x. case ho_typeof S G [] x of None \<Rightarrow> False | Some A \<Rightarrow>
          ho_positive_type rank (rank b) A \<longrightarrow> recur x) (ho_spine_arguments t) \<and>
        recur (ho_apply_terms e (ho_spine_arguments t))
      ))
    | _ \<Rightarrow> False)"

primrec ho_check_expansion_closure where
  "ho_check_expansion_closure S G R rank defs obs leaf extra 0 t=False"
| "ho_check_expansion_closure S G R rank defs obs leaf extra (Suc n) t=
    (ho_typeof S G [] t\<noteq>None \<and>
      (leaf t \<or>
       extra (ho_check_expansion_closure S G R rank defs obs leaf extra n) t \<or>
       (case t of HApp f x \<Rightarrow>
         ho_check_expansion_closure S G R rank defs obs leaf extra n f \<and>
         ho_check_expansion_closure S G R rank defs obs leaf extra n x
        | _ \<Rightarrow> False) \<or>
       ho_expansion_beta_branch S G obs (ho_check_expansion_closure S G R rank defs obs leaf extra n) t \<or>
       ho_expansion_definition_branch S G R rank defs obs (ho_check_expansion_closure S G R rank defs obs leaf extra n) t))"

context ho_source_accessible_reducibility
begin

lemma ho_expansion_observation_sound:
  assumes checked: "ho_expansion_observation S G obs recur t"
    and subst: "ho_typed_subst S V B G s"
    and rec: "\<And>u A. recur u \<Longrightarrow> ho_typeof S G [] u=Some A \<Longrightarrow>
      source_candidate A (ho_subst s 0 u)"
  shows "source.strongly_normalizing (ho_subst s 0 t)"
proof -
  obtain T A where typed: "ho_typeof S G [] t=Some T"
    and observation: "ho_typeof S G [] (ho_apply_terms t (obs T))=Some A"
    and check: "recur (ho_apply_terms t (obs T))"
    using checked unfolding ho_expansion_observation_def
    by (auto split: option.splits)
  have comp: "source_candidate A (ho_apply_terms (ho_subst s 0 t) (map (ho_subst s 0) (obs T)))"
    using rec[OF check observation] by (simp add: ho_subst_apply_terms)
  have root: "Wellfounded.accp application_descent
      (ho_apply_terms (ho_subst s 0 t) (map (ho_subst s 0) (obs T)))"
    by (rule source_SN_application_descent[OF source.candidate_SN[OF comp]])
  show ?thesis
    by (rule application_descent_SN, rule application_subterm_accessible[OF root ho_expansion_apply_subterm])
qed

lemma ho_expansion_beta_branch_sound:
  assumes checked: "ho_expansion_beta_branch S G obs recur t"
    and ty: "ho_typeof S G [] t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and rec: "\<And>u T. recur u \<Longrightarrow> ho_typeof S G [] u=Some T \<Longrightarrow>
      source_candidate T (ho_subst s 0 u)"
  shows "source_candidate A (ho_subst s 0 t)"
proof -
  obtain b T body x xs where head: "ho_application_head t=HAbs T body"
    and args: "ho_spine_arguments t=x#xs"
    and result: "A=HBase b"
    and observed: "list_all (ho_expansion_observation S G obs recur) (x#xs)"
    and ct: "ho_typeof S G [] (ho_apply_terms (ho_beta_subst x 0 body) xs)=Some (HBase b)"
    and cc: "recur (ho_apply_terms (ho_beta_subst x 0 body) xs)"
    using checked ty unfolding ho_expansion_beta_branch_def
    by (auto split: prod.splits option.splits ho_type.splits ho_term.splits list.splits)
  have t: "t=ho_apply_terms (HAbs T body) (x#xs)"
    using ho_spine_reconstruct[of t] head args by simp
  have inst: "ho_subst s 0 t=
      ho_apply_terms (HAbs T (ho_subst s 1 body)) (ho_subst s 0 x#map (ho_subst s 0) xs)"
    unfolding t by (simp add: ho_subst_apply_terms)
  have sn: "source.strongly_normalizing v"
    if "v\<in>set (ho_subst s 0 x#map (ho_subst s 0) xs)" for v
    using observed that ho_expansion_observation_sound[OF _ subst rec]
    by (auto simp: list_all_iff)
  have typed: "ho_typeof S V B (ho_subst s 0 t)=Some (HBase b)"
    using ho_typeof_free_subst_context[OF ty subst] result by simp
  have child: "source_candidate (HBase b)
      (ho_apply_terms (ho_beta_subst (ho_subst s 0 x) 0 (ho_subst s 1 body))
        (map (ho_subst s 0) xs))"
    using rec[OF cc ct] ho_expansion_subst_beta[where d=0 and k=0 and s=s and u=x and t=body]
    by (simp add: ho_subst_apply_terms)
  show ?thesis unfolding result inst
    by (rule source_candidate_beta_spine[OF sn typed[unfolded inst] child])
qed

lemma ho_expansion_definition_branch_sound:
  assumes checked: "ho_expansion_definition_branch S G R rank defs obs recur t"
    and ty: "ho_typeof S G [] t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and rec: "\<And>u T. recur u \<Longrightarrow> ho_typeof S G [] u=Some T \<Longrightarrow>
      source_candidate T (ho_subst s 0 u)"
  shows "source_candidate A (ho_subst s 0 t)"
proof -
  obtain b c where tc: "ho_typeof S G [] t=Some (HBase b)"
    and hc: "ho_application_head t=HConst c"
    using checked unfolding ho_expansion_definition_branch_def
    by (auto split: option.split_asm ho_type.split_asm ho_term.split_asm)
  obtain T where sc: "ho_lookup S c=Some T"
    using checked unfolding ho_expansion_definition_branch_def tc hc
    by (cases "ho_lookup S c") auto
  obtain e fuel where dc: "defs c=Some (e,fuel)"
    using checked sc unfolding ho_expansion_definition_branch_def tc hc
    by (cases "defs c") (auto split: option.split_asm)
  have head: "ho_application_head t=HConst c" using hc .
  have symbol: "ho_lookup S c=Some T" using sc .
  have result: "A=HBase b" using tc ty by simp
  have b: "b=ho_result_sort T"
    and types: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (ho_argument_types T) (ho_spine_arguments t)"
    and def_checked: "ho_check_definition_expansion R c e fuel"
    and expanded_type: "ho_typeof S G [] (ho_apply_terms e (ho_spine_arguments t))=Some (HBase b)"
    and observations: "list_all (ho_expansion_observation S G obs recur) (ho_spine_arguments t)"
    and accessible: "list_all (\<lambda>x. case ho_typeof S G [] x of None \<Rightarrow> False | Some U \<Rightarrow>
      ho_positive_type rank (rank b) U \<longrightarrow> recur x) (ho_spine_arguments t)"
    and expanded: "recur (ho_apply_terms e (ho_spine_arguments t))"
    by (use checked in \<open>auto simp only: ho_expansion_definition_branch_def tc hc prod.case option.case ho_term.case ho_type.case sc dc\<close>)
  have closed: "ho_closed_at 0 e" using def_checked unfolding ho_check_definition_expansion_def by simp
  have ec: "ho_subst s 0 e=e" by (rule ho_closed_free_subst[OF closed])
  have child: "source_candidate (HBase (ho_result_sort T))
      (ho_apply_terms e (map (ho_subst s 0) (ho_spine_arguments t)))"
    using rec[OF expanded expanded_type] b by (simp add: ho_subst_apply_terms ec)
  have individual: "ho_expansion_admissible (ho_result_sort T) U (ho_subst s 0 x)"
    if member: "x\<in>set (ho_spine_arguments t)" and xt: "ho_typeof S G [] x=Some U" for U x
  proof -
    have typed: "ho_typeof S V B (ho_subst s 0 x)=Some U"
      using ho_typeof_free_subst_context[OF xt subst] by simp
    have sn: "source.strongly_normalizing (ho_subst s 0 x)"
      by (rule ho_expansion_observation_sound[where obs=obs, OF _ subst rec])
        (use observations member in \<open>auto simp: list_all_iff\<close>)
    have pos: "ho_positive_type rank (rank (ho_result_sort T)) U \<Longrightarrow>
        source_candidate U (ho_subst s 0 x)"
      by (rule rec[OF _ xt])
        (use accessible member xt b in \<open>auto simp: list_all_iff\<close>)
    show ?thesis using typed sn pos unfolding ho_expansion_admissible_def by blast
  qed
  have admissible: "list_all2 (ho_expansion_admissible (ho_result_sort T))
      (ho_argument_types T) (map (ho_subst s 0) (ho_spine_arguments t))"
    using types individual
    by (induction rule: list_all2_induct) auto
  have eq: "ho_subst s 0 t=ho_apply_terms (HConst c) (map (ho_subst s 0) (ho_spine_arguments t))"
    using ho_subst_apply_terms[of s 0 "HConst c" "ho_spine_arguments t"]
      ho_spine_reconstruct[of t] head by simp
  show ?thesis unfolding result b eq
    by (rule source_candidate_checked_expansion[OF symbol admissible def_checked child])
qed

theorem ho_check_expansion_closure_sound:
  assumes checked: "ho_check_expansion_closure S G R rank defs obs leaf extra n t"
    and ty: "ho_typeof S G [] t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and extension_sound: "\<And>recur u T. (\<And>x U. recur x \<Longrightarrow> ho_typeof S G [] x=Some U \<Longrightarrow> source_candidate U (ho_subst s 0 x)) \<Longrightarrow> extra recur u \<Longrightarrow> ho_typeof S G [] u=Some T \<Longrightarrow> source_candidate T (ho_subst s 0 u)"
    and base: "\<And>u T. leaf u \<Longrightarrow> ho_typeof S G [] u=Some T \<Longrightarrow>
      source_candidate T (ho_subst s 0 u)"
  shows "source_candidate A (ho_subst s 0 t)"
  using checked ty
proof (induction n arbitrary: t A)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?rec = "ho_check_expansion_closure S G R rank defs obs leaf extra n"
  have cases: "leaf t \<or> extra ?rec t \<or>
      (case t of HApp f x \<Rightarrow> ?rec f \<and> ?rec x | _ \<Rightarrow> False) \<or>
      ho_expansion_beta_branch S G obs ?rec t \<or>
      ho_expansion_definition_branch S G R rank defs obs ?rec t"
    using Suc.prems(1) by simp
  from cases show ?case
  proof (elim disjE)
    assume "leaf t"
    then show ?thesis by (rule base[OF _ Suc.prems(2)])
  next
    assume ex: "extra ?rec t"
    show ?thesis by (rule extension_sound[OF Suc.IH ex Suc.prems(2)])
  next
    assume app: "(case t of HApp f x \<Rightarrow> ?rec f \<and> ?rec x | _ \<Rightarrow> False)"
    obtain f x where t: "t=HApp f x" and f: "?rec f" and x: "?rec x"
      using app by (auto split: ho_term.splits)
    obtain U where ft: "ho_typeof S G [] f=Some (HArrow U A)" and xt: "ho_typeof S G [] x=Some U"
      using Suc.prems(2) t by (auto split: option.splits ho_type.splits if_splits)
    show ?thesis unfolding t using source.candidate_application[OF Suc.IH[OF f ft] Suc.IH[OF x xt]] by simp
  next
    assume "ho_expansion_beta_branch S G obs ?rec t"
    then show ?thesis by (rule ho_expansion_beta_branch_sound[OF _ Suc.prems(2) subst Suc.IH])
  next
    assume "ho_expansion_definition_branch S G R rank defs obs ?rec t"
    then show ?thesis by (rule ho_expansion_definition_branch_sound[OF _ Suc.prems(2) subst Suc.IH])
  qed
qed

end
end
