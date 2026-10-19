theory Higher_Order_Lex_Closure
  imports Higher_Order_Lex_Order
begin

definition ho_lex_semantic_closure_step where
  "ho_lex_semantic_closure_step S G sorts orders ofuel prec priority arity c ls recur D t=(case ho_typeof S G D t of None \<Rightarrow> False
    | Some A \<Rightarrow>
      t\<in>set ls \<or>
      list_ex (ho_accessible_from S G sorts t) ls \<or>
      (case t of HConst d \<Rightarrow> (prec d::nat)<prec c
        | HApp f x \<Rightarrow> recur D f \<and> recur D x
        | HBound n \<Rightarrow> n<length D
        | HAbs T u \<Rightarrow> recur (T#D) u
        | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          prec d=prec c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          (D=[] \<and> (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) True \<or>
            (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) False \<and>
             ho_lex_subterm (ho_priority_arguments priority (ho_spine_arguments t)) (ho_priority_arguments priority ls)))) \<and>
          list_all (recur D) (ho_spine_arguments t))
      | _ \<Rightarrow> False))"

primrec ho_check_lex_semantic_closure where
  "ho_check_lex_semantic_closure S G sorts orders ofuel prec priority arity c ls 0 D t=False"
| "ho_check_lex_semantic_closure S G sorts orders ofuel prec priority arity c ls (Suc fuel) D t=
    ho_lex_semantic_closure_step S G sorts orders ofuel prec priority arity c ls (ho_check_lex_semantic_closure S G sorts orders ofuel prec priority arity c ls fuel) D t"


context ho_source_accessible_reducibility
begin

lemma lower_lex_semantic_symbol_computable:
  assumes ds: "ho_lookup S d=Some U" and prec: "prec d<prec c"
    and bound: "arity d\<le>length (ho_argument_types U)"
    and inhabited: "\<And>b. b\<in>ho_type_bases U \<Longrightarrow> \<exists>x. source_candidate (HBase b) x"
    and smaller: "\<And>e ys T. ((e,ys),(c,xs))\<in>lex_semantic_call_order prec weight priority \<Longrightarrow> ho_lookup S e=Some T \<Longrightarrow>
      list_all2 source_candidate (take (arity e) (ho_argument_types T)) ys \<Longrightarrow>
      source_candidate (ho_drop_type (arity e) T) (ho_apply_terms (HConst e) ys)"
  shows "source_candidate U (HConst d)"
proof (rule candidate_from_prefix_calls)
  show "ho_typeof S V B (HConst d)=Some U" using ds by simp
  show "arity d\<le>length (ho_argument_types U)" by (rule bound)
  show "\<exists>x. source_candidate (HBase b) x" if "b\<in>ho_type_bases U" for b
    by (rule inhabited[OF that])
  fix ys assume args: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys"
  have small: "((d,ys),(c,xs))\<in>lex_semantic_call_order prec weight priority"
    using prec by (simp add: lex_semantic_call_order_def inv_image_def lex_prod_def)
  show "source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
    by (rule smaller[OF small ds args])
qed

theorem ho_check_lex_semantic_closure_sound:
  assumes valid: "ho_lex_signatures S orders"
    and ev: "ho_env_value (B@V) e"
    and weight_eq: "weight=ho_lex_weights S V B orders e"
    and check: "ho_check_lex_semantic_closure S G rank orders ofuel prec priority arity c ls fuel D t"
    and ty: "ho_typeof S G D t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>n. n<length D \<Longrightarrow> source_candidate (D!n) (b n)"
    and closed: "\<And>l. l\<in>set ls \<Longrightarrow> ho_bound_closed 0 l"
    and binders: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source_candidate T x"
    and bounds: "\<And>d U. ho_lookup S d=Some U \<Longrightarrow> arity d\<le>length (ho_argument_types U)"
    and lhs_typed: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. ho_typeof S G [] l=Some T"
    and known: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. source_candidate T (ho_subst s 0 l)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source_candidate (HBase b) x"
    and smaller: "\<And>d ys U. ((d,ys),(c,map (ho_subst s 0) ls))\<in>lex_semantic_call_order prec weight priority \<Longrightarrow>
      ho_lookup S d=Some U \<Longrightarrow> list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
      source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
  shows "source_candidate A (ho_open s b 0 t)"
  using check ty env binders
proof (induction fuel arbitrary: t A D b)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  have it: "ho_typeof S V B (ho_open s b 0 t)=Some A"
    by (rule ho_open_type[where D="[]", simplified, OF Suc.prems(2)])
      (use subst in \<open>auto simp: ho_typed_subst_def\<close>,
       rule source.candidate_typed[OF Suc.prems(3)], assumption)
  have unchanged: "ho_open s b 0 l=ho_subst s 0 l" if "l\<in>set ls" for l
    by (rule ho_open_closed[OF closed[OF that]])
  let ?check = "ho_check_lex_semantic_closure S G rank orders ofuel prec priority arity c ls fuel"
  have choices: "t\<in>set ls \<or>
      list_ex (ho_accessible_from S G rank t) ls \<or>
      (case t of HConst d \<Rightarrow> prec d<prec c | HApp f x \<Rightarrow> ?check D f \<and> ?check D x | HBound n \<Rightarrow> n<length D | HAbs T u \<Rightarrow> ?check (T#D) u | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          prec d=prec c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          (D=[] \<and> (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) True \<or>
            (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) False \<and>
             ho_lex_subterm (ho_priority_arguments priority (ho_spine_arguments t)) (ho_priority_arguments priority ls)))) \<and> list_all (?check D) (ho_spine_arguments t))
       | _ \<Rightarrow> False)"
    using Suc.prems(1) by (simp only: ho_check_lex_semantic_closure.simps ho_lex_semantic_closure_step_def Suc.prems(2) option.case)
  from choices show ?case
  proof (elim disjE)
    assume "t\<in>set ls"
    then obtain T where "source_candidate T (ho_open s b 0 t)" using known unchanged by metis
    then show ?thesis by (rule source_candidate_retype[OF _ it])
  next
    assume base: "list_ex (ho_accessible_from S G rank t) ls"
    then obtain l where member: "l\<in>set ls" and path: "ho_accessible_from S G rank t l"
      by (auto simp: list_ex_iff)
    obtain U where lt: "ho_typeof S G [] l=Some U" using lhs_typed[OF member] by blast
    obtain Z where cl: "source_candidate Z (ho_subst s 0 l)" using known[OF member] by blast
    obtain T where tt: "ho_typeof S G [] t=Some T" and ct: "source_candidate T (ho_subst s 0 t)"
      using ho_check_accessible_path_sound[OF _ lt cl subst] path
      unfolding ho_accessible_from_def by blast
    have tc: "ho_bound_closed 0 t" using ho_typeof_bound_closed[OF tt] by simp
    have eq: "ho_open s b 0 t=ho_subst s 0 t" by (rule ho_open_closed[OF tc])
    show ?thesis using source_candidate_retype[OF ct] it eq by simp
  next
    assume simple: "(case t of HConst d \<Rightarrow> prec d<prec c | HApp f x \<Rightarrow> ?check D f \<and> ?check D x | HBound n \<Rightarrow> n<length D | HAbs T u \<Rightarrow> ?check (T#D) u | _ \<Rightarrow> False)"
    show ?thesis
    proof (cases t)
      case (HConst d)
      have ds: "ho_lookup S d=Some A" using Suc.prems(2) HConst by simp
      have prec: "prec d<prec c" using simple HConst by simp
      have "source_candidate A (HConst d)"
        by (rule lower_lex_semantic_symbol_computable[OF ds prec bounds[OF ds] inhabited[OF ds] smaller])
      then show ?thesis unfolding HConst by simp
    next
      case (HApp f x)
      obtain T where ft: "ho_typeof S G D f=Some (HArrow T A)" and xt: "ho_typeof S G D x=Some T"
        using Suc.prems(2) HApp by (auto split: option.splits ho_type.splits if_splits)
      have cf: "source_candidate (HArrow T A) (ho_open s b 0 f)"
        by (rule Suc.IH[OF _ ft Suc.prems(3)]) (use simple HApp Suc.prems(4) in auto)
      have cx: "source_candidate T (ho_open s b 0 x)"
        by (rule Suc.IH[OF _ xt Suc.prems(3)]) (use simple HApp Suc.prems(4) in auto)
      show ?thesis using source.candidate_application[OF cf cx] unfolding HApp by simp
    next
      case (HBound n)
      have n: "n<length D" and eq: "D!n=A" using Suc.prems(2) HBound by (auto split: if_splits)
      show ?thesis using Suc.prems(3)[OF n] eq HBound by simp
    next
      case (HAbs T u)
      obtain C where ut: "ho_typeof S G (T#D) u=Some C" and eq: "A=HArrow T C"
        using Suc.prems(2) HAbs by (auto split: option.splits)
      obtain a where ca: "source_candidate T a" using Suc.prems(4) HAbs by auto
      have ot: "ho_typeof S V B (HAbs T (ho_open s b 1 u))=Some (HArrow T C)"
        using it HAbs eq by simp
      have instances: "source_candidate C (ho_beta_subst x 0 (ho_open s b 1 u))"
        if cx: "source_candidate T x" for x
      proof -
        let ?b = "\<lambda>n. if n=0 then x else b (n-1)"
        have be: "source_candidate ((T#D)!n) (?b n)" if "n<length (T#D)" for n
          using that cx Suc.prems(3) by (cases n) auto
        have "source_candidate C (ho_open s ?b 0 u)"
          by (rule Suc.IH[OF _ ut be]) (use simple HAbs Suc.prems(4) in auto)
        then show ?thesis by (simp add: ho_open_beta)
      qed
      show ?thesis using source_candidate_abstraction_from_instances[OF ot ca instances] eq HAbs by simp
    qed (use simple in auto)
  next
    assume recursive: "(case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          prec d=prec c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          (D=[] \<and> (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) True \<or>
            (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) False \<and>
             ho_lex_subterm (ho_priority_arguments priority (ho_spine_arguments t)) (ho_priority_arguments priority ls)))) \<and> list_all (?check D) (ho_spine_arguments t))
       | _ \<Rightarrow> False)"
    then obtain d U where head: "ho_application_head t=HConst d" and ds: "ho_lookup S d=Some U"
      and prec: "prec d=prec c" and eq: "A=ho_drop_type (arity d) U"
      and types: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
      and comparison: "(D=[] \<and> (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) True \<or>
            (ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) False \<and>
             ho_lex_subterm (ho_priority_arguments priority (ho_spine_arguments t)) (ho_priority_arguments priority ls))))"
      and checked: "list_all (?check D) (ho_spine_arguments t)"
      by (auto split: ho_term.splits option.splits)
    have typed_checked: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T \<and> ?check D x)
        (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
      using types checked by (induction rule: list_all2_induct) auto
    have args: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) (map (ho_open s b 0) (ho_spine_arguments t))"
      proof -
      have bi: "\<And>x T. x\<in>set (ho_spine_arguments t) \<Longrightarrow> T\<in>ho_binder_types x \<Longrightarrow> \<exists>y. source_candidate T y"
        using Suc.prems(4) ho_spine_binder_types by blast
      have strengthened: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T \<and>
          ?check D x \<and> (\<forall>Z\<in>ho_binder_types x. \<exists>y. source_candidate Z y))
          (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
        using ho_list_all2_strengthen[OF typed_checked, of "\<lambda>x. \<forall>Z\<in>ho_binder_types x. \<exists>y. source_candidate Z y"] bi
        by (simp add: conj_assoc)
      show ?thesis using strengthened
        by (induction rule: list_all2_induct) (auto intro: Suc.IH[OF _ _ Suc.prems(3)])
    qed
    have acc: "Wellfounded.accp application_descent (ho_open s b 0 l)" if "l\<in>set ls" for l
      proof -
      note member = that
      obtain T where ct: "source_candidate T (ho_subst s 0 l)" using known[OF member] by blast
      have sn: "source.strongly_normalizing (ho_open s b 0 l)"
        using source.candidate_SN[OF ct] unchanged[OF member] by simp
      show ?thesis by (rule source_SN_application_descent[OF sn])
    qed
    have small: "((d,map (ho_open s b 0) (ho_spine_arguments t)),(c,map (ho_subst s 0) ls))\<in>lex_semantic_call_order prec weight priority"
    proof (cases "ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) True")
      case True
      have strict: "(weight d (map (ho_open s b 0) (ho_spine_arguments t)),weight c (map (ho_subst s 0) ls))\<in>lex less_than"
        using ho_check_lex_comparison_sound[where b=b, OF valid True subst ev] weight_eq by simp
      show ?thesis by (rule lex_semantic_strict_call_order[OF prec strict])
    next
      case False
      have weak: "ho_check_lex_comparison S orders ofuel G c ls d (ho_spine_arguments t) False"
        and lex: "ho_lex_subterm (ho_priority_arguments priority (ho_spine_arguments t)) (ho_priority_arguments priority ls)"
        using comparison False by auto
      have le: "ho_nat_lex_weak (weight d (map (ho_open s b 0) (ho_spine_arguments t))) (weight c (map (ho_open s b 0) ls))"
        using ho_check_lex_comparison_sound[where b=b, OF valid weak subst ev] weight_eq unchanged
        by (simp cong: map_cong)
      have order: "((d,map (ho_open s b 0) (ho_spine_arguments t)),(c,map (ho_open s b 0) ls))\<in>lex_semantic_call_order prec weight priority"
        by (rule lex_semantic_syntactic_call_order[where s=s and b=b and prec=prec and c=c and d=d,
          OF lex acc prec le])
      show ?thesis using order unchanged by (simp cong: map_cong)
    qed
    have ct: "source_candidate (ho_drop_type (arity d) U)
      (ho_apply_terms (HConst d) (map (ho_open s b 0) (ho_spine_arguments t)))"
      by (rule smaller[OF small ds args])
    have rewrite: "ho_open s b 0 t=ho_apply_terms (HConst d) (map (ho_open s b 0) (ho_spine_arguments t))"
      using ho_open_apply_terms[of s b 0 "ho_application_head t" "ho_spine_arguments t"]
        ho_spine_reconstruct[of t] head by simp
    show ?thesis using ct eq rewrite by simp
  qed
qed

end

end
