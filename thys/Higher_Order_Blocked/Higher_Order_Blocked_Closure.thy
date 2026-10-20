theory Higher_Order_Blocked_Closure
  imports Higher_Order_Blocked_Calls
begin

lemma lambda_blocked_open:
  assumes block: "ho_lambda_blocked R c xs"
  shows "ho_lambda_blocked R c (map (ho_open s b 0) xs)"
proof -
  have abs: "ho_is_abstraction (ho_open s b 0 x)" if "ho_is_abstraction x" for x
    using that by (cases x) auto
  have clash: "ho_lambda_clash (map (ho_open s b 0) xs) ls"
    if input_clash: "ho_lambda_clash xs ls" for ls
  proof -
    obtain i where i: "i<length xs" "i<length ls" and a: "ho_is_abstraction (xs!i)"
      and h: "\<exists>d. ho_application_head (ls!i)=HConst d"
      using input_clash unfolding ho_lambda_clash_def by blast
    show ?thesis unfolding ho_lambda_clash_def
      by (rule exI[of _ i]) (use i h abs[OF a] in simp)
  qed
  show ?thesis using block
    unfolding ho_lambda_blocked_def list_all_iff by (auto intro: clash)
qed

primrec ho_check_blocked_closure where
  "ho_check_blocked_closure S G R sorts prec priority arity c ls 0 D t=False"
| "ho_check_blocked_closure S G R sorts prec priority arity c ls (Suc fuel) D t=
    (ho_check_functional_access_closure S G R sorts prec priority arity c ls (Suc fuel) D t \<or>
    (case ho_typeof S G D t of None \<Rightarrow> False | Some A \<Rightarrow>
      (case t of
        HApp f x \<Rightarrow>
          ho_check_blocked_closure S G R sorts prec priority arity c ls fuel D f \<and>
          ho_check_blocked_closure S G R sorts prec priority arity c ls fuel D x
      | HAbs T u \<Rightarrow>
          ho_check_blocked_closure S G R sorts prec priority arity c ls fuel (T#D) u
      | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T)
            (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lambda_blocked R d (ho_spine_arguments t) \<and>
          list_all (ho_check_blocked_closure S G R sorts prec priority arity c ls fuel D)
            (ho_spine_arguments t))
      | _ \<Rightarrow> False)))"

context ho_source_accessible_reducibility
begin

theorem ho_check_blocked_closure_sound:
  assumes check: "ho_check_blocked_closure S G R rank prec priority arity c ls fuel D t"
    and ty: "ho_typeof S G D t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>n. n<length D \<Longrightarrow> source_candidate (D!n) (b n)"
    and closed: "\<And>l. l\<in>set ls \<Longrightarrow> ho_bound_closed 0 l"
    and binders: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source_candidate T x"
    and bounds: "\<And>d U. ho_lookup S d=Some U \<Longrightarrow> arity d\<le>length (ho_argument_types U)"
    and lhs_typed: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. ho_typeof S G [] l=Some T"
    and lhs_inhabited: "\<And>l T. l\<in>set ls \<Longrightarrow> T\<in>ho_binder_types l \<Longrightarrow> \<exists>x. source_candidate T x"
    and known: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. source_candidate T (ho_subst s 0 l)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source_candidate (HBase b) x"
    and smaller: "\<And>d ys U. ((d,ys),(c,map (ho_subst s 0) ls))\<in>priority_call_order prec priority \<Longrightarrow>
      ho_lookup S d=Some U \<Longrightarrow> list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
      source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
    and arities: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity d"
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
  let ?old = "ho_check_functional_access_closure S G R rank prec priority arity c ls (Suc fuel) D t"
  let ?check = "ho_check_blocked_closure S G R rank prec priority arity c ls fuel"
  show ?case
  proof (cases ?old)
    case True
    show ?thesis
      by (rule ho_check_functional_access_closure_sound[OF True Suc.prems(2) subst
        Suc.prems(3) closed Suc.prems(4) bounds lhs_typed lhs_inhabited known inhabited smaller])
  next
    case False
    have choices:
      "(case t of HApp f x \<Rightarrow> ?check D f \<and> ?check D x
        | HAbs T u \<Rightarrow> ?check (T#D) u | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T)
            (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lambda_blocked R d (ho_spine_arguments t) \<and>
          list_all (?check D) (ho_spine_arguments t))
      | _ \<Rightarrow> False)"
      using Suc.prems(1) False
      by (simp only: ho_check_blocked_closure.simps Suc.prems(2) option.case) blast
    from choices show ?thesis
    proof
      assume simple: "(case t of HApp f x \<Rightarrow> ?check D f \<and> ?check D x
        | HAbs T u \<Rightarrow> ?check (T#D) u | _ \<Rightarrow> False)"
      show ?thesis
      proof (cases t)
        case (HApp f x)
        obtain T where ft: "ho_typeof S G D f=Some (HArrow T A)" and xt: "ho_typeof S G D x=Some T"
          using Suc.prems(2) HApp by (auto split: option.splits ho_type.splits if_splits)
        have cf: "source_candidate (HArrow T A) (ho_open s b 0 f)"
          by (rule Suc.IH[OF _ ft Suc.prems(3)]) (use simple HApp Suc.prems(4) in auto)
        have cx: "source_candidate T (ho_open s b 0 x)"
          by (rule Suc.IH[OF _ xt Suc.prems(3)]) (use simple HApp Suc.prems(4) in auto)
        show ?thesis using source.candidate_application[OF cf cx] HApp by simp
      next
        case (HAbs T u)
        obtain C where eq: "A=HArrow T C" and ut: "ho_typeof S G (T#D) u=Some C"
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
      assume call: "(case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T)
            (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lambda_blocked R d (ho_spine_arguments t) \<and>
          list_all (?check D) (ho_spine_arguments t))
      | _ \<Rightarrow> False)"
      then obtain d U where head: "ho_application_head t=HConst d" and ds: "ho_lookup S d=Some U"
        and eq: "A=ho_drop_type (arity d) U"
        and types: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T)
          (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
        and block: "ho_lambda_blocked R d (ho_spine_arguments t)"
        and checked: "list_all (?check D) (ho_spine_arguments t)"
        by (auto split: ho_term.splits option.splits)
      have typed_checked: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T \<and> ?check D x)
          (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
        using types checked by (induction rule: list_all2_induct) auto
      have bi: "\<And>x T. x\<in>set (ho_spine_arguments t) \<Longrightarrow>
          T\<in>ho_binder_types x \<Longrightarrow> \<exists>y. source_candidate T y"
        using Suc.prems(4) ho_spine_binder_types by blast
      have strengthened: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T \<and>
          ?check D x \<and> (\<forall>Z\<in>ho_binder_types x. \<exists>y. source_candidate Z y))
          (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
        using ho_list_all2_strengthen[OF typed_checked,
          of "\<lambda>x. \<forall>Z\<in>ho_binder_types x. \<exists>y. source_candidate Z y"] bi
        by (simp add: conj_assoc)
      have args: "list_all2 source_candidate (take (arity d) (ho_argument_types U))
          (map (ho_open s b 0) (ho_spine_arguments t))"
        using strengthened
        by (induction rule: list_all2_induct) (auto intro: Suc.IH[OF _ _ Suc.prems(3)])
      have ct: "source_candidate (ho_drop_type (arity d) U)
          (ho_apply_terms (HConst d) (map (ho_open s b 0) (ho_spine_arguments t)))"
        by (rule lambda_blocked_calls_computable[where arity=arity,
          OF arities bounds[OF ds] ds lambda_blocked_open[OF block] args])
      have rewrite: "ho_open s b 0 t=ho_apply_terms (HConst d) (map (ho_open s b 0) (ho_spine_arguments t))"
        using ho_open_apply_terms[of s b 0 "ho_application_head t" "ho_spine_arguments t"]
          ho_spine_reconstruct[of t] head by simp
      show ?thesis using ct eq rewrite by simp
    qed
  qed
qed

end

end
