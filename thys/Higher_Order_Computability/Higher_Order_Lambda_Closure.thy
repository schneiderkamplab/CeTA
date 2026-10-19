theory Higher_Order_Lambda_Closure
  imports Higher_Order_Closure_Check
begin

lemma ho_open_apply_terms:
  "ho_open s b d (ho_apply_terms f xs)=ho_apply_terms (ho_open s b d f) (map (ho_open s b d) xs)"
  by (induction xs arbitrary: f) auto

lemma ho_spine_binder_types:
  "x\<in>set (ho_spine_arguments t) \<Longrightarrow> ho_binder_types x\<subseteq>ho_binder_types t"
  by (induction t) auto

lemma ho_list_all2_strengthen:
  "list_all2 P xs ys \<Longrightarrow> (\<And>y. y\<in>set ys \<Longrightarrow> Q y) \<Longrightarrow>
   list_all2 (\<lambda>x y. P x y \<and> Q y) xs ys"
  by (induction rule: list_all2_induct) auto

definition ho_lambda_closure_step where
  "ho_lambda_closure_step S G rank arity c ls recur D t=(case ho_typeof S G D t of None \<Rightarrow> False
    | Some A \<Rightarrow>
      t\<in>set ls \<or>
      (case A of HBase b \<Rightarrow> list_ex (ho_app_subterm t) ls | _ \<Rightarrow> False) \<or>
      (case t of HConst d \<Rightarrow> rank d<rank c
        | HApp f x \<Rightarrow> recur D f \<and> recur D x
        | HBound n \<Rightarrow> n<length D
        | HAbs T u \<Rightarrow> recur (T#D) u
        | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          rank d=rank c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lex_subterm (ho_spine_arguments t) ls \<and>
          list_all (recur D) (ho_spine_arguments t))
      | _ \<Rightarrow> False))"

primrec ho_check_lambda_closure :: "ho_type list \<Rightarrow> ho_type list \<Rightarrow> (nat \<Rightarrow> nat)
    \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ho_term list \<Rightarrow> nat \<Rightarrow> ho_type list \<Rightarrow> ho_term \<Rightarrow> bool" where
  "ho_check_lambda_closure S G rank arity c ls 0 D t=False"
| "ho_check_lambda_closure S G rank arity c ls (Suc fuel) D t=
    ho_lambda_closure_step S G rank arity c ls (ho_check_lambda_closure S G rank arity c ls fuel) D t"


context ho_source_neutral_reducibility
begin

theorem ho_check_lambda_closure_sound:
  assumes check: "ho_check_lambda_closure S G rank arity c ls fuel D t"
    and ty: "ho_typeof S G D t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>n. n<length D \<Longrightarrow> source.computable (D!n) (b n)"
    and closed: "\<And>l. l\<in>set ls \<Longrightarrow> ho_bound_closed 0 l"
    and binders: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source.computable T x"
    and bounds: "\<And>d U. ho_lookup S d=Some U \<Longrightarrow> arity d\<le>length (ho_argument_types U)"
    and known: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. source.computable T (ho_subst s 0 l)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source.computable (HBase b) x"
    and smaller: "\<And>d ys U. ((d,ys),(c,map (ho_subst s 0) ls))\<in>call_order rank \<Longrightarrow>
      ho_lookup S d=Some U \<Longrightarrow> list_all2 source.computable (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
      source.computable (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
  shows "source.computable A (ho_open s b 0 t)"
  using check ty env binders
proof (induction fuel arbitrary: t A D b)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  have it: "ho_typeof S V B (ho_open s b 0 t)=Some A"
    by (rule ho_open_type[where D="[]", simplified, OF Suc.prems(2)])
      (use subst in \<open>auto simp: ho_typed_subst_def\<close>,
       rule source.computable_typed[OF Suc.prems(3)], assumption)
  have unchanged: "ho_open s b 0 l=ho_subst s 0 l" if "l\<in>set ls" for l
    by (rule ho_open_closed[OF closed[OF that]])
  let ?check = "ho_check_lambda_closure S G rank arity c ls fuel"
  have choices: "t\<in>set ls \<or>
      (case A of HBase j \<Rightarrow> list_ex (ho_app_subterm t) ls | _ \<Rightarrow> False) \<or>
      (case t of HConst d \<Rightarrow> rank d<rank c | HApp f x \<Rightarrow> ?check D f \<and> ?check D x | HBound n \<Rightarrow> n<length D | HAbs T u \<Rightarrow> ?check (T#D) u | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          rank d=rank c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lex_subterm (ho_spine_arguments t) ls \<and> list_all (?check D) (ho_spine_arguments t))
       | _ \<Rightarrow> False)"
    using Suc.prems(1) by (simp only: ho_check_lambda_closure.simps ho_lambda_closure_step_def Suc.prems(2) option.case)
  from choices show ?case
  proof (elim disjE)
    assume "t\<in>set ls"
    then obtain T where "source.computable T (ho_open s b 0 t)" using known unchanged by metis
    then show ?thesis by (rule computable_retype[OF _ it])
  next
    assume base: "(case A of HBase b \<Rightarrow> list_ex (ho_app_subterm t) ls | _ \<Rightarrow> False)"
    then obtain j l where eq: "A=HBase j" and l: "l\<in>set ls" and sub: "ho_app_subterm t l"
      by (cases A) (auto simp: list_ex_iff)
    obtain T where cl: "source.computable T (ho_open s b 0 l)" using known[OF l] unchanged[OF l] by metis
    have path: "ho_direct_application_subterm\<^sup>*\<^sup>* (ho_open s b 0 t) (ho_open s b 0 l)"
      by (rule ho_app_subterm_open_path[OF sub])
    show ?thesis unfolding eq by (rule base_application_subterm_computable[OF cl path]) (use it eq in simp)
  next
    assume simple: "(case t of HConst d \<Rightarrow> rank d<rank c | HApp f x \<Rightarrow> ?check D f \<and> ?check D x | HBound n \<Rightarrow> n<length D | HAbs T u \<Rightarrow> ?check (T#D) u | _ \<Rightarrow> False)"
    show ?thesis
    proof (cases t)
      case (HConst d)
      have ds: "ho_lookup S d=Some A" using Suc.prems(2) HConst by simp
      have rank: "rank d<rank c" using simple HConst by simp
      have "source.computable A (HConst d)"
        by (rule lower_symbol_computable[OF ds rank bounds[OF ds] inhabited[OF ds] smaller])
      then show ?thesis unfolding HConst by simp
    next
      case (HApp f x)
      obtain T where ft: "ho_typeof S G D f=Some (HArrow T A)" and xt: "ho_typeof S G D x=Some T"
        using Suc.prems(2) HApp by (auto split: option.splits ho_type.splits if_splits)
      have cf: "source.computable (HArrow T A) (ho_open s b 0 f)"
        by (rule Suc.IH[OF _ ft Suc.prems(3)]) (use simple HApp Suc.prems(4) in auto)
      have cx: "source.computable T (ho_open s b 0 x)"
        by (rule Suc.IH[OF _ xt Suc.prems(3)]) (use simple HApp Suc.prems(4) in auto)
      show ?thesis using source.computable_application[OF cf cx] unfolding HApp by simp
    next
      case (HBound n)
      have n: "n<length D" and eq: "D!n=A" using Suc.prems(2) HBound by (auto split: if_splits)
      show ?thesis using Suc.prems(3)[OF n] eq HBound by simp
    next
      case (HAbs T u)
      obtain C where ut: "ho_typeof S G (T#D) u=Some C" and eq: "A=HArrow T C"
        using Suc.prems(2) HAbs by (auto split: option.splits)
      obtain a where ca: "source.computable T a" using Suc.prems(4) HAbs by auto
      have ot: "ho_typeof S V B (HAbs T (ho_open s b 1 u))=Some (HArrow T C)"
        using it HAbs eq by simp
      have instances: "source.computable C (ho_beta_subst x 0 (ho_open s b 1 u))"
        if cx: "source.computable T x" for x
      proof -
        let ?b = "\<lambda>n. if n=0 then x else b (n-1)"
        have be: "source.computable ((T#D)!n) (?b n)" if "n<length (T#D)" for n
          using that cx Suc.prems(3) by (cases n) auto
        have "source.computable C (ho_open s ?b 0 u)"
          by (rule Suc.IH[OF _ ut be]) (use simple HAbs Suc.prems(4) in auto)
        then show ?thesis by (simp add: ho_open_beta)
      qed
      show ?thesis using source_computable_abstraction_from_instances[OF ot ca instances] eq HAbs by simp
    qed (use simple in auto)
  next
    assume recursive: "(case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          rank d=rank c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lex_subterm (ho_spine_arguments t) ls \<and> list_all (?check D) (ho_spine_arguments t))
       | _ \<Rightarrow> False)"
    then obtain d U where head: "ho_application_head t=HConst d" and ds: "ho_lookup S d=Some U"
      and rank: "rank d=rank c" and eq: "A=ho_drop_type (arity d) U"
      and types: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
      and lex: "ho_lex_subterm (ho_spine_arguments t) ls"
      and checked: "list_all (?check D) (ho_spine_arguments t)"
      by (auto split: ho_term.splits option.splits)
    have typed_checked: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T \<and> ?check D x)
        (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
      using types checked by (induction rule: list_all2_induct) auto
    have args: "list_all2 source.computable (take (arity d) (ho_argument_types U)) (map (ho_open s b 0) (ho_spine_arguments t))"
      proof -
      have bi: "\<And>x T. x\<in>set (ho_spine_arguments t) \<Longrightarrow> T\<in>ho_binder_types x \<Longrightarrow> \<exists>y. source.computable T y"
        using Suc.prems(4) ho_spine_binder_types by blast
      have strengthened: "list_all2 (\<lambda>T x. ho_typeof S G D x=Some T \<and>
          ?check D x \<and> (\<forall>Z\<in>ho_binder_types x. \<exists>y. source.computable Z y))
          (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
        using ho_list_all2_strengthen[OF typed_checked, of "\<lambda>x. \<forall>Z\<in>ho_binder_types x. \<exists>y. source.computable Z y"] bi
        by (simp add: conj_assoc)
      show ?thesis using strengthened
        by (induction rule: list_all2_induct) (auto intro: Suc.IH[OF _ _ Suc.prems(3)])
    qed
    have acc: "Wellfounded.accp application_descent (ho_open s b 0 l)" if "l\<in>set ls" for l
      using known[OF that] unchanged[OF that] computable_application_descent by metis
    have small: "((d,map (ho_open s b 0) (ho_spine_arguments t)),(c,map (ho_subst s 0) ls))\<in>call_order rank"
      proof -
      have "((d,map (ho_open s b 0) (ho_spine_arguments t)),(c,map (ho_open s b 0) ls))\<in>call_order rank"
        by (rule syntactic_lex_open_call_order[where s=s and b=b and rank=rank and c=c and d=d, OF lex acc rank])
      then show ?thesis using unchanged by (simp cong: map_cong)
    qed
    have ct: "source.computable (ho_drop_type (arity d) U)
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
