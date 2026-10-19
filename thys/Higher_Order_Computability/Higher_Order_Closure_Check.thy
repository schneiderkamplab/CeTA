theory Higher_Order_Closure_Check
  imports Higher_Order_Syntactic_Descent
begin

fun ho_spine_arguments where
  "ho_spine_arguments (HApp f x)=ho_spine_arguments f@[x]"
| "ho_spine_arguments t=[]"

lemma ho_spine_reconstruct:
  "ho_apply_terms (ho_application_head t) (ho_spine_arguments t)=t"
  by (induction t) auto

lemma ho_spine_arguments_length [simp]: "length (ho_spine_arguments t)=ho_spine_length t"
  by (induction t) auto

lemma ho_subst_apply_terms:
  "ho_subst s d (ho_apply_terms f xs)=ho_apply_terms (ho_subst s d f) (map (ho_subst s d) xs)"
  by (induction xs arbitrary: f) auto

definition ho_closure_step where
  "ho_closure_step S G rank arity c ls recur t=(case ho_typeof S G [] t of None \<Rightarrow> False
    | Some A \<Rightarrow>
      t\<in>set ls \<or>
      (case A of HBase b \<Rightarrow> list_ex (ho_app_subterm t) ls | _ \<Rightarrow> False) \<or>
      (case t of HConst d \<Rightarrow> rank d<rank c
        | HApp f x \<Rightarrow> recur f \<and> recur x
        | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          rank d=rank c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lex_subterm (ho_spine_arguments t) ls \<and>
          list_all recur (ho_spine_arguments t))
      | _ \<Rightarrow> False))"

primrec ho_check_closure :: "ho_type list \<Rightarrow> ho_type list \<Rightarrow> (nat \<Rightarrow> nat)
    \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ho_term list \<Rightarrow> nat \<Rightarrow> ho_term \<Rightarrow> bool" where
  "ho_check_closure S G rank arity c ls 0 t=False"
| "ho_check_closure S G rank arity c ls (Suc fuel) t=
    ho_closure_step S G rank arity c ls (ho_check_closure S G rank arity c ls fuel) t"

context ho_source_neutral_reducibility
begin

lemma computable_retype:
  assumes comp: "source.computable T t" and ty: "ho_typeof S V B t=Some A"
  shows "source.computable A t"
proof -
  have "ho_typeof S V B t=Some T" by (rule source.computable_typed[OF comp])
  then have "T=A" using ty by simp
  then show ?thesis using comp by simp
qed

lemma lower_symbol_computable:
  assumes ds: "ho_lookup S d=Some U" and rank: "rank d<rank c"
    and bound: "arity d\<le>length (ho_argument_types U)"
    and inhabited: "\<And>b. b\<in>ho_type_bases U \<Longrightarrow> \<exists>x. source.computable (HBase b) x"
    and smaller: "\<And>e ys T. ((e,ys),(c,xs))\<in>call_order rank \<Longrightarrow> ho_lookup S e=Some T \<Longrightarrow>
      list_all2 source.computable (take (arity e) (ho_argument_types T)) ys \<Longrightarrow>
      source.computable (ho_drop_type (arity e) T) (ho_apply_terms (HConst e) ys)"
  shows "source.computable U (HConst d)"
proof (rule computable_from_prefix_calls)
  show "ho_typeof S V B (HConst d)=Some U" using ds by simp
  show "arity d\<le>length (ho_argument_types U)" by (rule bound)
  show "\<exists>x. source.computable (HBase b) x" if "b\<in>ho_type_bases U" for b
    by (rule inhabited[OF that])
  fix ys assume args: "list_all2 source.computable (take (arity d) (ho_argument_types U)) ys"
  have small: "((d,ys),(c,xs))\<in>call_order rank"
    using rank by (simp add: call_order_def inv_image_def lex_prod_def)
  show "source.computable (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
    by (rule smaller[OF small ds args])
qed

theorem ho_check_closure_sound:
  assumes check: "ho_check_closure S G rank arity c ls fuel t"
    and ty: "ho_typeof S G [] t=Some A"
    and subst: "ho_typed_subst S V B G s"
    and bounds: "\<And>d U. ho_lookup S d=Some U \<Longrightarrow> arity d\<le>length (ho_argument_types U)"
    and known: "\<And>l. l\<in>set ls \<Longrightarrow> \<exists>T. source.computable T (ho_subst s 0 l)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source.computable (HBase b) x"
    and smaller: "\<And>d ys U. ((d,ys),(c,map (ho_subst s 0) ls))\<in>call_order rank \<Longrightarrow>
      ho_lookup S d=Some U \<Longrightarrow> list_all2 source.computable (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
      source.computable (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
  shows "source.computable A (ho_subst s 0 t)"
  using check ty
proof (induction fuel arbitrary: t A)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  have it: "ho_typeof S V B (ho_subst s 0 t)=Some A"
    using ho_typeof_free_subst_context[OF Suc.prems(2) subst] by simp
  let ?check = "ho_check_closure S G rank arity c ls fuel"
  have choices: "t\<in>set ls \<or>
      (case A of HBase b \<Rightarrow> list_ex (ho_app_subterm t) ls | _ \<Rightarrow> False) \<or>
      (case t of HConst d \<Rightarrow> rank d<rank c | HApp f x \<Rightarrow> ?check f \<and> ?check x | _ \<Rightarrow> False) \<or>
      (case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          rank d=rank c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lex_subterm (ho_spine_arguments t) ls \<and> list_all ?check (ho_spine_arguments t))
       | _ \<Rightarrow> False)"
    using Suc.prems(1) by (simp only: ho_check_closure.simps ho_closure_step_def Suc.prems(2) option.case)
  from choices show ?case
  proof (elim disjE)
    assume "t\<in>set ls"
    then obtain T where "source.computable T (ho_subst s 0 t)" using known by blast
    then show ?thesis by (rule computable_retype[OF _ it])
  next
    assume base: "(case A of HBase b \<Rightarrow> list_ex (ho_app_subterm t) ls | _ \<Rightarrow> False)"
    then obtain b l where eq: "A=HBase b" and l: "l\<in>set ls" and sub: "ho_app_subterm t l"
      by (cases A) (auto simp: list_ex_iff)
    obtain T where cl: "source.computable T (ho_subst s 0 l)" using known[OF l] by blast
    have path: "ho_direct_application_subterm\<^sup>*\<^sup>* (ho_subst s 0 t) (ho_subst s 0 l)"
      by (rule ho_app_subterm_subst_path[OF sub])
    show ?thesis unfolding eq by (rule base_application_subterm_computable[OF cl path]) (use it eq in simp)
  next
    assume simple: "(case t of HConst d \<Rightarrow> rank d<rank c | HApp f x \<Rightarrow> ?check f \<and> ?check x | _ \<Rightarrow> False)"
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
      obtain T where ft: "ho_typeof S G [] f=Some (HArrow T A)" and xt: "ho_typeof S G [] x=Some T"
        using Suc.prems(2) HApp by (auto split: option.splits ho_type.splits if_splits)
      have cf: "source.computable (HArrow T A) (ho_subst s 0 f)"
        by (rule Suc.IH[OF _ ft]) (use simple HApp in simp)
      have cx: "source.computable T (ho_subst s 0 x)"
        by (rule Suc.IH[OF _ xt]) (use simple HApp in simp)
      show ?thesis using source.computable_application[OF cf cx] unfolding HApp by simp
    qed (use simple in auto)
  next
    assume recursive: "(case ho_application_head t of HConst d \<Rightarrow>
        (case ho_lookup S d of None \<Rightarrow> False | Some U \<Rightarrow>
          rank d=rank c \<and> A=ho_drop_type (arity d) U \<and>
          list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t) \<and>
          ho_lex_subterm (ho_spine_arguments t) ls \<and> list_all ?check (ho_spine_arguments t))
       | _ \<Rightarrow> False)"
    then obtain d U where head: "ho_application_head t=HConst d" and ds: "ho_lookup S d=Some U"
      and rank: "rank d=rank c" and eq: "A=ho_drop_type (arity d) U"
      and types: "list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T) (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
      and lex: "ho_lex_subterm (ho_spine_arguments t) ls"
      and checked: "list_all ?check (ho_spine_arguments t)"
      by (auto split: ho_term.splits option.splits)
    have typed_checked: "list_all2 (\<lambda>T x. ho_typeof S G [] x=Some T \<and> ?check x)
        (take (arity d) (ho_argument_types U)) (ho_spine_arguments t)"
      using types checked by (induction rule: list_all2_induct) auto
    have args: "list_all2 source.computable (take (arity d) (ho_argument_types U)) (map (ho_subst s 0) (ho_spine_arguments t))"
      using typed_checked by (induction rule: list_all2_induct) (auto intro: Suc.IH)
    have acc: "Wellfounded.accp application_descent (ho_subst s 0 l)" if "l\<in>set ls" for l
      using known[OF that] computable_application_descent by blast
    have small: "((d,map (ho_subst s 0) (ho_spine_arguments t)),(c,map (ho_subst s 0) ls))\<in>call_order rank"
      by (rule syntactic_lex_call_order[where s=s and rank=rank and c=c and d=d, OF lex acc rank])
    have ct: "source.computable (ho_drop_type (arity d) U)
      (ho_apply_terms (HConst d) (map (ho_subst s 0) (ho_spine_arguments t)))"
      by (rule smaller[OF small ds args])
    have rewrite: "ho_subst s 0 t=ho_apply_terms (HConst d) (map (ho_subst s 0) (ho_spine_arguments t))"
      using ho_subst_apply_terms[of s 0 "ho_application_head t" "ho_spine_arguments t"]
        ho_spine_reconstruct[of t] head by simp
    show ?thesis using ct eq rewrite by simp
  qed
qed

end

end
