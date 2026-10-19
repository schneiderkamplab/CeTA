theory Higher_Order_Lambda_Access_Path
  imports "Higher_Order_Semantic_Calls.Higher_Order_Semantic_Schema"
begin

lemma ho_constant_head_open:
  "ho_application_head t=HConst c \<Longrightarrow> ho_application_head (ho_open s b d t)=HConst c"
  by (induction t) auto

lemma ho_constant_arguments_open:
  "ho_application_head t=HConst c \<Longrightarrow>
    ho_spine_arguments (ho_open s b d t)=map (ho_open s b d) (ho_spine_arguments t)"
  by (induction t) auto

primrec ho_check_lambda_access_path where
  "ho_check_lambda_access_path S G sorts 0 D t u=(t=u)"
| "ho_check_lambda_access_path S G sorts (Suc fuel) D t u = (t=u \<or>
    (case u of HAbs A v \<Rightarrow> ho_check_lambda_access_path S G sorts fuel (A#D) t v
     | _ \<Rightarrow> (case ho_typeof S G D u of Some (HBase b) \<Rightarrow>
       (case ho_application_head u of HConst c \<Rightarrow>
         list_ex (\<lambda>v. case ho_typeof S G D v of None \<Rightarrow> False | Some T \<Rightarrow>
           ho_positive_type sorts (sorts b) T \<and> ho_check_lambda_access_path S G sorts fuel D t v)
           (ho_spine_arguments u)
        | _ \<Rightarrow> False)
      | _ \<Rightarrow> False)))"

context ho_source_accessible_reducibility
begin

theorem ho_check_lambda_access_path_sound:
  assumes check: "ho_check_lambda_access_path S G rank fuel D t u"
    and target: "ho_typeof S G [] t=Some A"
    and ty: "ho_typeof S G D u=Some U"
    and comp: "source_candidate Z (ho_open s b 0 u)"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>i. i<length D \<Longrightarrow> source_candidate (D!i) (b i)"
    and inhabited: "\<And>T. T\<in>ho_binder_types u \<Longrightarrow> \<exists>x. source_candidate T x"
  shows "source_candidate A (ho_subst s 0 t)"
proof -
  have closed: "ho_bound_closed 0 t" using ho_typeof_bound_closed[OF target] by simp
  have target_open: "ho_open s b 0 t=ho_subst s 0 t" for b by (rule ho_open_closed[OF closed])
  have it: "ho_typeof S V B (ho_subst s 0 t)=Some A"
    using ho_typeof_free_subst_context[OF target subst] by simp
  show ?thesis using check ty comp env inhabited
  proof (induction fuel arbitrary: D u U Z b)
    case 0
    have "t=u" using 0(1) by simp
    then show ?case using source_candidate_retype[OF 0(3)] it target_open by simp
  next
    case (Suc fuel)
    show ?case
    proof (cases "t=u")
      case True
      then show ?thesis using source_candidate_retype[OF Suc.prems(3)] it target_open by simp
    next
      case False
      have iu: "ho_typeof S V B (ho_open s b 0 u)=Some U"
        by (rule ho_open_type[where D="[]", simplified, OF Suc.prems(2)])
          (use subst in \<open>auto simp: ho_typed_subst_def\<close>, rule source.candidate_typed[OF Suc.prems(4)], assumption)
      show ?thesis
      proof (cases u)
        case (HAbs T v)
        obtain C where vt: "ho_typeof S G (T#D) v=Some C" and uc: "U=HArrow T C"
          using Suc.prems(2) HAbs by (auto split: option.splits)
        obtain x where cx: "source_candidate T x" using Suc.prems(5)[of T] HAbs by auto
        have cu: "source_candidate (HArrow T C) (ho_open s b 0 u)"
          using source_candidate_retype[OF Suc.prems(3) iu] uc by simp
        have applied: "source_candidate C (HApp (ho_open s b 0 u) x)"
          by (rule source.candidate_application[OF cu cx])
        let ?b = "\<lambda>i. if i=0 then x else b (i-1)"
        have applied_abs: "source_candidate C (HApp (HAbs T (ho_open s b 1 v)) x)"
          using applied HAbs by simp
        have reduct: "source_candidate C (ho_open s ?b 0 v)"
          using source_candidate_reduction[OF applied_abs ho_step.beta]
          by (simp add: ho_open_beta)
        have be: "source_candidate ((T#D)!i) (?b i)" if "i<length (T#D)" for i
          using that cx Suc.prems(4) by (cases i) auto
        have rec: "ho_check_lambda_access_path S G rank fuel (T#D) t v"
          using Suc.prems(1) False HAbs by simp
        have inh: "\<exists>x. source_candidate Z x" if "Z\<in>ho_binder_types v" for Z
          using Suc.prems(5) HAbs that by auto
        show ?thesis by (rule Suc.IH[OF rec vt reduct be inh])
      next
        case (HBound i)
        then show ?thesis using Suc.prems(1) False by (auto split: option.splits ho_type.splits)
      next
        case (HFree i)
        then show ?thesis using Suc.prems(1) False by (auto split: option.splits ho_type.splits)
      next
        case (HConst c)
        then show ?thesis using Suc.prems(1) False by (auto split: option.splits ho_type.splits)
      next
        case (HApp f x)
        obtain a c v T where ut: "ho_typeof S G D u=Some (HBase a)"
          and head: "ho_application_head u=HConst c"
          and member: "v\<in>set (ho_spine_arguments u)"
          and vt: "ho_typeof S G D v=Some T"
          and pos: "ho_positive_type rank (rank a) T"
          and rec: "ho_check_lambda_access_path S G rank fuel D t v"
          using Suc.prems(1) False HApp
          by (auto simp: list_ex_iff split: option.splits ho_type.splits ho_term.splits if_splits; blast)
        have iut: "ho_typeof S V B (ho_open s b 0 u)=Some (HBase a)" using ut Suc.prems(2) iu by simp
        have iv: "ho_typeof S V B (ho_open s b 0 v)=Some T"
          by (rule ho_open_type[where D="[]", simplified, OF vt])
            (use subst in \<open>auto simp: ho_typed_subst_def\<close>, rule source.candidate_typed[OF Suc.prems(4)], assumption)
        have cu: "source_candidate (HBase a) (ho_open s b 0 u)"
          by (rule source_candidate_retype[OF Suc.prems(3) iut])
        have av: "(T,ho_open s b 0 v)\<in>ho_accessible_arguments rank S V B (ho_open s b 0 u)"
          using member pos ho_constant_head_open[OF head, of s b 0] ho_constant_arguments_open[OF head, of s b 0]
          by (simp add: ho_accessible_arguments_def iut iv)
        have cv: "source_candidate T (ho_open s b 0 v)" by (rule source_candidate_accessible[OF cu av])
        have inh: "\<exists>x. source_candidate Z x" if "Z\<in>ho_binder_types v" for Z
          using Suc.prems(5) ho_spine_binder_types[OF member] that by blast
        show ?thesis by (rule Suc.IH[OF rec vt cv Suc.prems(4) inh])
      qed
    qed
  qed
qed

end

end
