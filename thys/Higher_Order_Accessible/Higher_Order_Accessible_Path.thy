theory Higher_Order_Accessible_Path
  imports Higher_Order_Candidate_Recursion
begin

lemma ho_constant_arguments_subst:
  "ho_application_head t=HConst c \<Longrightarrow>
   ho_spine_arguments (ho_subst s d t)=map (ho_subst s d) (ho_spine_arguments t)"
  by (induction t) auto

primrec ho_check_accessible_path where
  "ho_check_accessible_path S G rank 0 t u = (t=u)"
| "ho_check_accessible_path S G rank (Suc fuel) t u = (t=u \<or>
    (case ho_typeof S G [] u of Some (HBase b) \<Rightarrow>
      (case ho_application_head u of HConst c \<Rightarrow>
        list_ex (\<lambda>v. case ho_typeof S G [] v of None \<Rightarrow> False | Some T \<Rightarrow>
          ho_positive_type rank (rank b) T \<and> ho_check_accessible_path S G rank fuel t v)
          (ho_spine_arguments u)
        | _ \<Rightarrow> False)
      | _ \<Rightarrow> False))"

context ho_source_accessible_reducibility
begin

theorem ho_check_accessible_path_sound:
  assumes check: "ho_check_accessible_path S G rank fuel t u"
    and ty: "ho_typeof S G [] u=Some U"
    and comp: "source_candidate Z (ho_subst s 0 u)"
    and subst: "ho_typed_subst S V B G s"
  shows "\<exists>A. ho_typeof S G [] t=Some A \<and> source_candidate A (ho_subst s 0 t)"
  using check ty comp
proof (induction fuel arbitrary: u U Z)
  case 0
  have eq: "t=u" using 0(1) by simp
  have it: "ho_typeof S V B (ho_subst s 0 u)=Some U"
    using ho_typeof_free_subst_context[OF 0(2) subst] by simp
  show ?case using 0(2) source_candidate_retype[OF 0(3) it] eq by blast
next
  case (Suc fuel)
  show ?case
  proof (cases "t=u")
    case True
    have it: "ho_typeof S V B (ho_subst s 0 u)=Some U"
      using ho_typeof_free_subst_context[OF Suc.prems(2) subst] by simp
    show ?thesis using Suc.prems(2) source_candidate_retype[OF Suc.prems(3) it] True by blast
  next
    case False
    obtain b c v T where ut: "ho_typeof S G [] u=Some (HBase b)"
      and head: "ho_application_head u=HConst c"
      and member: "v\<in>set (ho_spine_arguments u)"
      and vt: "ho_typeof S G [] v=Some T"
      and pos: "ho_positive_type rank (rank b) T"
      and rec: "ho_check_accessible_path S G rank fuel t v"
      using Suc.prems(1) False by (auto simp: list_ex_iff split: option.splits ho_type.splits ho_term.splits)
    have iu: "ho_typeof S V B (ho_subst s 0 u)=Some (HBase b)"
      using ho_typeof_free_subst_context[OF ut subst] by simp
    have iv: "ho_typeof S V B (ho_subst s 0 v)=Some T"
      using ho_typeof_free_subst_context[OF vt subst] by simp
    have cu: "source_candidate (HBase b) (ho_subst s 0 u)"
      by (rule source_candidate_retype[OF Suc.prems(3) iu])
    have av: "(T,ho_subst s 0 v)\<in>ho_accessible_arguments rank S V B (ho_subst s 0 u)"
      using member pos ho_constant_head_substitution[OF head, of s 0]
        ho_constant_arguments_subst[OF head, of s 0]
      by (simp add: ho_accessible_arguments_def iu iv)
    have cv: "source_candidate T (ho_subst s 0 v)" by (rule source_candidate_accessible[OF cu av])
    show ?thesis by (rule Suc.IH[OF rec vt cv])
  qed
qed

end

end
