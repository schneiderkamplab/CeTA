theory Higher_Order_Functional_Access_Path
  imports "Higher_Order_Component_Order.Higher_Order_Component_Schema"
begin

lemma ho_open_insert_lift:
  "ho_open s (\<lambda>n. if n=0 then x else b (n-1)) d (ho_lift 1 d t)=ho_open s b d t"
  by (induction t arbitrary: d; auto; arith)

definition ho_application_unwrap where
  "ho_application_unwrap S G R D u=(case u of HApp (HApp (HConst c) f) x \<Rightarrow>
    (case ho_typeof S G D f of Some (HArrow A C) \<Rightarrow>
      if ho_typeof S G D x=Some A \<and> ho_lookup S c=Some (HArrow (HArrow A C) (HArrow A C)) \<and>
        ho_application_rule A C c\<in>set R then Some (HApp f x) else None
     | _ \<Rightarrow> None) | _ \<Rightarrow> None)"

lemma ho_application_rule_step:
  assumes member: "ho_application_rule A C c\<in>set R"
    and sy: "ho_lookup S c=Some (HArrow (HArrow A C) (HArrow A C))"
    and ft: "ho_typeof S V B f=Some (HArrow A C)" and xt: "ho_typeof S V B x=Some A"
  shows "ho_step S V R B (HApp (HApp (HConst c) f) x) (HApp f x)"
proof -
  let ?l = "PApp (PApp (PConst c) (PMeta 0 [])) (PMeta 1 [])"
  let ?r = "PApp (PMeta 0 []) (PMeta 1 [])"
  let ?s = "\<lambda>n. if n=0 then f else x"
  have mem: "([HArrow A C,A],?l,?r)\<in>set R" using member by (simp add: ho_application_rule_def)
  have wt: "ho_rule_welltyped S ([HArrow A C,A],?l,?r)"
    using sy by (simp add: ho_rule_welltyped_def)
  have sub: "ho_typed_subst S V B [HArrow A C,A] ?s"
    using ft xt by (auto simp: ho_typed_subst_def nth_Cons split: nat.splits)
  show ?thesis by (rule ho_step.rule[OF mem wt sub]) (simp_all add: ho_lift_0)
qed

lemma ho_application_unwrap_open:
  assumes unwrap: "ho_application_unwrap S G R D u=Some v"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>i. i<length D \<Longrightarrow> ho_typeof S V B (b i)=Some (D!i)"
  shows "ho_step S V R B (ho_open s b 0 u) (ho_open s b 0 v)"
proof -
  obtain c f x A C where u: "u=HApp (HApp (HConst c) f) x" and v: "v=HApp f x"
    and ft: "ho_typeof S G D f=Some (HArrow A C)" and xt: "ho_typeof S G D x=Some A"
    and sy: "ho_lookup S c=Some (HArrow (HArrow A C) (HArrow A C))"
    and member: "ho_application_rule A C c\<in>set R"
    using unwrap by (auto simp: ho_application_unwrap_def split: ho_term.splits option.splits ho_type.splits if_splits)
  have it: "ho_typeof S V B (ho_open s b 0 t)=Some T" if "ho_typeof S G D t=Some T" for t T
    by (rule ho_open_type[where D="[]", simplified, OF that])
      (use subst in \<open>auto simp: ho_typed_subst_def\<close>, rule env, assumption)
  show ?thesis using ho_application_rule_step[OF member sy it[OF ft] it[OF xt]] u v by simp
qed

lemma ho_application_unwrap_type:
  "ho_application_unwrap S G R D u=Some v \<Longrightarrow> ho_typeof S G D u=Some U \<Longrightarrow> ho_typeof S G D v=Some U"
  by (auto simp: ho_application_unwrap_def split: ho_term.splits option.splits ho_type.splits if_splits)

lemma ho_application_unwrap_binders:
  "ho_application_unwrap S G R D u=Some v \<Longrightarrow> ho_binder_types v\<subseteq>ho_binder_types u"
  by (auto simp: ho_application_unwrap_def split: ho_term.splits option.splits ho_type.splits if_splits)

primrec ho_check_functional_access_path where
  "ho_check_functional_access_path S G R sorts 0 D t u=(t=u)"
| "ho_check_functional_access_path S G R sorts (Suc fuel) D t u=(t=u \<or>
    (case u of HAbs A v \<Rightarrow>
       ho_check_functional_access_path S G R sorts fuel (A#D) (ho_lift 1 0 t) v \<or>
       (case ho_typeof S G D t of Some (HArrow T C) \<Rightarrow> T=A \<and>
         ho_check_functional_access_path S G R sorts fuel (A#D) (HApp (ho_lift 1 0 t) (HBound 0)) v | _ \<Rightarrow> False)
     | _ \<Rightarrow> (case ho_application_unwrap S G R D u of Some v \<Rightarrow>
       ho_check_functional_access_path S G R sorts fuel D t v
       | None \<Rightarrow> (case ho_typeof S G D u of Some (HBase a) \<Rightarrow>
         (case ho_application_head u of HConst c \<Rightarrow>
           list_ex (\<lambda>v. case ho_typeof S G D v of None \<Rightarrow> False | Some T \<Rightarrow>
             ho_positive_type sorts (sorts a) T \<and> ho_check_functional_access_path S G R sorts fuel D t v)
             (ho_spine_arguments u) | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))))"

context ho_source_accessible_reducibility
begin

theorem ho_check_functional_access_path_sound:
  assumes check: "ho_check_functional_access_path S G R rank fuel D t u"
    and target: "ho_typeof S G D t=Some A" and ty: "ho_typeof S G D u=Some U"
    and comp: "source_candidate Z (ho_open s b 0 u)"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>i. i<length D \<Longrightarrow> source_candidate (D!i) (b i)"
    and inhabited: "\<And>T. T\<in>ho_binder_types u \<Longrightarrow> \<exists>x. source_candidate T x"
  shows "source_candidate A (ho_open s b 0 t)"
  using check target ty comp env inhabited
proof (induction fuel arbitrary: D t u A U Z b)
  case 0
  have eq: "t=u" using 0(1) by simp
  have it: "ho_typeof S V B (ho_open s b 0 t)=Some A"
    by (rule ho_open_type[where D="[]", simplified, OF 0(2)])
      (use subst in \<open>auto simp: ho_typed_subst_def\<close>, rule source.candidate_typed[OF 0(5)], assumption)
  show ?case using source_candidate_retype[OF 0(4) it[unfolded eq]] eq by simp
next
  case (Suc fuel)
  have opened: "ho_typeof S V B (ho_open s b 0 q)=Some T" if "ho_typeof S G D q=Some T" for q T
    by (rule ho_open_type[where D="[]", simplified, OF that])
      (use subst in \<open>auto simp: ho_typed_subst_def\<close>, rule source.candidate_typed[OF Suc.prems(5)], assumption)
  show ?case
  proof (cases "t=u")
    case True
    show ?thesis using source_candidate_retype[OF Suc.prems(4) opened[OF Suc.prems(2), unfolded True]] True by simp
  next
    case False
    show ?thesis
    proof (cases u)
      case (HAbs T v)
      obtain C where vt: "ho_typeof S G (T#D) v=Some C" and uc: "U=HArrow T C"
        using Suc.prems(3) HAbs by (auto split: option.splits)
      obtain a where ca: "source_candidate T a" using Suc.prems(6)[of T] HAbs by auto
      have cu: "source_candidate (HArrow T C) (ho_open s b 0 u)"
        using source_candidate_retype[OF Suc.prems(4) opened[OF Suc.prems(3)]] uc by simp
      have be: "source_candidate ((T#D)!i) ((\<lambda>n. if n=0 then x else b(n-1)) i)"
        if cx: "source_candidate T x" and i: "i<length (T#D)" for x i
        using cx i Suc.prems(5) by (cases i) auto
      have body: "source_candidate C (ho_open s (\<lambda>n. if n=0 then x else b(n-1)) 0 v)"
        if cx: "source_candidate T x" for x
      proof -
        have app: "source_candidate C (HApp (HAbs T (ho_open s b 1 v)) x)"
          using source.candidate_application[OF cu cx] HAbs by simp
        show ?thesis using source_candidate_reduction[OF app ho_step.beta] by (simp add: ho_open_beta)
      qed
      have inh: "\<exists>x. source_candidate W x" if "W\<in>ho_binder_types v" for W
        using Suc.prems(6) HAbs that by auto
      have lifted: "ho_typeof S G (T#D) (ho_lift 1 0 t)=Some A"
        using ho_typeof_lift_context[where B="[]" and D="[T]", simplified, OF Suc.prems(2)] by simp
      have choices: "ho_check_functional_access_path S G R rank fuel (T#D) (ho_lift 1 0 t) v \<or>
        (\<exists>E. A=HArrow T E \<and> ho_check_functional_access_path S G R rank fuel (T#D) (HApp (ho_lift 1 0 t) (HBound 0)) v)"
        using Suc.prems(1) False HAbs Suc.prems(2) by (auto split: ho_type.splits)
      from choices show ?thesis
      proof
        assume direct: "ho_check_functional_access_path S G R rank fuel (T#D) (ho_lift 1 0 t) v"
        have "source_candidate A (ho_open s (\<lambda>n. if n=0 then a else b(n-1)) 0 (ho_lift 1 0 t))"
          by (rule Suc.IH[OF direct lifted vt body[OF ca] be[OF ca] inh])
        then show ?thesis by (simp only: ho_open_insert_lift)
      next
        assume "\<exists>E. A=HArrow T E \<and> ho_check_functional_access_path S G R rank fuel (T#D) (HApp (ho_lift 1 0 t) (HBound 0)) v"
        then obtain E where ae: "A=HArrow T E" and path: "ho_check_functional_access_path S G R rank fuel (T#D) (HApp (ho_lift 1 0 t) (HBound 0)) v" by blast
        have app_ty: "ho_typeof S G (T#D) (HApp (ho_lift 1 0 t) (HBound 0))=Some E" using lifted ae by simp
        have app: "source_candidate E (HApp (ho_open s b 0 t) x)" if cx: "source_candidate T x" for x
          using Suc.IH[OF path app_ty vt body[OF cx] be[OF cx] inh]
          by (simp only: ho_open.simps ho_open_insert_lift; simp)
        have sn: "source.strongly_normalizing (ho_open s b 0 t)"
          by (rule source_SN_function[OF source.candidate_SN[OF app[OF ca]]])
        show ?thesis using opened[OF Suc.prems(2)] sn app ae by simp
      qed
    next
      case (HApp f x)
      show ?thesis
      proof (cases "ho_application_unwrap S G R D u")
        case (Some v)
        have rec: "ho_check_functional_access_path S G R rank fuel D t v" using Suc.prems(1) False HApp Some by simp
        have vt: "ho_typeof S G D v=Some U" by (rule ho_application_unwrap_type[OF Some Suc.prems(3)])
        have step: "ho_step S V R B (ho_open s b 0 u) (ho_open s b 0 v)"
          by (rule ho_application_unwrap_open[OF Some subst]) (rule source.candidate_typed[OF Suc.prems(5)], assumption)
        have cv: "source_candidate Z (ho_open s b 0 v)" by (rule source_candidate_reduction[OF Suc.prems(4) step])
        have inh: "\<exists>x. source_candidate T x" if "T\<in>ho_binder_types v" for T
          using ho_application_unwrap_binders[OF Some] Suc.prems(6) that by blast
        show ?thesis by (rule Suc.IH[OF rec Suc.prems(2) vt cv Suc.prems(5) inh])
      next
        case None
        obtain a c v T where ut: "ho_typeof S G D u=Some (HBase a)"
          and head: "ho_application_head u=HConst c" and member: "v\<in>set (ho_spine_arguments u)"
          and vt: "ho_typeof S G D v=Some T" and pos: "ho_positive_type rank (rank a) T"
          and rec: "ho_check_functional_access_path S G R rank fuel D t v"
          using Suc.prems(1) False HApp None
          by (auto simp: list_ex_iff split: option.splits ho_type.splits ho_term.splits if_splits; blast)
        have cu: "source_candidate (HBase a) (ho_open s b 0 u)" by (rule source_candidate_retype[OF Suc.prems(4) opened[OF ut]])
        have av: "(T,ho_open s b 0 v)\<in>ho_accessible_arguments rank S V B (ho_open s b 0 u)"
          using member pos ho_constant_head_open[OF head, of s b 0] ho_constant_arguments_open[OF head, of s b 0]
          by (simp add: ho_accessible_arguments_def opened[OF ut] opened[OF vt])
        have cv: "source_candidate T (ho_open s b 0 v)" by (rule source_candidate_accessible[OF cu av])
        have inh: "\<exists>x. source_candidate W x" if "W\<in>ho_binder_types v" for W
          using Suc.prems(6) ho_spine_binder_types[OF member] that by blast
        show ?thesis by (rule Suc.IH[OF rec Suc.prems(2) vt cv Suc.prems(5) inh])
      qed
    qed (use Suc.prems(1) False in \<open>auto simp: ho_application_unwrap_def split: option.splits ho_type.splits\<close>)
  qed
qed

end
end
