theory Higher_Order_Descent_Check
  imports Higher_Order_Descent_Recursion
begin

fun ho_applied_prefixes where
  "ho_applied_prefixes (HApp f x) = (HApp f x,[]) # map (\<lambda>(v,xs). (v,xs@[x])) (ho_applied_prefixes f)"
| "ho_applied_prefixes t = [(t,[])]"

lemma ho_applied_prefixes_reconstruct:
  "(v,xs)\<in>set (ho_applied_prefixes t) \<Longrightarrow> t=ho_apply_terms v xs"
  by (induction t arbitrary: v xs) (auto simp: ho_apply_terms_fold foldl_append)

fun ho_bound_argument where
  "ho_bound_argument D A (HBound i) = (i<length D \<and> D!i=A)"
| "ho_bound_argument D A t = False"

definition ho_check_candidate_drop where
  "ho_check_candidate_drop S G sorts n D t u =
    (case ho_typeof S G [] u of Some (HBase b) \<Rightarrow>
      sorts b=n \<and> (case ho_application_head u of HConst c \<Rightarrow>
        list_ex (\<lambda>(v,xs). v\<in>set (ho_spine_arguments u) \<and>
          (case ho_typeof S G [] v of Some T \<Rightarrow>
             ho_positive_type sorts n T \<and> list_all2 (ho_bound_argument D) (ho_argument_types T) xs
           | None \<Rightarrow> False)) (ho_applied_prefixes t)
       | _ \<Rightarrow> False)
     | _ \<Rightarrow> False)"

fun ho_lex_checked where
  "ho_lex_checked rel [] ys=False"
| "ho_lex_checked rel (x#xs) []=False"
| "ho_lex_checked rel (x#xs) (y#ys)=(length xs=length ys \<and>
    ((x=y \<and> ho_lex_checked rel xs ys) \<or> rel x y))"

lemma ho_lex_checked_map:
  assumes check: "ho_lex_checked rel ys xs"
    and edge: "\<And>x y. x\<in>set xs \<Longrightarrow> rel y x \<Longrightarrow> (f y,f x)\<in>r"
  shows "(map f ys,map f xs)\<in>lex r"
  using check edge
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  obtain x zs where xs: "xs=x#zs" using Cons.prems(1) by (cases xs) auto
  have len: "length ys=length zs" using Cons.prems(1) xs by simp
  show ?case
  proof (cases "rel y x")
    case True
    have "(f y,f x)\<in>r" by (rule Cons.prems(2)[OF _ True]) (simp add: xs)
    then show ?thesis using len unfolding xs by simp
  next
    case False
    have eq: "y=x" and rest: "ho_lex_checked rel ys zs" using Cons.prems(1) xs False by auto
    have "(map f ys,map f zs)\<in>lex r"
      by (rule Cons.IH[OF rest]) (use Cons.prems(2) xs in auto)
    then show ?thesis using eq by (simp add: xs)
  qed
qed

context ho_source_accessible_reducibility
begin

theorem ho_check_candidate_drop_sound:
  assumes check: "ho_check_candidate_drop S G rank n D t u"
    and comp: "source_candidate Z (ho_subst s 0 u)"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>i. i<length D \<Longrightarrow> source_candidate (D!i) (b i)"
  shows "(ho_open s b 0 t,ho_subst s 0 u)\<in>candidate_terminating_descent n"
proof -
  obtain a c v xs T where ut: "ho_typeof S G [] u=Some (HBase a)"
    and level: "rank a=n" and head: "ho_application_head u=HConst c"
    and prefix: "(v,xs)\<in>set (ho_applied_prefixes t)"
    and member: "v\<in>set (ho_spine_arguments u)"
    and vt: "ho_typeof S G [] v=Some T"
    and pos: "ho_positive_type rank n T"
    and args: "list_all2 (ho_bound_argument D) (ho_argument_types T) xs"
    using check unfolding ho_check_candidate_drop_def
    by (auto simp: list_ex_iff split: option.splits ho_type.splits ho_term.splits)
  have iu: "ho_typeof S V B (ho_subst s 0 u)=Some (HBase a)"
    using ho_typeof_free_subst_context[OF ut subst] by simp
  have iv: "ho_typeof S V B (ho_subst s 0 v)=Some T"
    using ho_typeof_free_subst_context[OF vt subst] by simp
  have av: "(T,ho_subst s 0 v)\<in>ho_accessible_arguments rank S V B (ho_subst s 0 u)"
    using member pos level ho_constant_head_substitution[OF head, of s 0]
      ho_constant_arguments_subst[OF head, of s 0]
    by (simp add: ho_accessible_arguments_def iu iv)
  let ?I = "access.candidate_slice n (access.candidate_lower n) (access.candidate_level n (access.candidate_lower n))"
  have bases: "\<And>A j. A\<in>set (ho_argument_types T) \<Longrightarrow> j\<in>ho_type_bases A \<Longrightarrow> rank j\<le>n"
    using ho_polarity_bases[of rank n T] pos
    by (induction T) auto
  have ca: "list_all2 (source.candidate_computable ?I) (ho_argument_types T) (map (ho_open s b 0) xs)"
  proof -
    have each: "source.candidate_computable ?I A (ho_open s b 0 x)"
      if at: "A\<in>set (ho_argument_types T)" and ba: "ho_bound_argument D A x" for A x
    proof -
      obtain i where x: "x=HBound i" and i: "i<length D" and ty: "D!i=A"
        using ba by (cases x) auto
      have cb: "source_candidate A (b i)" using env[OF i] ty by simp
      show ?thesis using source_candidate_slice[where T=A and t="b i", OF bases[OF at]] cb x by simp
    qed
    show ?thesis
    proof (rule list_all2_all_nthI)
      show "length (ho_argument_types T)=length (map (ho_open s b 0) xs)"
        using list_all2_lengthD[OF args] by simp
      fix i assume i: "i<length (ho_argument_types T)"
      have il: "i<length xs" using i list_all2_lengthD[OF args] by simp
      show "source.candidate_computable ?I (ho_argument_types T!i) (map (ho_open s b 0) xs!i)"
        using each[OF nth_mem[OF i] list_all2_nthD[OF args i]] il by simp
    qed
  qed
  have vc: "ho_bound_closed 0 v" using ho_typeof_bound_closed[OF vt] by simp
  have opened: "ho_open s b 0 t=ho_apply_terms (ho_subst s 0 v) (map (ho_open s b 0) xs)"
    using ho_open_apply_terms[of s b 0 v xs] ho_applied_prefixes_reconstruct[OF prefix]
      ho_open_closed[OF vc, of s b] by simp
  have step: "access.accessible_step n ?I (ho_subst s 0 u) (ho_open s b 0 t)"
    unfolding access.accessible_step_def
    using iu level av ca opened by (auto simp: ho_apply_terms_fold)
  show ?thesis using candidate_descent_SN[OF comp, of n] step
    by (simp add: candidate_terminating_descent_def candidate_descent_def)
qed

theorem checked_accessible_call_order:
  assumes check: "ho_lex_checked (ho_check_candidate_drop S G rank n D)
      (ho_priority_arguments priority ys) (ho_priority_arguments priority xs)"
    and known: "\<And>x. x\<in>set xs \<Longrightarrow> \<exists>T. source_candidate T (ho_subst s 0 x)"
    and closed: "\<And>x. x\<in>set xs \<Longrightarrow> ho_bound_closed 0 x"
    and subst: "ho_typed_subst S V B G s"
    and env: "\<And>i. i<length D \<Longrightarrow> source_candidate (D!i) (b i)"
    and prec: "prec d=prec c"
  shows "((d,map (ho_open s b 0) ys),(c,map (ho_subst s 0) xs))\<in>accessible_call_order n prec priority"
proof -
  have edge: "(ho_open s b 0 y,ho_open s b 0 x)\<in>(candidate_terminating_descent n)\<^sup>+"
    if member: "x\<in>set (ho_priority_arguments priority xs)"
      and ck: "ho_check_candidate_drop S G rank n D y x" for x y
  proof -
    have xm: "x\<in>set xs" using member by simp
    obtain T where cx: "source_candidate T (ho_subst s 0 x)" using known[OF xm] by blast
    have "(ho_open s b 0 y,ho_subst s 0 x)\<in>candidate_terminating_descent n"
      by (rule ho_check_candidate_drop_sound[OF ck cx subst env])
    then show ?thesis using ho_open_closed[OF closed[OF xm], of s b] by (auto intro: r_into_trancl)
  qed
  have order: "(map (ho_open s b 0) (ho_priority_arguments priority ys),
      map (ho_open s b 0) (ho_priority_arguments priority xs))\<in>lex ((candidate_terminating_descent n)\<^sup>+)"
    by (rule ho_lex_checked_map[OF check edge])
  have unchanged: "map (ho_open s b 0) xs=map (ho_subst s 0) xs"
    by (rule map_cong) (simp, rule ho_open_closed[OF closed], assumption)
  have ordered: "(ho_priority_arguments priority (map (ho_open s b 0) ys),
      ho_priority_arguments priority (map (ho_subst s 0) xs))\<in>lex ((candidate_terminating_descent n)\<^sup>+)"
    using order by (simp only: ho_priority_arguments_map[symmetric] unchanged)
  show ?thesis using ordered prec
    by (simp add: accessible_call_order_def inv_image_def lex_prod_def)
qed

end

end
