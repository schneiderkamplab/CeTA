(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Guarded_List_Checker
  imports
    CSR_Guarded_List_Generic_Checker
    CSR_Checker_Extensions.CSR_Conservative_Checker
begin

datatype ('f,'v) csr_guarded_ovcons_witness =
  CSR_Guarded_OvCons_Witness
    'f 'f 'f 'f 'f 'f 'f 'f 'f 'f 'f 'f 'f 'f 'f
    'v 'v 'v 'v 'v 'v 'v 'v

fun check_csr_guarded_ovcons_terminal ::
  "('dpp, ('f::{showl,compare_order}, label_type) lab, string) dpp_ops \<Rightarrow>
   ((('f,label_type) lab) muL) \<Rightarrow> 'dpp \<Rightarrow>
   ((('f,label_type) lab),string) csr_guarded_ovcons_witness \<Rightarrow>
   showsl check"
where
  "check_csr_guarded_ovcons_terminal J \<mu> dpp
      (CSR_Guarded_OvCons_Witness
        tt a natp listp ilistp u11 u21 u31 z su len ni co ta zs
        X L IL M N V V1 V2) = debug id (STR ''guarded-list CSR component'') (do {
    check (plain_csr_dpp J dpp)
      (showsl_lit (STR ''guarded component is not a plain CSR-DP problem''));
    check (distinct
      [tt,a,natp,listp,ilistp,u11,u21,u31,z,su,len,ni,co,ta,zs])
      (showsl_lit (STR ''guarded component symbols are not distinct''));
    check (Sharp u11 \<notin> set [a,u11,u21,u31] \<and>
      Sharp len \<notin> set [a,u11,u21,u31] \<and> Sharp u11 \<noteq> Sharp len)
      (showsl_lit (STR ''guarded component marked symbols are not fresh''));
    check (csr_guard_rules_check tt a natp listp ilistp u11 u21 u31
      z su len ni co ta zs (dpp_ops.rules J dpp))
      (showsl_lit (STR ''guarded residual violates semantic-rank obligations''));
    check (set (dpp_ops.pairs J dpp) = {
      csr_guard_strict_pair (Sharp len) co (Sharp u11) a listp natp N L,
      csr_guard_weak_pair (Sharp u11) tt (Sharp len) L})
      (showsl_lit (STR ''guarded component does not contain the exact two pairs''));
    check_wf_trs (dpp_ops.rules J dpp);
    check (list_all (\<lambda>(f,n). case f of Sharp _ \<Rightarrow> False | _ \<Rightarrow> True)
      (defined_list (dpp_ops.rules J dpp)))
      (showsl_lit (STR ''guarded residual defines a reserved marked symbol''));
    check (1 \<notin> mu_of \<mu> (u11,2))
      (showsl_lit (STR ''guarded continuation tail is not frozen''));
    check (mu_of \<mu> (a,2) \<subseteq> {0} \<and>
      mu_of \<mu> (natp,1) = {} \<and>
      mu_of \<mu> (listp,1) = {} \<and>
      mu_of \<mu> (ilistp,1) = {})
      (showsl_lit (STR ''guard recognizer replacement map is invalid''))
  })"

lemma check_csr_guarded_ovcons_terminal_sound:
  assumes J: "dpp_spec J"
    and ok: "isOK (check_csr_guarded_ovcons_terminal J \<mu> dpp witness)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof (cases witness)
  case (CSR_Guarded_OvCons_Witness
      tt a natp listp ilistp u11 u21 u31 z su len ni co ta zs
      X L IL M N V V1 V2)
  from ok CSR_Guarded_OvCons_Witness have plain: "plain_csr_dpp J dpp"
    and symbols: "distinct
      [tt,a,natp,listp,ilistp,u11,u21,u31,z,su,len,ni,co,ta,zs]"
    and marked_u11: "Sharp u11 \<notin> set [a,u11,u21,u31]"
    and marked_len: "Sharp len \<notin> set [a,u11,u21,u31]"
    and wrappers: "Sharp u11 \<noteq> Sharp len"
    and rules_checked: "csr_guard_rules_check tt a natp listp ilistp
      u11 u21 u31 z su len ni co ta zs (dpp_ops.rules J dpp)"
    and pairs: "set (dpp_ops.pairs J dpp) = {
      csr_guard_strict_pair (Sharp len) co (Sharp u11) a listp natp N L,
      csr_guard_weak_pair (Sharp u11) tt (Sharp len) L}"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and no_sharp: "list_all
      (\<lambda>(f,n). case f of Sharp _ \<Rightarrow> False | _ \<Rightarrow> True)
      (defined_list (dpp_ops.rules J dpp))"
    and frozen: "1 \<notin> mu_of \<mu> (u11,2)"
    and mu_and: "mu_of \<mu> (a,2) \<subseteq> {0}"
    and mu_nat: "mu_of \<mu> (natp,1) = {}"
    and mu_list: "mu_of \<mu> (listp,1) = {}"
    and mu_ilist: "mu_of \<mu> (ilistp,1) = {}"
    by (auto simp: isOK_check list_all_iff)
  have fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
  proof -
    fix f n
    show "\<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
      using no_sharp
      by (auto simp: list_all_iff)
  qed
  have arity_two: "(2::nat) = Suc (Suc 0)"
    by (simp add: numeral_2_eq_2)
  have frozen': "1 \<notin> mu_of \<mu> (u11,Suc (Suc 0))"
    using frozen unfolding arity_two[symmetric] .
  from csr_guard_rules_check_sound[OF rules_checked symbols]
  have truth_checked: "csr_guard_truth_rules_backward
      tt a natp listp ilistp z su len ni co ta zs
      (set (dpp_ops.rules J dpp))"
    and normal_checked: "csr_guard_normal_rules_backward_eq
      a u11 u21 u31 z su len ni co ta zs
      (set (dpp_ops.rules J dpp))"
    by auto
  have names: "distinct [tt,a,natp,listp,ilistp]" using symbols by simp
  have guard_checked: "csr_guard_successful_tests
      tt a natp listp ilistp z su len ni co ta zs (mu_of \<mu>)
      (set (dpp_ops.rules J dpp))"
    by (rule csr_guard_successful_tests_active[
        OF names mu_and mu_nat mu_list mu_ilist truth_checked])
  show ?thesis
    apply (rule finite_min_csr_dpp_guarded_two_pair[
        where R = "set (dpp_ops.rules J dpp)" and
          P = "set (dpp_ops.pairs J dpp)" and \<mu> = "mu_of \<mu>"])
                apply (rule symbols)
               apply (rule marked_u11)
              apply (rule marked_len)
             apply (rule wrappers)
            apply (rule pairs)
           apply (rule wf)
          apply (rule fresh)
         apply (rule frozen')
        apply (rule guard_checked)
       apply (rule normal_checked)
    done
qed

datatype (dead 'f, dead 'l, dead 'v) guarded_csr_dp_proof =
    Guarded_CSR_DP_Existing "('f,'l,'v) csr_dp_termination_proof"
  | Guarded_CSR_DP_Dep_Graph
      "((('f,'l,'v) guarded_csr_dp_proof option \<times> ('f,'l,'v) trsLL) list)"
  | Guarded_CSR_DP_OvCons
      "((('f,'l) lab),'v) csr_guarded_ovcons_witness"

fun check_guarded_csr_dp_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   ((('f,label_type) lab) muL) \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) guarded_csr_dp_proof \<Rightarrow> showsl check"
and check_guarded_csr_dp_components ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   ((('f,label_type) lab) muL) \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ((('f,label_type,string) guarded_csr_dp_proof option \<times>
      ('f,label_type,string) trsLL) list) \<Rightarrow> showsl check"
where
  "check_guarded_csr_dp_proof I J \<mu> i dpp (Guarded_CSR_DP_Existing prf) =
    check_csr_dp_termination_proof_min I J \<mu> False i dpp prf"
| "check_guarded_csr_dp_proof I J \<mu> i dpp (Guarded_CSR_DP_Dep_Graph edpts) =
    debug i (STR ''guarded CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts;
      check_guarded_csr_dp_components I J \<mu> i dpp edpts
    })"
| "check_guarded_csr_dp_proof I J \<mu> i dpp (Guarded_CSR_DP_OvCons witness) =
    check_csr_guarded_ovcons_terminal J \<mu> dpp witness"
| "check_guarded_csr_dp_components I J \<mu> i dpp [] = succeed"
| "check_guarded_csr_dp_components I J \<mu> i dpp ((None,P) # rest) =
    check_guarded_csr_dp_components I J \<mu> (add_index i 1) dpp rest"
| "check_guarded_csr_dp_components I J \<mu> i dpp ((Some prf,P) # rest) = do {
    check_guarded_csr_dp_proof I J \<mu> (add_index i 1)
      (dpp_ops.intersect_pairs J dpp P) prf;
    check_guarded_csr_dp_components I J \<mu> (add_index i 1) dpp rest
  }"

lemma check_guarded_csr_dp_components_member:
  assumes ok: "isOK (check_guarded_csr_dp_components I J \<mu> i dpp edpts)"
    and mem: "(Some prf,P) \<in> set edpts"
  shows "\<exists>j. isOK (check_guarded_csr_dp_proof I J \<mu> j
    (dpp_ops.intersect_pairs J dpp P) prf)"
  using ok mem
proof (induction edpts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain po C where x: "x = (po,C)" by (cases x)
  show ?case
  proof (cases po)
    case None
    with Cons x show ?thesis by auto
  next
    case (Some p)
    show ?thesis
    proof (cases "p = prf \<and> C = P")
      case True
      with Cons.prems Some x show ?thesis by auto
    next
      case False
      with Cons Some x show ?thesis by auto
    qed
  qed
qed

lemma check_guarded_csr_dp_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_guarded_csr_dp_proof I J \<mu> i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using plain wf fresh ok
proof (induction "prf" arbitrary: dpp i)
  case (Guarded_CSR_DP_Existing p)
  from Guarded_CSR_DP_Existing.prems(4) have rec:
      "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp p)"
    by simp
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
      OF I J Guarded_CSR_DP_Existing.prems(1-3) rec])
next
  case (Guarded_CSR_DP_Dep_Graph edpts)
  from Guarded_CSR_DP_Dep_Graph.prems(4) have graph_ok:
      "isOK (check_csr_dep_graph_proc J \<mu> dpp edpts)"
    and components_ok:
      "isOK (check_guarded_csr_dp_components I J \<mu> i dpp edpts)"
    by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_min_sound[
      OF J Guarded_CSR_DP_Dep_Graph.prems(1) graph_ok])
    fix p C
    assume mem: "(Some p,C) \<in> set edpts"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_guarded_csr_dp_components_member[OF components_ok mem]
    obtain j where rec: "isOK (check_guarded_csr_dp_proof I J \<mu> j ?d p)"
      by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
          OF J Guarded_CSR_DP_Dep_Graph.prems(1)])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d =
      (NFS dpp, M dpp, set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C, set (Q dpp), set (R dpp), set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J ?d =
      (NFS ?d, M ?d, set (P ?d), set (Pw ?d),
        set (Q ?d), set (R ?d), set (Rw ?d))"
      by (rule dpp_sound)
    have pairs': "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules': "set (rules ?d) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of ?d] by auto
    have wf': "wf_trs (set (rules ?d))"
      using Guarded_CSR_DP_Dep_Graph.prems(2) unfolding rules' .
    have fresh': "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
      using Guarded_CSR_DP_Dep_Graph.prems(3) unfolding rules' .
    have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
      apply (rule Guarded_CSR_DP_Dep_Graph.IH[
          where xa = "(Some p,C)" and xaa = "Some p" and xaaa = p])
            apply (rule mem)
           apply simp
          apply simp
         apply (rule plain')
        apply (rule wf')
       apply (rule fresh')
      apply (rule rec)
      done
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) \<inter> set C) (set (rules dpp))"
      using fin unfolding pairs' rules' .
  qed
next
  case (Guarded_CSR_DP_OvCons witness)
  from Guarded_CSR_DP_OvCons.prems(4) have terminal:
      "isOK (check_csr_guarded_ovcons_terminal J \<mu> dpp witness)"
    by simp
  show ?case by (rule check_csr_guarded_ovcons_terminal_sound[
      OF J terminal])
qed

fun check_guarded_improved_csr_dp_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) \<Rightarrow> ((('f,label_type) lab) muL) \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) guarded_csr_dp_proof \<Rightarrow> showsl check"
and check_guarded_improved_csr_dp_components ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) \<Rightarrow> ((('f,label_type) lab) muL) \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ((('f,label_type,string) guarded_csr_dp_proof option \<times>
      ('f,label_type,string) trsLL) list) \<Rightarrow> showsl check"
where
  "check_guarded_improved_csr_dp_proof I J U \<mu> i dpp
      (Guarded_CSR_DP_Existing prf) =
    check_improved_csr_dp_termination_proof I J U \<mu> False i dpp prf"
| "check_guarded_improved_csr_dp_proof I J U \<mu> i dpp
      (Guarded_CSR_DP_Dep_Graph edpts) =
    debug i (STR ''guarded improved CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts;
      check_guarded_improved_csr_dp_components I J U \<mu> i dpp edpts
    })"
| "check_guarded_improved_csr_dp_proof I J U \<mu> i dpp
      (Guarded_CSR_DP_OvCons witness) =
    check_csr_guarded_ovcons_terminal J \<mu> dpp witness"
| "check_guarded_improved_csr_dp_components I J U \<mu> i dpp [] = succeed"
| "check_guarded_improved_csr_dp_components I J U \<mu> i dpp
      ((None,P) # rest) =
    check_guarded_improved_csr_dp_components I J U \<mu>
      (add_index i 1) dpp rest"
| "check_guarded_improved_csr_dp_components I J U \<mu> i dpp
      ((Some prf,P) # rest) = do {
    check_guarded_improved_csr_dp_proof I J U \<mu> (add_index i 1)
      (dpp_ops.intersect_pairs J dpp P) prf;
    check_guarded_improved_csr_dp_components I J U \<mu>
      (add_index i 1) dpp rest
  }"

lemma check_guarded_improved_csr_dp_components_member:
  assumes ok: "isOK (check_guarded_improved_csr_dp_components
      I J U \<mu> i dpp edpts)"
    and mem: "(Some prf,P) \<in> set edpts"
  shows "\<exists>j. isOK (check_guarded_improved_csr_dp_proof I J U \<mu> j
    (dpp_ops.intersect_pairs J dpp P) prf)"
  using ok mem
proof (induction edpts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain po C where x: "x = (po,C)" by (cases x)
  show ?case
  proof (cases po)
    case None
    with Cons x show ?thesis by auto
  next
    case (Some p)
    show ?thesis
    proof (cases "p = prf \<and> C = P")
      case True
      with Cons.prems Some x show ?thesis by auto
    next
      case False
      with Cons Some x show ?thesis by auto
    qed
  qed
qed

lemma check_guarded_improved_csr_dp_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh_sharp: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fresh_U: "\<And>n.
      \<not> defined (set (dpp_ops.rules J dpp)) (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and ok: "isOK (check_guarded_improved_csr_dp_proof
      I J U \<mu> i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using plain wf fresh_sharp fresh_U ok
proof (induction "prf" arbitrary: dpp i)
  case (Guarded_CSR_DP_Existing p)
  from Guarded_CSR_DP_Existing.prems(5) have rec:
      "isOK (check_improved_csr_dp_termination_proof
        I J U \<mu> False i dpp p)"
    by simp
  show ?case by (rule check_improved_csr_dp_termination_proof_sound[
      OF I J Guarded_CSR_DP_Existing.prems(1-4) unsharp rec])
next
  case (Guarded_CSR_DP_Dep_Graph edpts)
  from Guarded_CSR_DP_Dep_Graph.prems(5) have graph_ok:
      "isOK (check_csr_dep_graph_proc J \<mu> dpp edpts)"
    and components_ok:
      "isOK (check_guarded_improved_csr_dp_components
        I J U \<mu> i dpp edpts)"
    by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_min_sound[
      OF J Guarded_CSR_DP_Dep_Graph.prems(1) graph_ok])
    fix p C
    assume mem: "(Some p,C) \<in> set edpts"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_guarded_improved_csr_dp_components_member[
        OF components_ok mem]
    obtain j where rec: "isOK (check_guarded_improved_csr_dp_proof
      I J U \<mu> j ?d p)"
      by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
          OF J Guarded_CSR_DP_Dep_Graph.prems(1)])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d =
      (NFS dpp, M dpp, set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C, set (Q dpp), set (R dpp), set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J ?d =
      (NFS ?d, M ?d, set (P ?d), set (Pw ?d),
        set (Q ?d), set (R ?d), set (Rw ?d))"
      by (rule dpp_sound)
    have pairs': "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules': "set (rules ?d) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of ?d] by auto
    have wf': "wf_trs (set (rules ?d))"
      using Guarded_CSR_DP_Dep_Graph.prems(2) unfolding rules' .
    have fresh_sharp': "\<And>f n.
      \<not> defined (set (rules ?d)) (Sharp f,n)"
      using Guarded_CSR_DP_Dep_Graph.prems(3) unfolding rules' .
    have fresh_U': "\<And>n. \<not> defined (set (rules ?d)) (U,n)"
      using Guarded_CSR_DP_Dep_Graph.prems(4) unfolding rules' .
    have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
      apply (rule Guarded_CSR_DP_Dep_Graph.IH[
          where xa = "(Some p,C)" and xaa = "Some p" and xaaa = p])
             apply (rule mem)
            apply simp
           apply simp
          apply (rule plain')
         apply (rule wf')
        apply (rule fresh_sharp')
       apply (rule fresh_U')
      apply (rule rec)
      done
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp) \<inter> set C)
      (set (dpp_ops.rules J dpp))"
      using fin' unfolding pairs' rules' .
  qed
next
  case (Guarded_CSR_DP_OvCons witness)
  from Guarded_CSR_DP_OvCons.prems(5) have terminal:
      "isOK (check_csr_guarded_ovcons_terminal J \<mu> dpp witness)"
    by simp
  show ?case by (rule check_csr_guarded_ovcons_terminal_sound[
      OF J terminal])
qed

datatype (dead 'f, dead 'l, dead 'v) guarded_csr_termination_proof =
    Guarded_CSR_Rule_Removal
      "('f,'l) lab redtriple_impl" "('f,'l,'v) trsLL"
      "('f,'l,'v) guarded_csr_termination_proof"
  | Guarded_CSR_Dependency_Pairs
      "('f,'l,'v) trsLL" "('f,'l,'v) guarded_csr_dp_proof"
  | Guarded_CSR_Improved_Dependency_Pairs
      "('f,'l) lab" "('f,'l,'v) trsLL"
      "('f,'l,'v) guarded_csr_dp_proof"

primrec check_guarded_csr_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> ((('f,label_type) lab) muL) \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) guarded_csr_termination_proof \<Rightarrow> showsl check"
where
  "check_guarded_csr_termination_proof I J i \<mu> R
      (Guarded_CSR_Rule_Removal redp Rr prf) =
    debug i (STR ''guarded CSR rule removal'')
      (case csr_rule_removal_impl redp \<mu> Rr R of
        Inl e \<Rightarrow> Inl e
      | Inr R2 \<Rightarrow> check_guarded_csr_termination_proof I J
          (add_index i 1) \<mu> R2 prf)"
| "check_guarded_csr_termination_proof I J i \<mu> R
      (Guarded_CSR_Dependency_Pairs P prf) =
    debug i (STR ''guarded CSR dependency pairs'') (do {
      csr_sharp_mu_check \<mu>;
      check (list_all (\<lambda>(f,n). case f of Sharp _ \<Rightarrow> False | _ \<Rightarrow> True)
        (defined_list R))
        (showsl_lit (STR ''guarded CSR source defines a reserved marked symbol''));
      dpp \<leftarrow> mu_csr_dependency_pairs_tt Sharp J \<mu> R P;
      check_guarded_csr_dp_proof I J \<mu> (add_index i 1) dpp prf
    })"
| "check_guarded_csr_termination_proof I J i \<mu> R
      (Guarded_CSR_Improved_Dependency_Pairs U P prf) =
    debug i (STR ''guarded improved CSR dependency pairs'') (do {
      dpp \<leftarrow> improved_csr_dependency_pairs_tt J U \<mu> R P;
      check_guarded_improved_csr_dp_proof I J U \<mu>
        (add_index i 1) dpp prf
    })"

lemma check_guarded_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_guarded_csr_termination_proof I J i \<mu> R prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
  using ok
proof (induct "prf" arbitrary: R i)
  case (Guarded_CSR_Rule_Removal redp rr child)
  from Guarded_CSR_Rule_Removal.prems obtain R2 where
      proc: "csr_rule_removal_impl redp \<mu> rr R = return R2"
    and rec: "isOK (check_guarded_csr_termination_proof I J
      (add_index i 1) \<mu> R2 child)"
    by (cases "csr_rule_removal_impl redp \<mu> rr R"; auto)
  have sn: "SN (csstep (mu_of \<mu>) (set R2))"
    by (rule Guarded_CSR_Rule_Removal.hyps[OF rec])
  show ?case by (rule csr_rule_removal_impl[OF proc sn])
next
  case (Guarded_CSR_Dependency_Pairs P dp_prf)
  let ?idx = "add_index i 1"
  from Guarded_CSR_Dependency_Pairs.prems obtain dpp where
      no_sharp: "list_all
        (\<lambda>(f,n). case f of Sharp _ \<Rightarrow> False | _ \<Rightarrow> True)
        (defined_list R)"
    and tt: "mu_csr_dependency_pairs_tt Sharp J \<mu> R P = return dpp"
    and rec: "isOK (check_guarded_csr_dp_proof I J \<mu> ?idx dpp dp_prf)"
    by (cases "mu_csr_dependency_pairs_tt Sharp J \<mu> R P"; auto)
  note tt' = tt[unfolded mu_csr_dependency_pairs_tt_def Let_def, simplified]
  have wf: "wf_trs (set R)" using tt' by auto
  have vc: "rhs_mu_vars_condition (mu_of \<mu>) (set R)"
    by (rule rhs_mu_vars_condition_list_sound, insert tt', auto)
  have D: "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    using tt' by auto
  have fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
  proof -
    fix f n
    from no_sharp show "\<not> defined (set R) (Sharp f,n)"
      by (auto simp: list_all_iff)
  qed
  interpret dpp_spec J by fact
  have dpp: "dpp = dpp_ops.mk J False False P [] [] [] R"
    using tt' by auto
  have plain: "plain_csr_dpp J dpp"
    and rules: "set (rules dpp) = set R"
    and pairs: "set (pairs dpp) = set P"
    using plain_csr_dpp_mk_context[OF J dpp] by auto
  have fin_dpp: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp)) (set (rules dpp))"
    by (rule check_guarded_csr_dp_proof_sound[
        OF I J plain wf[unfolded rules[symmetric]]
          fresh[unfolded rules[symmetric]] rec])
  have finP: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using fin_dpp unfolding rules pairs .
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R)) (set R)"
    apply (rule finite_min_csr_dpp_rename_vars[
        where P' = "set P" and
          P = "mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R)" and
          R = "set R"])
     apply (rule finP)
    subgoal for st
      using tt' eq_rule_mod_vars_refl[of st]
      unfolding mu_CSDP_list by blast
    done
  show ?case by (rule finite_min_csr_mu_CSDP_on_imp_SN_csstep[
      OF wf fresh vc D fin])
next
  case (Guarded_CSR_Improved_Dependency_Pairs U P dp_prf)
  let ?idx = "add_index i 1"
  from Guarded_CSR_Improved_Dependency_Pairs.prems obtain dpp where
      tt: "improved_csr_dependency_pairs_tt J U \<mu> R P = return dpp"
    and rec: "isOK (check_guarded_improved_csr_dp_proof
      I J U \<mu> ?idx dpp dp_prf)"
    by (cases "improved_csr_dependency_pairs_tt J U \<mu> R P"; auto)
  from improved_csr_dependency_pairs_tt_sound[OF J tt]
  have dpp: "dpp = dpp_ops.mk J False False P [] [] [] R"
    and wf: "wf_trs (set R)"
    and fresh_U: "\<And>n. (U,n) \<notin> set (funas_trs_list R)"
    and unsharp: "\<not> is_sharp_lab U"
    and fresh_sharp: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and cover: "improved_csdp_coverage Sharp U (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P)"
    by auto
  interpret dpp_spec J by fact
  have plain: "plain_csr_dpp J dpp"
    and rules: "set (rules dpp) = set R"
    and pairs: "set (pairs dpp) = set P"
    using plain_csr_dpp_mk_context[OF J dpp] by auto
  have fresh_U': "\<And>n. \<not> defined (set R) (U,n)"
  proof
    fix n
    assume def: "defined (set R) (U,n)"
    then obtain l r where lr: "(l,r) \<in> set R"
      and root: "root l = Some (U,n)"
      unfolding defined_def by blast
    have root_mem: "(U,n) \<in> funas_term l"
      using root by (cases l, auto)
    have "(U,n) \<in> set (funas_trs_list R)"
      using lr root_mem by (force simp: funas_trs_def funas_rule_def)
    with fresh_U show False by contradiction
  qed
  have fin_dpp: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp)) (set (rules dpp))"
    by (rule check_guarded_improved_csr_dp_proof_sound[
        OF I J plain wf[unfolded rules[symmetric]]
          fresh_sharp[unfolded rules[symmetric]]
          fresh_U'[unfolded rules[symmetric]] unsharp rec])
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using fin_dpp unfolding rules pairs .
  have defs: "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    by auto
  show ?case by (rule finite_min_improved_CSDP_imp_SN_csstep[
      OF wf defs cover fresh_U' unsharp fresh_sharp fin])
qed

end
