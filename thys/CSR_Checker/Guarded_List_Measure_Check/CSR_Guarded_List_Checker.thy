(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Guarded_List_Checker
  imports CSR_Guarded_List_Measure
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
        X L IL M N V V1 V2) = debug id (STR ''guarded OvConsOS CSR component'') (do {
    check (plain_csr_dpp J dpp)
      (showsl_lit (STR ''guarded component is not a plain CSR-DP problem''));
    check (distinct
      [tt,a,natp,listp,ilistp,u11,u21,u31,z,su,len,ni,co,ta,zs])
      (showsl_lit (STR ''guarded component symbols are not distinct''));
    check (Sharp u11 \<notin> set [a,u11,u21,u31] \<and>
      Sharp len \<notin> set [a,u11,u21,u31] \<and> Sharp u11 \<noteq> Sharp len)
      (showsl_lit (STR ''guarded component marked symbols are not fresh''));
    check (set (dpp_ops.rules J dpp) =
      csr_guard_ovcons_residual tt a natp listp ilistp u11 u21 u31
        z su len ni co ta zs X L IL M N V V1 V2)
      (showsl_lit (STR ''guarded component rules are not the exact residual''));
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
    and rules: "set (dpp_ops.rules J dpp) =
      csr_guard_ovcons_residual tt a natp listp ilistp u11 u21 u31
        z su len ni co ta zs X L IL M N V V1 V2"
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
  show ?thesis
    apply (rule finite_min_csr_dpp_ovcons_guarded_two_pair[
        where R = "set (dpp_ops.rules J dpp)" and
          P = "set (dpp_ops.pairs J dpp)" and \<mu> = "mu_of \<mu>"])
                apply (rule symbols)
               apply (rule marked_u11)
              apply (rule marked_len)
             apply (rule wrappers)
            apply (rule rules)
           apply (rule pairs)
          apply (rule wf)
         apply (rule fresh)
        apply (rule frozen')
       apply (rule mu_and)
      apply (rule mu_nat)
     apply (rule mu_list)
    apply (rule mu_ilist)
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

end
