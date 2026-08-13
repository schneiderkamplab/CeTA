(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Typed_Checker
  imports CSR_Muterm_Ext.CSR_Muterm_Usable_Rules
begin

theorem check_muterm_typed_dp_proof_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and ok: "isOK (check_muterm_typed_dp_proof I J \<mu> i R S P p)"
  shows "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
  using ok
proof (induct p arbitrary: i P)
  case Muterm_Typed_P_Is_Empty
  then have "P = []" by simp
  then have empty: "muterm_typed_pair_step (set P) (set S) = {}" by simp
  show ?case unfolding finite_muterm_typed_dpp_def empty
    by (rule SN_rel_empty1)
next
  case (Muterm_Typed_Local_Usable U child)
  from Muterm_Typed_Local_Usable.prems have closed_check:
      "muterm_qcs_ur_closed_check R S U \<mu> P"
    and child_ok: "isOK (check_dp_termination_proof I J False
      (add_index i 1) (dpp_ops.mk J False False P [] [] [] U) child)"
    by auto
  have closed: "muterm_qcs_ur_closed (set R) (set S) (set U)
      (mu_of \<mu>) (set P)"
    by (rule muterm_qcs_ur_closed_check_sound[OF closed_check])
  have child_fin: "finite_dpp (False,False,set P,{},{},{},set U)"
  proof -
    have raw: "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False P [] [] [] U))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    show ?thesis using raw dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" U]
      by simp
  qed
  show ?case by (rule finite_muterm_typed_dpp_usable[
    OF wf fresh closed child_fin])
next
  case (Muterm_Typed_CSR_Proof child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_CSR_Proof.prems have nc_list:
      "list_all (is_Fun \<circ> snd) P"
    and child_ok: "isOK (check_csr_dp_termination_proof_core
      I J \<mu> False (add_index i 1) ?d child)"
    by (auto simp: Let_def)
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have raw: "finite_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
    by (rule check_csr_dp_termination_proof_core_sound[
      OF I J plain child_ok])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set P,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
    by simp
  have fin: "finite_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using raw sem dpp_spec.pairs_sound[OF J,of ?d]
      dpp_spec.rules_sound[OF J,of ?d]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have nc: "\<forall>dp\<in>set P. is_Fun (snd dp)"
    using nc_list by (simp add: list_all_iff)
  show ?case by (rule finite_csr_dpp_imp_finite_muterm_typed_noncollapsing[
    OF nc fin])
next
  case (Muterm_Typed_Dep_Graph edps)
  from Muterm_Typed_Dep_Graph.prems have graph_ok:
      "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and components_ok: "isOK (check_muterm_typed_graph_components
      I J \<mu> i R S P edps)"
    by (auto simp: Let_def)
  show ?case
  proof (rule check_muterm_typed_dep_graph_sound[OF graph_ok])
    fix p C
    assume mem: "(Some p,C) \<in> set edps"
    from check_muterm_typed_graph_components_member[OF components_ok mem]
    obtain j where rec: "isOK (check_muterm_typed_dp_proof I J \<mu> j R S
      (filter (\<lambda>dp. dp \<in> set C) P) p)" by blast
    have set_filter: "set (filter (\<lambda>dp. dp \<in> set C) P) =
      set P \<inter> set C" by auto
    show "finite_muterm_typed_dpp Sharp (mu_of \<mu>) (set R)
      (set P \<inter> set C) (set S)"
      unfolding set_filter[symmetric]
      apply (rule Muterm_Typed_Dep_Graph.hyps)
       apply (rule mem)
      apply simp
      apply simp
      apply (rule rec)
      done
  qed
qed

end
