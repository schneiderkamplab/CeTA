(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Typed_Checker
  imports CSR_Muterm_Ext.CSR_Muterm_Usable_Rules
begin

lemma muterm_typed_pair_step_subset_ordinary:
  "muterm_typed_pair_step P S \<subseteq>
    (rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*"
proof
  fix st
  assume step: "st \<in> muterm_typed_pair_step P S"
  obtain s t where st: "st = (s,t)" by (cases st)
  from step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S)"
    unfolding st muterm_typed_pair_step_def by auto
  from cases show "st \<in> (rstep (R \<union> S))\<^sup>* O rrstep P O
    (rstep (R \<union> S))\<^sup>*"
  proof
    assume noncoll: "muterm_noncollapsing_rrstep P s t"
    then have pair: "(s,t) \<in> rrstep P"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by blast
    show "st \<in> (rstep (R \<union> S))\<^sup>* O rrstep P O
      (rstep (R \<union> S))\<^sup>*"
      unfolding st using pair by auto
  next
    assume collapsing:
      "\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S"
    then obtain x where pair: "(s,x) \<in> rrstep P"
      and bridge: "(x,t) \<in> rrstep S"
      using muterm_collapsing_rrstep_imp_rrstep by blast
    from bridge obtain l r \<sigma> where lr: "(l,r) \<in> S"
      and x: "x = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding rrstep_def' by blast
    have weak: "(x,t) \<in> rstep (R \<union> S)"
      unfolding x t
      by (rule rstepI[OF UnI2[OF lr], of _ Hole \<sigma>], simp_all)
    show "st \<in> (rstep (R \<union> S))\<^sup>* O rrstep P O
      (rstep (R \<union> S))\<^sup>*"
      unfolding st using pair weak by auto
  qed
qed

theorem finite_ordinary_imp_finite_muterm_typed:
  assumes fin: "finite_dpp (False,False,P,{},{},{},R \<union> S)"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
proof -
  let ?A = "(rstep (R \<union> S))\<^sup>* O rrstep P O
    (rstep (R \<union> S))\<^sup>*"
  let ?B = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  from fin have sn: "SN ?A"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have cs_sub: "csdp_step Sharp \<mu> R \<subseteq> rstep (R \<union> S)"
  proof -
    have "csdp_step Sharp \<mu> R \<subseteq> rstep R"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    also have "rstep R \<subseteq> rstep (R \<union> S)"
      by (rule rstep_mono, auto)
    finally show ?thesis .
  qed
  have strict_sub: "muterm_typed_pair_step P S \<subseteq> ?A"
    by (rule muterm_typed_pair_step_subset_ordinary)
  have pre_sub: "(csdp_step Sharp \<mu> R)\<^sup>* \<subseteq>
      (rstep (R \<union> S))\<^sup>*"
    by (rule rtrancl_mono[OF cs_sub])
  have sub: "?B \<subseteq> ?A"
  proof
    fix st
    assume mem: "st \<in> ?B"
    obtain s t where st: "st = (s,t)" by (cases st)
    from mem obtain x y where pre: "(s,x) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      and strict: "(x,y) \<in> muterm_typed_pair_step P S"
      and post: "(y,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      unfolding st by auto
    from strict_sub strict obtain a b where xa: "(x,a) \<in> (rstep (R \<union> S))\<^sup>*"
      and pair: "(a,b) \<in> rrstep P"
      and by_step: "(b,y) \<in> (rstep (R \<union> S))\<^sup>*"
      by auto
    have sa: "(s,a) \<in> (rstep (R \<union> S))\<^sup>*"
      by (rule rtrancl_trans[OF set_mp[OF pre_sub pre] xa])
    have bt: "(b,t) \<in> (rstep (R \<union> S))\<^sup>*"
      by (rule rtrancl_trans[OF by_step set_mp[OF pre_sub post]])
    show "st \<in> ?A" unfolding st using sa pair bt by auto
  qed
  then have "SN ?B" by (rule SN_subset[OF sn])
  then show ?thesis unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
qed

theorem check_muterm_typed_dp_proof_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and ok: "isOK (check_muterm_typed_dp_proof I J \<mu> i R S P p)"
  shows "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
  using ok
proof (induct p arbitrary: i P)
  case Muterm_Typed_P_Is_Empty
  then have "P = []" by simp
  then have empty: "muterm_min_typed_pair_step Sharp (mu_of \<mu>)
      (set R) (set P) (set S) = {}"
    unfolding muterm_min_typed_pair_step_def by simp
  show ?case unfolding finite_muterm_min_typed_dpp_def empty
    by (rule SN_rel_empty1)
next
  case (Muterm_Typed_Local_Usable U child)
  from Muterm_Typed_Local_Usable.prems have closure_ok:
      "muterm_qcs_ur_closed_check R S U \<mu> P"
    and child_ok:
      "isOK (check_dp_termination_proof I J False
        (add_index i 1) (dpp_ops.mk J False False P [] [] [] U) child)"
    unfolding muterm_qcs_ur_closed_check_def Let_def by auto
  have child_fin: "finite_dpp (False,False,set P,{},{},{},set U)"
  proof -
    have raw: "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False P [] [] [] U))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    show ?thesis using raw dpp_spec.mk_sound[
      OF J, of False False P "[]" "[]" "[]" U] by simp
  qed
  have closed: "muterm_qcs_ur_closed (set R) (set S) (set U)
      (mu_of \<mu>) (set P)"
    by (rule muterm_qcs_ur_closed_check_sound[OF closure_ok])
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_usable[OF wf fresh closed child_fin])
  show ?case by (rule finite_muterm_typed_imp_finite_min_typed[OF full])
next
  case (Muterm_Typed_CSR_Proof child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_CSR_Proof.prems have nc_list:
      "list_all (is_Fun \<circ> snd) P"
    and child_ok: "isOK (check_csr_dp_termination_proof_min
      I J \<mu> False (add_index i 1) ?d child)"
    by (auto simp: Let_def)
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have rules_d: "set (dpp_ops.rules J ?d) = set R"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
      dpp_spec.rules_sound[OF J, of ?d]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have wf_d: "wf_trs (set (dpp_ops.rules J ?d))"
    unfolding rules_d by (rule wf)
  have fresh_d: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J ?d)) (Sharp f,n)"
    unfolding rules_d by (rule fresh)
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
    by (rule check_csr_dp_termination_proof_min_sound[
      OF I J plain wf_d fresh_d child_ok])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set P,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
    by simp
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using raw sem dpp_spec.pairs_sound[OF J,of ?d]
      dpp_spec.rules_sound[OF J,of ?d]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have nc: "\<forall>dp\<in>set P. is_Fun (snd dp)"
    using nc_list by (simp add: list_all_iff)
  show ?case
    by (rule finite_min_csr_dpp_imp_finite_muterm_min_typed_noncollapsing[
      OF nc fin])
next
  case (Muterm_Typed_Expanded_CSR_Proof child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  from Muterm_Typed_Expanded_CSR_Proof.prems have child_ok:
      "isOK (check_muterm_expanded_csr_proof
        I J \<mu> (add_index i 1) ?d child)"
    by (simp add: Let_def)
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J, of False False ?E "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have rules_d: "set (dpp_ops.rules J ?d) = set R"
    using dpp_spec.mk_sound[OF J, of False False ?E "[]" "[]" "[]" R]
      dpp_spec.rules_sound[OF J, of ?d]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have wf_d: "wf_trs (set (dpp_ops.rules J ?d))"
    unfolding rules_d by (rule wf)
  have fresh_d: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J ?d)) (Sharp f,n)"
    unfolding rules_d by (rule fresh)
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
    by (rule check_muterm_expanded_csr_proof_sound[
      OF I J plain wf_d fresh_d child_ok])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set ?E,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False ?E "[]" "[]" "[]" R]
    by simp
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set ?E) (set R)"
    using raw sem dpp_spec.pairs_sound[OF J,of ?d]
      dpp_spec.rules_sound[OF J,of ?d]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
    using fin set_muterm_expanded_pairs_list[of string_renameN P S] by simp
  show ?case
    by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[OF fin'])
next
  case (Muterm_Typed_Expanded_Local_Usable U child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  from Muterm_Typed_Expanded_Local_Usable.prems have closure_ok:
      "muterm_qcs_expanded_ur_closed_check R S U \<mu> P"
    and child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] U) child)"
    unfolding muterm_qcs_expanded_ur_closed_check_def Let_def by auto
  have raw: "finite_dpp (False,False,set ?E,{},{},{},set U)"
  proof -
    have "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False ?E [] [] [] U))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    then show ?thesis using dpp_spec.mk_sound[
      OF J, of False False ?E "[]" "[]" "[]" U] by simp
  qed
  have fin: "finite_dpp (False,False,
      muterm_expanded_pairs string_renameN (set P) (set S),{},{},{},set U)"
    using raw set_muterm_expanded_pairs_list[of string_renameN P S] by simp
  have closed: "muterm_qcs_expanded_ur_closed (set R) (set S) (set U)
      (mu_of \<mu>) (set P)"
    by (rule muterm_qcs_expanded_ur_closed_check_sound[OF closure_ok])
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_expanded_usable[
      OF wf fresh closed fin])
  show ?case by (rule finite_muterm_typed_imp_finite_min_typed[OF full])
next
  case (Muterm_Typed_Expanded_Strong_Usable U redp Pr child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  from Muterm_Typed_Expanded_Strong_Usable.prems
  obtain d' where proc:
      "muterm_strong_ur_redpair_proc J \<mu> (get_rel_impl redp) Pr U ?d = return d'"
    and child_ok: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
      (add_index i 1) d' child)" by (auto simp: Let_def)
  have d': "d' = dpp_spec.delete_pairs J ?d Pr"
    using proc unfolding muterm_strong_ur_redpair_proc_def by auto
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J,of False False ?E "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have plain': "plain_csr_dpp J d'"
    unfolding d' by (rule plain_csr_dpp_delete_pairs[OF J plain])
  interpret dpp_spec J by fact
  have rules_d: "set (rules ?d) = set R"
    using mk_sound[of False False ?E "[]" "[]" "[]" R]
      rules_sound[of ?d] dpp_sound[of ?d] by auto
  have rules': "set (rules d') = set (rules ?d)"
    using d' delete_P_Pw_sound[of ?d Pr Pr] rules_sound[of d'] by auto
  have wf_d: "wf_trs (set (rules ?d))" using wf unfolding rules_d .
  have fresh_d: "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
    using fresh unfolding rules_d .
  have wf': "wf_trs (set (rules d'))" using wf_d unfolding rules' .
  have fresh': "\<And>f n. \<not> defined (set (rules d')) (Sharp f,n)"
    using fresh_d unfolding rules' .
  have child_fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs d')) (set (rules d'))"
    by (rule check_csr_dp_termination_proof_min_sound[
      OF I J plain' wf' fresh' child_ok])
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
    by (rule muterm_strong_ur_redpair_proc_sound[
      OF J get_rel_impl proc wf_d fresh_d child_fin])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set ?E,{},{},{},set R)"
    using mk_sound[of False False ?E "[]" "[]" "[]" R] by simp
  have expanded_fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
    using fin sem pairs_sound[of ?d] rules_sound[of ?d] dpp_sound[of ?d]
      set_muterm_expanded_pairs_list[of string_renameN P S] by auto
  show ?case
    by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[
      OF expanded_fin])
next
  case (Muterm_Typed_Expanded_Ordinary child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  from Muterm_Typed_Expanded_Ordinary.prems have child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] R) child)"
    by (simp add: Let_def)
  have raw: "finite_dpp (False,False,set ?E,{},{},{},set R)"
  proof -
    have "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False ?E [] [] [] R))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    then show ?thesis using dpp_spec.mk_sound[
      OF J, of False False ?E "[]" "[]" "[]" R] by simp
  qed
  have fin: "finite_dpp (False,False,
      muterm_expanded_pairs string_renameN (set P) (set S),{},{},{},
      set R)"
    using raw set_muterm_expanded_pairs_list[of string_renameN P S]
    by simp
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_expanded_ordinary[OF fin])
  show ?case by (rule finite_muterm_typed_imp_finite_min_typed[OF full])
next
  case (Muterm_Typed_Dep_Graph edps)
  from Muterm_Typed_Dep_Graph.prems have graph_ok:
      "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and components_ok: "isOK (check_muterm_typed_graph_components
      I J \<mu> i R S P edps)"
    by (auto simp: Let_def)
  show ?case
  proof (rule check_muterm_min_typed_dep_graph_sound[OF graph_ok])
    fix p C
    assume mem: "(Some p,C) \<in> set edps"
    from check_muterm_typed_graph_components_member[OF components_ok mem]
    obtain j where rec: "isOK (check_muterm_typed_dp_proof I J \<mu> j R S
      (filter (\<lambda>dp. dp \<in> set C) P) p)" by blast
    have set_filter: "set (filter (\<lambda>dp. dp \<in> set C) P) =
      set P \<inter> set C" by auto
    show "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>) (set R)
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
