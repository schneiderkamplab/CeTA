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
    by auto
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
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_csr_dpp_imp_finite_muterm_typed_noncollapsing[OF nc fin])
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
