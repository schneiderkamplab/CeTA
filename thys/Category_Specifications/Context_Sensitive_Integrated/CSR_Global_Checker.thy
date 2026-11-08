theory CSR_Global_Checker
  imports CSR_Signature_Extension
begin

lemma check_extended_csr_global_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_extended_csr_termination_proof I J a i mu R p)"
  shows "SN (csstep (mu_of mu) (set R))"
proof (cases "extended_csr_proof_is_global p")
  case True
  show ?thesis using check_extended_csr_termination_proof_sound[OF I J ok] True by blast
next
  case False
  then obtain U P S child where p: "p=Conservative_CSR_Dependency_Pairs U P S child"
    by (cases p) auto
  from ok p obtain dpp where tt: "conservative_csr_dependency_pairs_tt J U mu R P S = Inr dpp"
    by auto
  have wf: "Trs.wf_trs (set R)"
    by (rule conservative_csr_dependency_pairs_tt_sound(2)[OF J tt])
  have restricted: "SN (sig_step (set (funas_trs_list R)) (csstep (mu_of mu) (set R)))"
    using check_extended_csr_termination_proof_sound[OF I J ok] by blast
  show ?thesis by (rule csr_signature_extension[OF _ wf restricted]) simp
qed

lemma check_gm_csr_global_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_gm_extended_csr_termination_proof
      I J a i \<mu> R p)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof (cases p)
  case (Existing_CSR_Proof old)
  with ok have old_ok:
    "isOK (check_extended_csr_termination_proof I J a i \<mu> R old)"
    by simp
  show ?thesis by (rule check_extended_csr_global_sound[OF I J old_ok])
next
  case (Guarded_CSR_Proof child)
  from ok Guarded_CSR_Proof have child_ok:
      "isOK (check_guarded_csr_termination_proof I J i \<mu> R child)"
    by simp
  have "SN (csstep (mu_of \<mu>) (set R))"
    by (rule check_guarded_csr_termination_proof_sound[OF I J child_ok])
  then show ?thesis
    by assumption
next
  case (Innermost_CSR_Dependency_Pairs P S child)
  show ?thesis
  proof (cases "S = []")
    case True
    from ok Innermost_CSR_Dependency_Pairs True have rec:
        "isOK (check_innermost_csr_or_rta08_termination_proof
          I J i \<mu> R P child)"
      by simp
    have "SN (csstep (mu_of \<mu>) (set R))"
      by (rule check_innermost_csr_or_rta08_termination_proof_sound[
        OF I J rec])
    then show ?thesis
      by assumption
  next
    case False
    from ok Innermost_CSR_Dependency_Pairs False obtain dpp where tt:
        "direct_innermost_csr_dependency_pairs_tt J \<mu> R P (R @ S) = Inr dpp"
      and rec: "isOK (check_csr_dp_termination_proof
        I J False (add_index i 1) dpp child)"
      by auto
    have fin: "finite_dpp (dpp_ops.dpp J dpp)"
      by (rule check_csr_dp_termination_proof_sound[OF I J rec])
    have "SN (csstep (mu_of \<mu>) (set R))"
      by (rule direct_innermost_csr_dependency_pairs_tt_finite_imp_SN[
        OF J tt fin])
    then show ?thesis
      by assumption
  qed
next
  case (Muterm_Innermost_CSR_Dependency_Pairs P S child)
  from ok Muterm_Innermost_CSR_Dependency_Pairs obtain dpp where tt:
      "muterm_innermost_csr_dependency_pairs_tt J \<mu> R P S = Inr dpp"
    and rec: "isOK (check_csr_dp_termination_proof
      I J False (add_index i 1) dpp child)"
    by auto
  have fin: "finite_dpp (dpp_ops.dpp J dpp)"
    by (rule check_csr_dp_termination_proof_sound[OF I J rec])
  have "SN (csstep (mu_of \<mu>) (set R))"
    by (rule muterm_innermost_csr_dependency_pairs_tt_finite_imp_SN[
      OF J tt fin])
  then show ?thesis
    by assumption
next
  case (Muterm_Usable_CSR_Dependency_Pairs P S W child)
  from ok Muterm_Usable_CSR_Dependency_Pairs obtain dpp where tt:
      "muterm_usable_csr_dependency_pairs_tt J \<mu> R P S W = Inr dpp"
    and rec: "isOK (check_csr_dp_termination_proof
      I J False (add_index i 1) dpp child)"
    by auto
  have fin: "finite_dpp (dpp_ops.dpp J dpp)"
    by (rule check_csr_dp_termination_proof_sound[OF I J rec])
  have "SN (csstep (mu_of \<mu>) (set R))"
    by (rule muterm_usable_csr_dependency_pairs_tt_finite_imp_SN[
      OF J tt fin])
  then show ?thesis
    by assumption
next
  case (Muterm_Typed_CSR_Dependency_Pairs P S child)
  have wf: "Trs.wf_trs (set R)" using ok Muterm_Typed_CSR_Dependency_Pairs
    by (auto simp: Let_def)
  have restricted: "SN (sig_step (set (funas_trs_list R)) (csstep (mu_of \<mu>) (set R)))"
    by (rule check_gm_extended_csr_termination_proof_sound[OF I J ok])
  show ?thesis by (rule csr_signature_extension[OF _ wf restricted]) simp

next
  case (Muterm_Expanded_Innermost_CSR_Dependency_Pairs P S child)
  have wf: "Trs.wf_trs (set R)" using ok Muterm_Expanded_Innermost_CSR_Dependency_Pairs
    by (auto simp: Let_def)
  have restricted: "SN (sig_step (set (funas_trs_list R)) (csstep (mu_of \<mu>) (set R)))"
    by (rule check_gm_extended_csr_termination_proof_sound[OF I J ok])
  show ?thesis by (rule csr_signature_extension[OF _ wf restricted]) simp

next
  case (Muterm_Expanded_Innermost_Filtered_Usable_CSR_Dependency_Pairs P S child)
  have wf: "Trs.wf_trs (set R)" using ok Muterm_Expanded_Innermost_Filtered_Usable_CSR_Dependency_Pairs
    by (auto simp: Let_def)
  have restricted: "SN (sig_step (set (funas_trs_list R)) (csstep (mu_of \<mu>) (set R)))"
    by (rule check_gm_extended_csr_termination_proof_sound[OF I J ok])
  show ?thesis by (rule csr_signature_extension[OF _ wf restricted]) simp

next
  case (Muterm_Expanded_Innermost_Usable_CSR_Dependency_Pairs P S U child)
  have wf: "Trs.wf_trs (set R)" using ok Muterm_Expanded_Innermost_Usable_CSR_Dependency_Pairs
    by (auto simp: Let_def)
  have restricted: "SN (sig_step (set (funas_trs_list R)) (csstep (mu_of \<mu>) (set R)))"
    by (rule check_gm_extended_csr_termination_proof_sound[OF I J ok])
  show ?thesis by (rule csr_signature_extension[OF _ wf restricted]) simp

next
  case (GM_CSR_Transformation removals mark c active child)
  from ok GM_CSR_Transformation obtain R' where remove:
      "csr_rule_removals_impl removals \<mu> R = Inr R'"
    by (cases "csr_rule_removals_impl removals \<mu> R", auto)
  let ?D = "defined_list R'"
  let ?F = "remdups (funas_trs_list R)"
  let ?act = "\<lambda>fn. the (map_of active fn)"
  let ?T = "gm_transformed_rules_list (mu_of \<mu>) (set ?D) ?act mark ?F R' ?D"
  from ok GM_CSR_Transformation remove have wf: "Trs.wf_trs (set R')"
    and source_sig: "funas_trs (set R') \<subseteq> set ?F"
    and ground_c: "(c, 0) \<in> set ?F"
    and child_ok: "isOK (check_trs_termination_proof I J False (add_index i 1)
      (tp_ops.mk I False [] ?T []) child)"
    by (auto simp: Let_def)
  from check_trs_termination_proof[OF I J child_ok]
  have child_SN: "SN (Trs.rstep (set ?T))"
    unfolding tp_spec.mk_sound[OF I] SN_qrel_def by auto
  have transformed: "set (gm_transformed_rules_list (mu_of \<mu>) (set ?D)
      ?act mark ?F R' ?D) \<subseteq> set ?T" by simp
  from gm_transformed_rules_list_sound[OF wf source_sig ground_c transformed child_SN]
  have residual: "SN (sig_step (set (funas_trs_list R))
      (csstep (mu_of \<mu>) (set R')))" by simp
  have global: "SN (csstep (mu_of \<mu>) (set R'))"
    by (rule csr_signature_extension[OF _ wf residual]) (use source_sig in simp)
  show ?thesis by (rule csr_rule_removals_impl_sound[OF remove global])
qed


lemma csr_integrated_global_sound:
  assumes accepted: "certify_integrated_cert_problem False
    (FP_TRS_input (Context_Sensitive mu) Rs) Termination (Decision True) certificate = Certified"
  shows "SN (csstep (mu_of mu) (set Rs))"
proof -
  have alternatives:
    "(\<exists>p. isOK (check_gm_extended_csr_termination_proof tp_impl dpp_impl False
        (showsl_lit (STR ''1'')) mu Rs p)) \<or>
     (\<exists>p. isOK (check_fptrs_termination_proof tp_impl dpp_impl False
        (showsl_lit (STR ''1'')) (fp_strategy_to_fp_impl (Context_Sensitive mu) Rs, Rs) p))"
  proof (cases certificate)
    case (Inl p)
    show ?thesis using accepted Inl
      by (cases p; auto simp: certify_integrated_cert_problem_def
        certify_cert_problem_rfc_absolute_def certify_cert_problem_def check_cert_def Let_def
        split: sum.splits if_splits)
  next
    case (Inr p)
    then show ?thesis using accepted
      by (simp add: certify_integrated_cert_problem_def certify_relative_adp_cert_problem_def
        check_relative_adp_cert_problem_def)
  qed
  then show ?thesis
  proof
    assume "\<exists>p. isOK (check_gm_extended_csr_termination_proof tp_impl dpp_impl False
        (showsl_lit (STR ''1'')) mu Rs p)"
    then obtain p where ok: "isOK (check_gm_extended_csr_termination_proof tp_impl dpp_impl False
        (showsl_lit (STR ''1'')) mu Rs p)" by blast
    show ?thesis by (rule check_gm_csr_global_sound[OF tp_rbt_impl dpp_rbt_impl ok])
  next
    assume "\<exists>p. isOK (check_fptrs_termination_proof tp_impl dpp_impl False
        (showsl_lit (STR ''1'')) (fp_strategy_to_fp_impl (Context_Sensitive mu) Rs, Rs) p)"
    then obtain p where ok: "isOK (check_fptrs_termination_proof tp_impl dpp_impl False
        (showsl_lit (STR ''1'')) (fp_strategy_to_fp_impl (Context_Sensitive mu) Rs, Rs) p)" by blast
    from check_fptrs_termination_proof[OF tp_rbt_impl dpp_rbt_impl ok]
    show ?thesis by (simp add: fp_strategy_to_fp_impl_def SN_fpstep_def csstep_iff_fpstep_impl)
  qed
qed
end
