theory TRS_Outermost_Integrated
  imports Category_Outermost_Bridge.TRS_Outermost_Loop_Bridge
    Relative_ADP_Ceta_Dev.Relative_ADP_Ceta
begin
text \<open>YES uses all concrete integrated Outermost termination proofs with
certificate assumptions disabled. NO below uses direct loop certificates with
finite signature checks on every witness component. No unrestricted
signature-extension claim is needed for either result.\<close>
theorem trs_outermost_integrated_YES:
  assumes rules: "set Rs = to_rules R"
    and accepted: "certify_integrated_cert_problem False
      (FP_TRS_input Outermost Rs) Termination (Decision True) certificate = Certified"
  shows "trs_outermost_terminates A R"
proof -
  have sn: "SN (ostep (fst ` to_rules R) (to_rules R))"
    using certify_integrated_cert_problem_sound[OF accepted]
    by (simp add: desired_property_def rules)
  have "SN (sig_step (to_signature A) (ostep (fst ` to_rules R) (to_rules R)))"
    by (rule SN_subset[OF sn]) auto
  then show ?thesis by (simp add: trs_outermost_terminates_iff_signature)
qed

lemma outermost_integrated_loop_acceptance:
  assumes "certify_integrated_cert_problem False (FP_TRS_input Outermost Rs)
    Termination (Decision False)
    (Inl (TRS_Nontermination_Proof (TRS_Loop (TRS_loop_prf t w_seq mu C)))) = Certified"
  shows "isOK (check_fploop Rs (o_to_fp_impl (map fst Rs)) (FP_loop_prf C mu t w_seq))"
  using assms
  by (cases "check_fploop Rs (o_to_fp_impl (map fst Rs)) (FP_loop_prf C mu t w_seq)";
      simp_all add: certify_integrated_cert_problem_def certify_cert_problem_rfc_absolute_def
      certify_cert_problem_def check_cert_def fp_strategy_to_fp_impl_def Let_def
      del: check_fploop.simps split: sum.splits if_splits)

theorem trs_outermost_integrated_NO:
  assumes rules: "set Rs = to_rules R"
    and accepted: "certify_integrated_cert_problem False (FP_TRS_input Outermost Rs)
      Termination (Decision False)
      (Inl (TRS_Nontermination_Proof (TRS_Loop (TRS_loop_prf t w_seq mu C)))) = Certified"
    and ctxt: "funas_ctxt C \<subseteq> to_signature A"
    and subst: "\<And>x u. (x,u) \<in> set mu \<Longrightarrow> funas_term u \<subseteq> to_signature A"
    and start: "funas_term t \<subseteq> to_signature A"
    and terms: "\<And>p r u. (p,r,u) \<in> set w_seq \<Longrightarrow> funas_term u \<subseteq> to_signature A"
  shows "\<not> trs_outermost_terminates A R"
  by (rule trs_outermost_loop_checker_NO[OF rules
    outermost_integrated_loop_acceptance[OF accepted] ctxt subst start terms])

theorem trs_outermost_serialized_YES:
  assumes rules: "set Rs = to_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (FP_TRS_input Outermost Rs, Termination, Decision True, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "trs_outermost_terminates A R"
proof -
  have "certify_integrated_cert_problem False (FP_TRS_input Outermost Rs)
      Termination (Decision True) certificate = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  then show ?thesis by (rule trs_outermost_integrated_YES[OF rules])
qed

theorem trs_outermost_serialized_NO:
  assumes rules: "set Rs = to_rules R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (FP_TRS_input Outermost Rs, Termination, Decision False,
        Inl (TRS_Nontermination_Proof (TRS_Loop (TRS_loop_prf t w_seq mu C))))"
    and accepted: "certify_proof_integrated False None None None text = Certified"
    and ctxt: "funas_ctxt C \<subseteq> to_signature A"
    and subst: "\<And>x u. (x,u) \<in> set mu \<Longrightarrow> funas_term u \<subseteq> to_signature A"
    and start: "funas_term t \<subseteq> to_signature A"
    and terms: "\<And>p r u. (p,r,u) \<in> set w_seq \<Longrightarrow> funas_term u \<subseteq> to_signature A"
  shows "\<not> trs_outermost_terminates A R"
proof -
  have ok: "certify_integrated_cert_problem False (FP_TRS_input Outermost Rs)
      Termination (Decision False)
      (Inl (TRS_Nontermination_Proof (TRS_Loop (TRS_loop_prf t w_seq mu C)))) = Certified"
    using accepted by (simp add: certify_proof_integrated_def parsed bind2'_def)
  show ?thesis by (rule trs_outermost_integrated_NO[OF rules ok ctxt subst start terms])
qed

ML \<open>
  val results = @{thms outermost_step_iff trs_outermost_terminates_iff_signature
    trs_outermost_nonterminates_iff_signature
    trs_outermost_loop_checker_NO trs_outermost_integrated_YES trs_outermost_integrated_NO
    trs_outermost_serialized_YES trs_outermost_serialized_NO}
  val _ = if Thm_Deps.has_skip_proof results then error "Outermost: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Outermost integrated oracle dependencies: " ^ commas names)
\<close>
end
