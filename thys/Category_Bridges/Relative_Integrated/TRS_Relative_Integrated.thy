theory TRS_Relative_Integrated
  imports TRS_Relative_Ranked_Loops
begin

text \<open>The finite declared signature is retained for the NO guard, including
unused declarations. This is an acceptance condition, not category validity.
YES needs no signature-extension condition.\<close>
definition relative_no_guard where
  "relative_no_guard F Ss =
    ((\<exists>f n. (f,n) \<in> set F \<and> n > 1) \<or>
     (\<forall>l r. (l,r) \<in> set Ss \<longrightarrow> vars_term r \<subseteq> vars_term l))"

lemma relative_no_guard_sound:
  assumes "set F = to_signature A" "set Ss = to_rules S" "relative_no_guard F Ss"
  shows "relative_extension_condition A S"
  using assms by (auto simp: relative_no_guard_def relative_extension_condition_def to_signature_def)

theorem trs_relative_integrated_YES:
  assumes strict: "set Rs = to_rules R" and weak: "set Ss = to_rules S"
    and accepted: "certify_integrated_cert_problem False
      (Inn_TRS_input No_Strategy Rs Ss) Termination (Decision True) certificate = Certified"
  shows "trs_relative_terminates A R S"
proof -
  have "SN_rel (Trs.rstep (to_rules R)) (Trs.rstep (to_rules S))"
    using certify_integrated_cert_problem_sound[OF accepted]
    by (simp add: desired_property_def default_nfs_flag_def SN_qrel_def strict weak)
  then show ?thesis by (rule ordinary_relative_implies_ranked)
qed

definition relative_ranked_certificate where
  "relative_ranked_certificate F certificate \<longleftrightarrow>
    (\<exists>s loop_steps sigma C. certificate =
      Inl (Relative_TRS_Nontermination_Proof (Rel_Loop (Rel_trs_loop_prf s loop_steps sigma C))) \<and>
      ranked_relative_loop_guard (set F) s loop_steps sigma C)"

text \<open>The bound checker validates either signature extension or a ranked
loop witness. No unrestricted-to-ranked implication is assumed.\<close>
definition relative_bound_accepts where
  "relative_bound_accepts F Rs Ss b certificate =
    ((b \<or> relative_no_guard F Ss \<or> relative_ranked_certificate F certificate) \<and>
     certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs Ss)
       Termination (Decision b) certificate = Certified)"

theorem trs_relative_bound_decision:
  assumes problem: "relative_problem A R S"
    and signature: "set F = to_signature A"
    and strict: "set Rs = to_rules R" and weak: "set Ss = to_rules S"
    and accepted: "relative_bound_accepts F Rs Ss b certificate"
  shows "b \<longleftrightarrow> trs_relative_terminates A R S"
proof (cases b)
  case True
  with accepted have "certify_integrated_cert_problem False
    (Inn_TRS_input No_Strategy Rs Ss) Termination (Decision True) certificate = Certified"
    by (simp add: relative_bound_accepts_def)
  from trs_relative_integrated_YES[OF strict weak this] True show ?thesis by simp
next
  case False
  with accepted have guard: "relative_no_guard F Ss \<or> relative_ranked_certificate F certificate"
    and checked: "certify_integrated_cert_problem False
      (Inn_TRS_input No_Strategy Rs Ss) Termination (Decision False) certificate = Certified"
    by (auto simp: relative_bound_accepts_def)
  show ?thesis
  proof (cases "relative_no_guard F Ss")
    case True
    have extension: "relative_extension_condition A S"
      by (rule relative_no_guard_sound[OF signature weak True])
    have "\<not> SN_rel (Trs.rstep (to_rules R)) (Trs.rstep (to_rules S))"
      using certify_integrated_cert_problem_sound[OF checked]
      by (simp add: desired_property_def default_nfs_flag_def SN_qrel_def strict weak)
    with trs_relative_terminates_iff[OF problem extension] False show ?thesis by blast
  next
    case no_extension: False
    obtain s loop_steps sigma C where cert: "certificate =
      Inl (Relative_TRS_Nontermination_Proof (Rel_Loop (Rel_trs_loop_prf s loop_steps sigma C)))"
      and ranked: "ranked_relative_loop_guard (set F) s loop_steps sigma C"
      using guard no_extension unfolding relative_ranked_certificate_def by blast
    have "\<not> SN_rel (sig_step (set F) (Trs.rstep (set Rs)))
      (sig_step (set F) (Trs.rstep (set Ss)))"
      by (rule relative_integrated_ranked_loop[OF checked[unfolded cert] ranked])
    then show ?thesis using False
      by (simp add: signature strict weak trs_relative_terminates_iff_signature)
  qed
qed

corollary trs_relative_bound_NO:
  assumes "relative_problem A R S" "set F = to_signature A"
    "set Rs = to_rules R" "set Ss = to_rules S"
    "relative_bound_accepts F Rs Ss False certificate"
  shows "\<not> trs_relative_terminates A R S"
  using trs_relative_bound_decision[OF assms] by simp

theorem trs_relative_serialized_decision:
  assumes problem: "relative_problem A R S"
    and signature: "set F = to_signature A"
    and strict: "set Rs = to_rules R" and weak: "set Ss = to_rules S"
    and guard: "b \<or> relative_no_guard F Ss \<or> relative_ranked_certificate F certificate"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (Inn_TRS_input No_Strategy Rs Ss, Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> trs_relative_terminates A R S"
proof -
  have "relative_bound_accepts F Rs Ss b certificate"
    using integrated_serialized_acceptance[OF parsed accepted] guard
    by (simp add: relative_bound_accepts_def)
  then show ?thesis by (rule trs_relative_bound_decision[OF problem signature strict weak])
qed

ML \<open>
  val checked = @{thms ranked_relative_loop_guard_finite relative_integrated_ranked_loop
    relative_no_guard_sound trs_relative_integrated_YES
    trs_relative_bound_decision trs_relative_bound_NO trs_relative_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof checked then error "Relative: admitted proof" else ()
  val names = Thm_Deps.all_oracles checked |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Relative integrated oracle dependencies: " ^ commas names)
\<close>
end
