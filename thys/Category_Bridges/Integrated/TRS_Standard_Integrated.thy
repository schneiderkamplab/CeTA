theory TRS_Standard_Integrated
  imports Category_Specification_Bridges.TRS_Standard_Equivalence
    Category_Integrated_Base.Category_Integrated_Base
begin

text \<open>The concrete integrated checker supplies its own module-correctness
proofs. These statements cover either decision on the exact Standard input.
The string-level statement exposes the remaining parser/input correspondence
premise rather than assuming that an arbitrary certificate names the benchmark.\<close>

theorem trs_standard_integrated_decision:
  assumes problem: "trs_problem A R"
    and rules: "set Rs = to_rules R"
    and accepted: "certify_integrated_cert_problem False
      (Inn_TRS_input No_Strategy Rs []) Termination (Decision b) certificate = Certified"
  shows "b \<longleftrightarrow> trs_standard_terminates A R"
  using certify_integrated_cert_problem_sound[OF accepted]
  by (simp add: desired_property_def default_nfs_flag_def SN_qrel_def rules
      trs_standard_terminates_iff[OF problem])

corollary trs_standard_integrated_YES:
  "trs_problem A R \<Longrightarrow> set Rs = to_rules R \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
     Termination (Decision True) certificate = Certified \<Longrightarrow>
   trs_standard_terminates A R"
  using trs_standard_integrated_decision[where b=True] by blast

corollary trs_standard_integrated_NO:
  "trs_problem A R \<Longrightarrow> set Rs = to_rules R \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
     Termination (Decision False) certificate = Certified \<Longrightarrow>
   \<not> trs_standard_terminates A R"
  using trs_standard_integrated_decision[where b=False] by blast

ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms trs_standard_integrated_decision
    trs_standard_integrated_YES trs_standard_integrated_NO}
    then error "TRS Standard integrated bridge: admitted proof" else ()
\<close>
end
