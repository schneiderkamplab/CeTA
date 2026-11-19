theory TRS_Standard_Equivalence
  imports Category_Properties.TRS_Standard_Properties TRS_Representation
begin

lemma trs_standard_terminates_iff_signature:
  "trs_standard_terminates A R \<longleftrightarrow> SN (sig_step (to_signature A) (rstep (to_rules R)))"
proof -
  have chains: "(\<exists>ts. \<forall>i. fo_step A R (ts i) (ts (Suc i))) \<longleftrightarrow>
    (\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R)))"
  proof
    assume "\<exists>ts. \<forall>i. fo_step A R (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. fo_step A R (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R))"
      by (intro exI[of _ "to_term \<circ> ts"]) (simp add: standard_step_iff)
  next
    assume "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R))"
    then obtain ts where "\<forall>i. (ts i, ts (Suc i)) \<in> sig_step (to_signature A) (rstep (to_rules R))" by blast
    then show "\<exists>ts. \<forall>i. fo_step A R (ts i) (ts (Suc i))"
      by (intro exI[of _ "from_term \<circ> ts"]) (simp add: standard_step_iff)
  qed
  show ?thesis unfolding trs_standard_terminates_def no_infinite_steps_def SN_defs using chains by blast
qed

text \<open>Signature extension removes the restriction on terms. Its existing
proof also handles rules with variable left sides or extra right variables.\<close>
theorem trs_standard_terminates_iff:
  assumes "trs_problem A R"
  shows "trs_standard_terminates A R \<longleftrightarrow> SN (rstep (to_rules R))"
  unfolding trs_standard_terminates_iff_signature
  using SN_sig_rstep_imp_SN_rstep[OF correct_rules[OF assms]]
    SN_subset[of "rstep (to_rules R)" "sig_step (to_signature A) (rstep (to_rules R))"]
  unfolding sig_step_def by blast

theorem trs_standard_terminates_iff_on:
  assumes problem: "trs_problem A R"
  shows "trs_standard_terminates A R \<longleftrightarrow>
    SN_on (rstep (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
proof
  assume "trs_standard_terminates A R"
  then have "SN (rstep (to_rules R))"
    using trs_standard_terminates_iff[OF problem] by blast
  then show "SN_on (rstep (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
    unfolding SN_defs by blast
next
  assume "SN_on (rstep (to_rules R)) {t. funas_term t \<subseteq> to_signature A}"
  then have "SN (sig_step (to_signature A) (rstep (to_rules R)))"
    unfolding SN_defs sig_step_def by blast
  then show "trs_standard_terminates A R"
    by (simp add: trs_standard_terminates_iff_signature)
qed

corollary trs_standard_nonterminates_iff:
  "trs_problem A R \<Longrightarrow>
   (\<not> trs_standard_terminates A R) \<longleftrightarrow> \<not> SN (rstep (to_rules R))"
  by (simp add: trs_standard_terminates_iff)
end
