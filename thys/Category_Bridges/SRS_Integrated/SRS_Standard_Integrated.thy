theory SRS_Standard_Integrated
  imports Category_Specification_Bridges.SRS_Unary_Encoding
    Category_Integrated_Base.Category_Integrated_Base
begin

text \<open>Each rule may use its own tail variable. Both sides must share that
variable. This is the string category's representation condition, including
empty words, rather than an additional termination hypothesis.\<close>
definition represents_words where
  "represents_words T R \<longleftrightarrow>
    (\<forall>l r. (l,r) \<in> T \<longrightarrow> (\<exists>u v x. (u,v) \<in> R \<and>
      l = string_to_term (Var x) u \<and> r = string_to_term (Var x) v)) \<and>
    (\<forall>u v. (u,v) \<in> R \<longrightarrow> (\<exists>x.
      (string_to_term (Var x) u,string_to_term (Var x) v) \<in> T))"

lemma word_tail_subst:
  "string_to_term (Var x) w \<cdot> sigma = string_to_term (sigma x) w"
  by (induct w) auto

lemma represented_step_subset:
  assumes rep: "represents_words T R"
  shows "Trs.rstep T \<subseteq> Trs.rstep (word_rules x R)"
proof
  fix st assume "st \<in> Trs.rstep T"
  then obtain C l r sigma where lr: "(l,r) \<in> T"
    and st: "st = (C\<langle>l \<cdot> sigma\<rangle>, C\<langle>r \<cdot> sigma\<rangle>)"
    by (cases st) (auto elim: Trs.rstep.cases)
  obtain u v y where uv: "(u,v) \<in> R" and eq:
    "l = string_to_term (Var y) u" "r = string_to_term (Var y) v"
    using rep lr unfolding represents_words_def by blast
  have rule: "(string_to_term (Var x) u,string_to_term (Var x) v) \<in> word_rules x R"
    using uv unfolding word_rules_def by blast
  show "st \<in> Trs.rstep (word_rules x R)"
    using rstep_ctxt[OF rstep_subst[OF rstep_rule[OF rule], of "\<lambda>_. sigma y"], of C]
    by (simp add: st eq word_tail_subst)
qed

lemma represented_words_iff:
  assumes rep: "represents_words T R"
  shows "srs_standard_terminates R \<longleftrightarrow> SN (Trs.rstep T)"
proof
  assume "srs_standard_terminates R"
  then show "SN (Trs.rstep T)"
    using srs_standard_unary_iff represented_step_subset[OF rep]
    by (meson SN_subset)
next
  assume sn: "SN (Trs.rstep T)"
  have "srs_of_trs T = R"
    using rep unfolding represents_words_def srs_of_trs_def
    by (auto; metis word_roundtrip word_unary)
  then show "srs_standard_terminates R"
    using srs_of_trs_SN[OF sn] by (simp add: srs_standard_terminates_iff)
qed

theorem srs_standard_integrated_decision:
  assumes rules: "represents_words (set Rs) R"
    and accepted: "certify_integrated_cert_problem False
      (Inn_TRS_input No_Strategy Rs []) Termination (Decision b) certificate = Certified"
  shows "b \<longleftrightarrow> srs_standard_terminates R"
  using certify_integrated_cert_problem_sound[OF accepted]
  by (simp add: desired_property_def default_nfs_flag_def SN_qrel_def
      represented_words_iff[OF rules])

corollary srs_standard_integrated_YES:
  "represents_words (set Rs) R \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
     Termination (Decision True) certificate = Certified \<Longrightarrow>
   srs_standard_terminates R"
  using srs_standard_integrated_decision[where b=True] by blast

corollary srs_standard_integrated_NO:
  "represents_words (set Rs) R \<Longrightarrow>
   certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
     Termination (Decision False) certificate = Certified \<Longrightarrow>
   \<not> srs_standard_terminates R"
  using srs_standard_integrated_decision[where b=False] by blast

theorem srs_standard_serialized_decision:
  assumes rules: "represents_words (set Rs) R"
    and parsed: "parse_combined_integrated_cert_problem None None None text =
      Right (Inn_TRS_input No_Strategy Rs [], Termination, Decision b, certificate)"
    and accepted: "certify_proof_integrated False None None None text = Certified"
  shows "b \<longleftrightarrow> srs_standard_terminates R"
proof -
  have "certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
      Termination (Decision b) certificate = Certified"
    by (rule integrated_serialized_acceptance[OF parsed accepted])
  then show ?thesis by (rule srs_standard_integrated_decision[OF rules])
qed

ML \<open>
  val results = @{thms srs_standard_integrated_decision srs_standard_integrated_YES
    srs_standard_integrated_NO srs_standard_serialized_decision}
  val _ = if Thm_Deps.has_skip_proof results then error "SRS bridge: admitted proof" else ()
  val names = Thm_Deps.all_oracles results
    |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("SRS integrated oracle dependencies: " ^ commas names)
\<close>
end
