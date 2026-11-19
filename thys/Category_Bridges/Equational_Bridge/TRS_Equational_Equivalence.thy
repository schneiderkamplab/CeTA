theory TRS_Equational_Equivalence
  imports Category_Properties.TRS_Equational_Properties
    Category_Specification_Bridges.TRS_Relative_Equivalence AC_TRS.AC_Rewriting
begin
lemma equational_axioms_translation:
  "to_rules (equational_axioms assoc_symbols comm_symbols) = AC_trs assoc_symbols comm_symbols"
proof
  show "to_rules (equational_axioms assoc_symbols comm_symbols) \<subseteq> AC_trs assoc_symbols comm_symbols"
    by (auto simp: to_rules_def equational_axioms_def AC_trs_def A_trs_def A_rules_def C_rules_def)
  show "AC_trs assoc_symbols comm_symbols \<subseteq> to_rules (equational_axioms assoc_symbols comm_symbols)"
  proof
    fix p assume p: "p \<in> AC_trs assoc_symbols comm_symbols"
    have rev: "(from_term (fst p),from_term (snd p)) \<in> equational_axioms assoc_symbols comm_symbols"
      using p by (cases p; auto simp: equational_axioms_def AC_trs_def A_trs_def A_rules_def C_rules_def)
    have "(to_term (from_term (fst p)),to_term (from_term (snd p))) \<in> to_rules (equational_axioms assoc_symbols comm_symbols)"
      unfolding to_rules_def
      by (intro CollectI exI[of _ "from_term (fst p)"] exI[of _ "from_term (snd p)"])
        (simp add: rev)
    then show "p \<in> to_rules (equational_axioms assoc_symbols comm_symbols)" by simp
  qed
qed
lemma equational_step_eq_relative:
  "equational_step A R assoc_symbols comm_symbols = relative_step A R (equational_axioms assoc_symbols comm_symbols)"
  by (intro ext) (simp add: equational_step_def equational_conversion_def relative_step_def)
lemma equational_step_iff_ranked:
  "equational_step A R assoc_symbols comm_symbols s t \<longleftrightarrow>
    (to_term s,to_term t) \<in> relto (sig_step (to_signature A) (rstep (to_rules R)))
      (sig_step (to_signature A) (acrstep assoc_symbols comm_symbols))"
  using relative_step_iff[of A R "equational_axioms assoc_symbols comm_symbols" s t]
  by (simp add: equational_step_eq_relative equational_axioms_translation)
theorem trs_equational_terminates_iff_ranked:
  "trs_equational_terminates A R assoc_symbols comm_symbols \<longleftrightarrow>
    SN_rel (sig_step (to_signature A) (rstep (to_rules R)))
      (sig_step (to_signature A) (acrstep assoc_symbols comm_symbols))"
  using trs_relative_terminates_iff_signature[of A R "equational_axioms assoc_symbols comm_symbols"]
  by (simp add: trs_equational_terminates_def trs_relative_terminates_def
      equational_step_eq_relative equational_axioms_translation)
lemma equational_unrestricted_relation:
  "aoc_rewriting.relaoc assoc_symbols comm_symbols R = relto (rstep R) (acrstep assoc_symbols comm_symbols)"
  by (simp add: aoc_rewriting.relaoc_def conversion_def symcl_acstep)
lemma equational_termination_transfer:
  assumes "SN (aoc_rewriting.relaoc assoc_symbols comm_symbols (to_rules R))"
  shows "trs_equational_terminates A R assoc_symbols comm_symbols"
  using ordinary_relative_implies_ranked[of R "equational_axioms assoc_symbols comm_symbols" A] assms
  by (simp add: equational_unrestricted_relation SN_rel_defs equational_axioms_translation
    trs_equational_terminates_def trs_relative_terminates_def equational_step_eq_relative)
lemma equational_contains_standard:
  "fo_step A R s t \<Longrightarrow> equational_step A R assoc_symbols comm_symbols s t"
  by (auto simp: equational_step_def equational_conversion_def intro: finite_steps.zero)
lemma ordinary_nontermination_equational:
  "\<not> trs_standard_terminates A R \<Longrightarrow> \<not> trs_equational_terminates A R assoc_symbols comm_symbols"
  by (auto simp: trs_standard_nontermination_iff trs_equational_nontermination_iff
      intro: equational_contains_standard)

theorem trs_equational_nonterminates_iff_ranked:
  "\<not> trs_equational_terminates A R assoc_symbols comm_symbols \<longleftrightarrow>
    \<not> SN_rel (sig_step (to_signature A) (rstep (to_rules R)))
      (sig_step (to_signature A) (acrstep assoc_symbols comm_symbols))"
  by (simp add: trs_equational_terminates_iff_ranked)

ML \<open>
  val results = @{thms equational_axioms_translation equational_step_iff_ranked
    trs_equational_terminates_iff_ranked trs_equational_nonterminates_iff_ranked
    equational_termination_transfer ordinary_nontermination_equational}
  val _ = if Thm_Deps.has_skip_proof results then error "Equational: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Equational equivalence oracle dependencies: " ^ commas names)
\<close>
end
