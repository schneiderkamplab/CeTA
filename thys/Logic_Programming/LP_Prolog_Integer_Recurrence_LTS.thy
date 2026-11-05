theory LP_Prolog_Integer_Recurrence_LTS
  imports LP_Prolog_Integer_Recurrence_Valuation
begin

definition lpp_recurrence_state_values where
  "lpp_recurrence_state_values s x = IA.to_int (valuation s (x,IA.IntT))"

lemma lpp_recurrence_lts_step:
  assumes rules: "transition_rules system = {Transition loc loc
      (lpp_recurrence_relation_formula xs ops outputs)}"
    and lengths: "length xs=length outputs"
    and edge: "(s,t)\<in>LPPIntegerLTS.transition system"
  shows "(lpp_recurrence_state_values s,lpp_recurrence_state_values t)
    \<in>lpp_recurrence_integer_relation xs ops outputs"
proof -
  obtain gamma where source: "IA4.assignment (valuation s)"
    and target: "IA4.assignment (valuation t)"
    and local_typed: "IA4.assignment gamma"
    and formula: "IA4.satisfies (LPPIntegerLTS.pre_post_inter (valuation s) (valuation t) gamma)
      (lpp_recurrence_relation_formula xs ops outputs)"
    using edge rules by (auto elim!: LPPIntegerLTS.mem_transitionE)
  let ?delta = "LPPIntegerLTS.pre_post_inter (valuation s) (valuation t) gamma"
  have typed: "IA4.assignment ?delta" using source target local_typed by simp
  have project: "(\<lambda>x. IA.to_int (?delta (x,IA.IntT))) =
      lpp_trans_integer (lpp_recurrence_state_values s) (lpp_recurrence_state_values t)
        (\<lambda>x. IA.to_int (gamma (x,IA.IntT)))"
    by (rule ext, rename_tac x, case_tac x) (simp_all add: lpp_recurrence_state_values_def)
  have exact: "IA4.satisfies (lpp_integer_assignment
      (lpp_trans_integer (lpp_recurrence_state_values s) (lpp_recurrence_state_values t)
        (\<lambda>x. IA.to_int (gamma (x,IA.IntT)))))
      (lpp_recurrence_relation_formula xs ops outputs)"
    using formula lpp_recurrence_relation_arbitrary_valuation[OF typed,
      where xs=xs and ops=ops and outputs=outputs] by (simp only: project)
  show ?thesis using exact
    by (simp add: lpp_recurrence_integer_relation_def lpp_recurrence_relation_formula_exact[OF lengths])
qed

lemma lpp_recurrence_lts_nontermination:
  assumes rules: "transition_rules system = {Transition loc loc
      (lpp_recurrence_relation_formula xs ops outputs)}"
    and lengths: "length xs=length outputs"
    and child: "\<not>LPPIntegerLTS.lts_termination system"
  shows "\<exists>rho. \<not>SN_on (lpp_recurrence_integer_relation xs ops outputs) {rho}"
proof -
  obtain s where no: "\<not>SN_on (LPPIntegerLTS.transition system) {s}"
    using child unfolding SN_on_def by blast
  let ?rep = "\<lambda>s rho. rho=lpp_recurrence_state_values s"
  have simulate: "\<exists>v. ?rep b v \<and>
      (u,v)\<in>(lpp_recurrence_integer_relation xs ops outputs)\<^sup>+"
    if "(a,b)\<in>LPPIntegerLTS.transition system" "?rep a u" for a b u
    using lpp_recurrence_lts_step[OF rules lengths that(1)] that(2)
    by (auto intro: r_into_trancl)
  have "\<not>SN_on (lpp_recurrence_integer_relation xs ops outputs)
      {lpp_recurrence_state_values s}"
    by (rule lp_source_nontermination_simulation[where rep="?rep", OF no _ simulate]) simp
  then show ?thesis by blast
qed

ML \<open>
val checked = [@{thm lpp_recurrence_lts_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted recurrence LTS inverse dependency" else ();
\<close>
end
