theory LP_Prolog_Finite_Observed_Calls
 imports LP_Prolog_Evaluation_Context LP_Prolog_Finite_Evaluation
begin

definition lpp_finite_observed_calls ::
  "'v lpp_observed_triple set \<Rightarrow> 'v lpp_success_clause list \<Rightarrow> 'w lpp_success_iatom rel" where
  "lpp_finite_observed_calls D P = {(a,lpp_success_atom_eval b eta) |a h ps b gs observations sigma eta.
    ((h,ps,b,gs),observations)\<in>D \<and>
    lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta \<and>
    list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs \<and>
    list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result eta) observations \<and>
    list_all (lpp_guarded_success P lpp_finite_evaluation_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)}"

theorem lpp_checked_finite_observed_call:
  assumes checked: "lpp_check_observed_call D facts guards observations head call c bindings"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval head eta"
    and facts: "\<And>b. b\<in>set facts \<Longrightarrow> lpp_guarded_success P lpp_finite_evaluation_result (lpp_success_atom_eval b eta)"
    and guards: "\<And>g. g\<in>set guards \<Longrightarrow> lpp_success_guard_holds lpp_finite_evaluation_result eta g"
    and observations: "\<And>observation. observation\<in>set observations \<Longrightarrow> lpp_evaluation_observation_holds lpp_finite_evaluation_result eta observation"
  shows "(a,lpp_success_atom_eval call eta)\<in>lpp_finite_observed_calls (set D) P"
proof -
  let ?mu = "lpc_triple_model_subst (lpp_lift_atom head) bindings"
  obtain h ps b gs os where row: "D!c=((h,ps,b,gs),os)" by (cases "D!c") auto
  have index: "c<length D" and head: "lpp_success_atom_subst h ?mu=head"
    and call: "lpp_success_atom_subst b ?mu=call"
    and prefix: "list_all (\<lambda>p. lpp_success_atom_subst p ?mu\<in>set facts) ps"
    and tested: "list_all (\<lambda>g. lpp_success_guard_subst g ?mu\<in>set guards) gs"
    and observed: "list_all (\<lambda>observation. lpp_numeric_observation_substitute observation ?mu\<in>set observations) os"
    using checked by (auto simp: lpp_check_observed_call_def row Let_def)
  have member: "((h,ps,b,gs),os)\<in>set D" using nth_mem[OF index] row by simp
  have models: "list_all (lpp_guarded_success P lpp_finite_evaluation_result)
    (map (\<lambda>p. lpp_success_atom_eval p (\<lambda>x. lp_ieval (?mu x) eta)) ps)"
    using prefix facts by (auto simp: list_all_iff lpp_success_atom_subst_eval[symmetric])
  have tests: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result (\<lambda>x. lp_ieval (?mu x) eta)) gs"
    using tested guards by (auto simp: list_all_iff lpp_success_guard_subst_eval[symmetric])
  have obs: "list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result (\<lambda>x. lp_ieval (?mu x) eta)) os"
    using observed observations by (auto simp: list_all_iff lpp_evaluation_observation_substitute[symmetric])
  have head_eval: "lpp_success_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta)=lpp_success_atom_eval head eta"
    using arg_cong[OF head, of "\<lambda>a. lpp_success_atom_eval a eta"]
    by (simp only: lpp_success_atom_subst_eval)
  have match: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta)"
    using matching by (simp only: head_eval)
  have call_eval: "lpp_success_atom_eval b (\<lambda>x. lp_ieval (?mu x) eta)=lpp_success_atom_eval call eta"
    using arg_cong[OF call, of "\<lambda>b. lpp_success_atom_eval b eta"]
    by (simp only: lpp_success_atom_subst_eval)
  show ?thesis unfolding lpp_finite_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ b],
      rule exI[of _ gs], rule exI[of _ os], rule exI[of _ sigma],
      rule exI[of _ "\<lambda>x. lp_ieval (?mu x) eta"])
    using member models tests obs match call_eval by (simp only: call_eval HOL.simp_thms)
qed

end
