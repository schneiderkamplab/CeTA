theory LP_Prolog_Observed_Calls
  imports LP_Prolog_Guarded_Receipt LP_Prolog_Numeric_Row_Check
begin

type_synonym 'v lpp_observed_triple = "'v lpp_guarded_triple * 'v lpp_numeric_observation list"

fun lpp_numeric_observation_substitute where
  "lpp_numeric_observation_substitute (LPPOGround t) mu = LPPOGround (t\<cdot>mu)"
| "lpp_numeric_observation_substitute (LPPOEquation a b) mu = LPPOEquation (a\<cdot>mu) (b\<cdot>mu)"
| "lpp_numeric_observation_substitute (LPPOShape G shape t) mu = LPPOShape G shape (t\<cdot>mu)"
| "lpp_numeric_observation_substitute (LPPOInteger t) mu = LPPOInteger (t\<cdot>mu)"
| "lpp_numeric_observation_substitute (LPPOEvaluation e t) mu = LPPOEvaluation (e\<cdot>mu) (t\<cdot>mu)"
| "lpp_numeric_observation_substitute (LPPOComparison c a b) mu = LPPOComparison c (a\<cdot>mu) (b\<cdot>mu)"

lemma lpp_numeric_observation_substitute_eval:
  "lpp_numeric_observation_holds eta (lpp_numeric_observation_substitute observation mu) =
    lpp_numeric_observation_holds (\<lambda>x. lp_ieval (mu x) eta) observation"
  by (cases observation) (simp_all add: lp_ieval_finite_subst)

definition lpp_observed_calls ::
  "'v lpp_observed_triple set \<Rightarrow> 'v lpp_success_clause list \<Rightarrow> 'w lpp_success_iatom rel" where
  "lpp_observed_calls D P = {(a,lpp_success_atom_eval b eta) |a h ps b gs observations sigma eta.
    ((h,ps,b,gs),observations)\<in>D \<and>
    lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta \<and>
    list_all (lpp_success_guard_holds lpp_integer_result eta) gs \<and>
    list_all (lpp_numeric_observation_holds eta) observations \<and>
    list_all (lpp_guarded_success P lpp_integer_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)}"

lemma lpp_observed_call_guarded:
  "(a,b)\<in>lpp_observed_calls D P \<Longrightarrow>
    (a,b)\<in>lpp_guarded_calls (fst ` D) P lpp_integer_result"
proof -
  assume step: "(a,b)\<in>lpp_observed_calls D P"
  obtain h ps c gs os sigma eta where member: "((h,ps,c,gs),os)\<in>D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and models: "list_all (lpp_guarded_success P lpp_integer_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and endpoint: "b=lpp_success_atom_eval c eta"
    using step by (auto simp: lpp_observed_calls_def)
  have projected: "(h,ps,c,gs)\<in>fst ` D" using member by force
  show ?thesis unfolding lpp_guarded_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ c],
      rule exI[of _ gs], rule exI[of _ sigma], rule exI[of _ eta])
    using projected matching guards models endpoint
    by (auto simp: lpp_success_iatom_subst_def)
qed

lemma lpp_observed_call_structural:
  "(a,b)\<in>lpp_observed_calls D P \<Longrightarrow>
    (lpp_lift_iatom a,lpp_lift_iatom b)\<in>
      lp_triple_calls (lpp_erase_triples (fst ` D)) (lpp_erase_success P)"
  by (rule lpp_guarded_call_erases) (rule lpp_observed_call_guarded)

definition lpp_check_observed_call where
  "lpp_check_observed_call D facts guards observations head call c bindings =
    (c<length D \<and> (case D!c of ((h,ps,b,gs),os) \<Rightarrow>
      let mu=lpc_triple_model_subst (lpp_lift_atom head) bindings in
      lpp_success_atom_subst h mu=head \<and> lpp_success_atom_subst b mu=call \<and>
      list_all (\<lambda>p. lpp_success_atom_subst p mu\<in>set facts) ps \<and>
      list_all (\<lambda>g. lpp_success_guard_subst g mu\<in>set guards) gs \<and>
      list_all (\<lambda>observation. lpp_numeric_observation_substitute observation mu\<in>set observations) os))"

theorem lpp_checked_observed_call:
  assumes checked: "lpp_check_observed_call D facts guards observations head call c bindings"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval head eta"
    and facts: "\<And>b. b\<in>set facts \<Longrightarrow> lpp_guarded_success P lpp_integer_result (lpp_success_atom_eval b eta)"
    and guards: "\<And>g. g\<in>set guards \<Longrightarrow> lpp_success_guard_holds lpp_integer_result eta g"
    and observations: "\<And>observation. observation\<in>set observations \<Longrightarrow> lpp_numeric_observation_holds eta observation"
  shows "(a,lpp_success_atom_eval call eta)\<in>lpp_observed_calls (set D) P"
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
  have models: "list_all (lpp_guarded_success P lpp_integer_result)
    (map (\<lambda>p. lpp_success_atom_eval p (\<lambda>x. lp_ieval (?mu x) eta)) ps)"
    using prefix facts by (auto simp: list_all_iff lpp_success_atom_subst_eval[symmetric])
  have tests: "list_all (lpp_success_guard_holds lpp_integer_result (\<lambda>x. lp_ieval (?mu x) eta)) gs"
    using tested guards by (auto simp: list_all_iff lpp_success_guard_subst_eval[symmetric])
  have obs: "list_all (lpp_numeric_observation_holds (\<lambda>x. lp_ieval (?mu x) eta)) os"
    using observed observations by (auto simp: list_all_iff lpp_numeric_observation_substitute_eval[symmetric])
  have head_eval: "lpp_success_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta)=lpp_success_atom_eval head eta"
    using arg_cong[OF head, of "\<lambda>a. lpp_success_atom_eval a eta"]
    by (simp only: lpp_success_atom_subst_eval)
  have match: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta)"
    using matching by (simp only: head_eval)
  have call_eval: "lpp_success_atom_eval b (\<lambda>x. lp_ieval (?mu x) eta)=lpp_success_atom_eval call eta"
    using arg_cong[OF call, of "\<lambda>b. lpp_success_atom_eval b eta"]
    by (simp only: lpp_success_atom_subst_eval)
  show ?thesis unfolding lpp_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ b],
      rule exI[of _ gs], rule exI[of _ os], rule exI[of _ sigma],
      rule exI[of _ "\<lambda>x. lp_ieval (?mu x) eta"])
    using member models tests obs match call_eval by (simp only: call_eval HOL.simp_thms)
qed

ML \<open>
val checked = [@{thm lpp_checked_observed_call}, @{thm lpp_observed_call_structural}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted observed-call receipt dependency" else ();
\<close>
end
