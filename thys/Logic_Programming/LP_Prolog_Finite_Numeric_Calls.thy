theory LP_Prolog_Finite_Numeric_Calls
 imports LP_Prolog_Finite_Observed_Calls LP_Prolog_Numeric_Component
begin

lemma lpp_finite_numeric_observation_integer:
  assumes checked: "lpp_check_numeric_observation K observation test"
    and known: "lpp_integer_known K eta"
    and observed: "lpp_evaluation_observation_holds lpp_finite_evaluation_result eta observation"
  shows "lpp_numeric_observation_holds eta observation"
proof (cases observation)
  case (LPPOEvaluation e t)
  obtain comparison a b where test: "test=(comparison,a,b)" by (cases test) auto
  obtain rho where typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    using lpp_integer_known_environment[OF known] by blast
  have expression: "e=lpp_expression_term b" and check: "lpp_expression_check K b"
    using checked by (auto simp: LPPOEvaluation test)
  have integer: "lpp_integer_evaluation (lp_ieval e eta) (lpp_expression_value b rho)"
    unfolding expression by (rule lpp_expression_evaluation[OF check typed])
  show ?thesis using observed
    by (simp only: LPPOEvaluation lpp_evaluation_observation_holds.simps
      lpp_numeric_observation_holds.simps lpp_finite_evaluation_integer[OF integer])
qed (use observed in auto)

lemma lpp_finite_numeric_call_row_types:
  fixes P :: "'v lpp_success_clause list" and receipt :: "'v lpp_numeric_call_receipt"
  assumes checked: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    and transfer: "lpp_check_transfer_program T P receipts"
    and guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs"
    and facts: "list_all (lpp_guarded_success P lpp_finite_evaluation_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
  shows "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
  by (rule lpp_check_path_types_sound[OF transfer _ guards facts lpp_finite_evaluation_integer_contract])
    (use checked in \<open>auto simp: lpp_check_numeric_call_row_def Let_def\<close>)

lemma lpp_finite_numeric_call_row_observations:
  assumes checked: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
    and observed: "list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result eta) os"
  shows "list_all (lpp_numeric_observation_holds eta) os"
proof -
  let ?K = "map lpp_transfer_variable (lppnc_facts receipt)"
  have tests: "list_all2 (lpp_check_numeric_observation ?K)
    (filter lpp_numeric_constraint_observation os) (lppnc_tests receipt)"
    using checked by (auto simp: lpp_check_numeric_call_row_def lpp_check_numeric_path_def Let_def)
  have typed: "\<exists>test. lpp_check_numeric_observation ?K observation test"
    if member: "observation\<in>set (filter lpp_numeric_constraint_observation os)" for observation
  proof -
    obtain i where bound: "i<length (filter lpp_numeric_constraint_observation os)"
      and item: "observation=filter lpp_numeric_constraint_observation os!i"
      using member by (auto simp only: in_set_conv_nth)
    have check: "lpp_check_numeric_observation ?K observation (lppnc_tests receipt!i)"
      using list_all2_nthD[OF tests bound] by (simp only: item)
    show ?thesis using check by blast
  qed
  have each: "lpp_numeric_observation_holds eta observation" if member: "observation\<in>set os" for observation
  proof (cases "lpp_numeric_constraint_observation observation")
    case True
    have member': "observation\<in>set (filter lpp_numeric_constraint_observation os)"
      using True member by simp
    obtain numeric_test where check: "lpp_check_numeric_observation ?K observation numeric_test"
      using typed[OF member'] by blast
    show ?thesis by (rule lpp_finite_numeric_observation_integer[OF check known])
      (use observed member in \<open>auto simp: list_all_iff\<close>)
  next
    case False
    show ?thesis using False observed member by (cases observation) (auto simp: list_all_iff)
  qed
  show ?thesis using each by (simp add: list_all_iff)
qed

theorem lpp_checked_finite_numeric_calls_SN:
  fixes P :: "'v lpp_success_clause list" and row_receipts :: "'v lpp_numeric_call_receipt list"
  assumes checked: "lpp_check_numeric_calls T coordinates locations system D row_receipts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and child: "SN (LPPIntegerLTS.transition system)"
  shows "SN (lpp_finite_observed_calls (set D) P)"
proof (rule lpp_typed_relational_simulation_SN[where
    T="\<lambda>a. \<exists>pre. lpp_numeric_call coordinates a pre" and
    rep="\<lambda>a s. \<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_numeric_call coordinates a pre" and S="LPPIntegerLTS.transition system"])
  fix a target assume step: "(a,target)\<in>lpp_finite_observed_calls (set D) P"
  obtain h ps b gs os sigma eta where member: "((h,ps,b,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs"
    and observations: "list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result eta) os"
    and facts: "list_all (lpp_guarded_success P lpp_finite_evaluation_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "target=lpp_success_atom_eval b eta"
    using step by (auto simp: lpp_finite_observed_calls_def)
  obtain receipt where row: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    using lpp_numeric_calls_row[OF checked member] by blast
  have known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
    by (rule lpp_finite_numeric_call_row_types[OF row transfer guards facts])
  show "\<exists>pre. lpp_numeric_call coordinates target pre"
    using lpp_numeric_call_row_output[OF row known] target by simp
next
  fix a assume typed: "\<exists>pre. lpp_numeric_call coordinates a pre"
  obtain pre where represented: "lpp_numeric_call coordinates a pre" using typed by blast
  have sn: "SN_on (LPPIntegerLTS.transition system)
    {State (lpp_integer_assignment pre) (locations (fst a))}"
    by (rule SN_on_subset2[OF subset_UNIV child])
  show "\<exists>s. (\<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_numeric_call coordinates a pre) \<and> SN_on (LPPIntegerLTS.transition system) {s}"
    using represented sn by blast
next
  fix a target s
  assume step: "(a,target)\<in>lpp_finite_observed_calls (set D) P"
    and typed: "\<exists>pre. lpp_numeric_call coordinates a pre"
    and represented: "\<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_numeric_call coordinates a pre"
  obtain pre where s: "s=State (lpp_integer_assignment pre) (locations (fst a))"
    and pre: "lpp_numeric_call coordinates a pre" using represented by blast
  obtain h ps b gs os sigma eta where member: "((h,ps,b,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs"
    and observations: "list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result eta) os"
    and facts: "list_all (lpp_guarded_success P lpp_finite_evaluation_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "target=lpp_success_atom_eval b eta"
    using step by (auto simp: lpp_finite_observed_calls_def)
  obtain receipt where row: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    using lpp_numeric_calls_row[OF checked member] by blast
  have known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
    by (rule lpp_finite_numeric_call_row_types[OF row transfer guards facts])
  obtain post where edge: "(State (lpp_integer_assignment pre) (locations (fst a)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system"
    and post: "lpp_numeric_call coordinates (lpp_success_atom_eval b eta) post"
    using lpp_checked_numeric_call_step[OF row known lpp_finite_numeric_call_row_observations[OF row known observations] matching pre] by blast
  show "\<exists>t. (s,t)\<in>LPPIntegerLTS.transition system \<and>
    (\<exists>pre. t=State (lpp_integer_assignment pre) (locations (fst target)) \<and>
      lpp_numeric_call coordinates target pre)"
    using edge post by (auto simp: s target lpp_success_atom_eval_def)
qed

theorem lpp_check_finite_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_numeric_call_receipt list"
  assumes checked: "lpp_check_numeric_component T coordinates locations system_impl D row_receipts child_proof"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_finite_observed_calls (set D) P)"
proof (rule lpp_checked_finite_numeric_calls_SN[OF _ transfer])
  show "lpp_check_numeric_calls T coordinates locations (lts_of system_impl) D row_receipts"
    using checked by (simp add: lpp_check_numeric_component_def)
  have entries: "LTS.source ` transition_rules (lts_of system_impl) \<subseteq> lts.initial (lts_of system_impl)"
    using checked by (auto simp: lpp_check_numeric_component_def list_all_iff)
  have child: "isOK (ia4_check_termination system_impl child_proof)"
    using checked by (simp add: lpp_check_numeric_component_def)
  have terminates: "LPPIntegerLTS.lts_termination (lts_of system_impl)"
    by (rule ia4_check_termination_sound[OF child])
  show "SN (LPPIntegerLTS.transition (lts_of system_impl))"
    by (rule lpp_all_numeric_entries_SN[OF entries terminates])
qed

ML \<open>
val checked = [@{thm lpp_checked_finite_observed_call},
  @{thm lpp_finite_numeric_call_row_types},
  @{thm lpp_finite_numeric_call_row_observations},
  @{thm lpp_check_finite_numeric_component_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite numeric component checker dependency" else ();
\<close>
end
