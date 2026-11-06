theory LP_Prolog_Stable_Numeric_Calls
 imports LP_Prolog_Stable_Numeric_Call_Step
begin

definition lpp_check_stable_numeric_calls where
  "lpp_check_stable_numeric_calls T coordinates modes locations system D row_receipts =
    (length D=length row_receipts \<and>
      list_all (\<lambda>i. lpp_check_stable_numeric_call_row T coordinates modes locations system (D!i) (row_receipts!i)) [0..<length D])"

lemma lpp_stable_numeric_calls_row:
  assumes checked: "lpp_check_stable_numeric_calls T coordinates modes locations system D row_receipts"
    and member: "triple\<in>set D"
  shows "\<exists>receipt. lpp_check_stable_numeric_call_row T coordinates modes locations system triple receipt"
proof -
  obtain i where bound: "i<length D" and triple: "D!i=triple"
    using member by (auto simp: in_set_conv_nth)
  have "lpp_check_stable_numeric_call_row T coordinates modes locations system triple (row_receipts!i)"
    using checked bound triple by (auto simp: lpp_check_stable_numeric_calls_def list_all_iff)
  then show ?thesis by blast
qed

theorem lpp_checked_stable_numeric_calls_SN:
  fixes P :: "'v lpp_success_clause list" and row_receipts :: "'v lpp_stable_numeric_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_calls T coordinates modes locations system D row_receipts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and child: "SN (LPPIntegerLTS.transition system)"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof (rule lpp_typed_relational_simulation_SN[where
    T="\<lambda>a. \<exists>pre. lpp_stable_numeric_call operation coordinates modes a pre" and
    rep="\<lambda>a s. \<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_stable_numeric_call operation coordinates modes a pre" and S="LPPIntegerLTS.transition system"])
  fix a target assume step: "(a,target)\<in>lpp_stable_observed_calls operation (set D) P"
  obtain h ps b gs os sigma eta where member: "((h,ps,b,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation)) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "target=lpp_success_atom_eval b eta"
    using step by (auto simp: lpp_stable_observed_calls_def)
  obtain receipt where row: "lpp_check_stable_numeric_call_row T coordinates modes locations system ((h,ps,b,gs),os) receipt"
    using lpp_stable_numeric_calls_row[OF checked member] by blast
  have known: "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts receipt)) eta"
    by (rule lpp_stable_numeric_call_row_types[OF compatible row transfer guards facts])
  show "\<exists>pre. lpp_stable_numeric_call operation coordinates modes target pre"
    using lpp_stable_numeric_call_row_output[OF row known observations] target by simp
next
  fix a assume typed: "\<exists>pre. lpp_stable_numeric_call operation coordinates modes a pre"
  obtain pre where represented: "lpp_stable_numeric_call operation coordinates modes a pre" using typed by blast
  have sn: "SN_on (LPPIntegerLTS.transition system)
    {State (lpp_integer_assignment pre) (locations (fst a))}"
    by (rule SN_on_subset2[OF subset_UNIV child])
  show "\<exists>s. (\<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_stable_numeric_call operation coordinates modes a pre) \<and> SN_on (LPPIntegerLTS.transition system) {s}"
    using represented sn by blast
next
  fix a target s
  assume step: "(a,target)\<in>lpp_stable_observed_calls operation (set D) P"
    and typed: "\<exists>pre. lpp_stable_numeric_call operation coordinates modes a pre"
    and represented: "\<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_stable_numeric_call operation coordinates modes a pre"
  obtain pre where s: "s=State (lpp_integer_assignment pre) (locations (fst a))"
    and pre: "lpp_stable_numeric_call operation coordinates modes a pre" using represented by blast
  obtain h ps b gs os sigma eta where member: "((h,ps,b,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation)) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "target=lpp_success_atom_eval b eta"
    using step by (auto simp: lpp_stable_observed_calls_def)
  obtain receipt where row: "lpp_check_stable_numeric_call_row T coordinates modes locations system ((h,ps,b,gs),os) receipt"
    using lpp_stable_numeric_calls_row[OF checked member] by blast
  have known: "lpp_integer_known (map lpp_transfer_variable (lppsnc_facts receipt)) eta"
    by (rule lpp_stable_numeric_call_row_types[OF compatible row transfer guards facts])
  obtain post where edge: "(State (lpp_integer_assignment pre) (locations (fst a)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system"
    and post: "lpp_stable_numeric_call operation coordinates modes (lpp_success_atom_eval b eta) post"
    using lpp_checked_stable_numeric_call_step[OF compatible row known observations matching pre] by blast
  show "\<exists>t. (s,t)\<in>LPPIntegerLTS.transition system \<and>
    (\<exists>pre. t=State (lpp_integer_assignment pre) (locations (fst target)) \<and>
      lpp_stable_numeric_call operation coordinates modes target pre)"
    using edge post by (auto simp: s target lpp_success_atom_eval_def)
qed


ML \<open>
val checked = [@{thm lpp_checked_stable_numeric_calls_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable numeric calls dependency" else ();
\<close>
end
