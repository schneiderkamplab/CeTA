theory LP_Prolog_Stable_Result_Guards
 imports LP_Prolog_Stable_Integer_Result_Domain LP_Prolog_Stable_Return_Receipts
begin

text \<open>Checked consequences of successful evaluation enrich the existing
success program. Complete clause and helper coverage is preserved. The added
integer fact concerns the result term, never the unevaluated operands.\<close>

fun lpp_result_guard_check where
  "lpp_result_guard_check gs (i,receipt) = (i<length gs \<and>
    lpp_check_integer_result_receipt [] receipt \<and>
    (case gs!i of LPPSEvaluates e t \<Rightarrow> e=lpp_integer_result_term receipt | _ \<Rightarrow> False))"
fun lpp_result_guard where
  "lpp_result_guard (LPPSEvaluates e t) = LPPSInteger t"
| "lpp_result_guard g = g"
definition lpp_enrich_result_guards where
  "lpp_enrich_result_guards gs receipts = gs @ map (\<lambda>(i,r). lpp_result_guard (gs!i)) receipts"

lemma lpp_result_guard_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_result_guard_check gs (i,receipt)"
    and holds: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
  shows "lpp_success_guard_holds lpp_finite_evaluation_result eta (lpp_result_guard (gs!i))"
proof -
  obtain t where guard: "gs!i=LPPSEvaluates (lpp_integer_result_term receipt) t"
    and index: "i<length gs" and check: "lpp_check_integer_result_receipt [] receipt"
    using checked by (auto split: lpp_success_guard.splits)
  have selected_guard: "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta (gs!i)"
    using holds nth_mem[OF index] by (auto simp: list_all_iff)
  have evaluated: "lpp_stable_scalar_evaluation operation
    (lp_ieval (lpp_integer_result_term receipt) eta) (lp_ieval t eta)"
    using selected_guard by (simp add: guard)
  have integer: "lpp_is_integer (lp_ieval t eta)"
    by (rule lpp_checked_actual_integer_result[OF compatible check _ evaluated])
      (simp add: lpp_integer_known_def)
  show ?thesis using integer by (simp add: guard)
qed

lemma lpp_enrich_result_guards_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "list_all (lpp_result_guard_check gs) receipts"
    and holds: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
  shows "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta)
    (lpp_enrich_result_guards gs receipts)"
proof -
  have old: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs"
  proof (unfold list_all_iff, intro ballI)
    fix g assume "g\<in>set gs"
    then have "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta g"
      using holds by (simp add: list_all_iff)
    then show "lpp_success_guard_holds lpp_finite_evaluation_result eta g"
      by (cases g) (auto dest: lpp_stable_evaluation_finite_envelope[OF compatible])
  qed
  have extra: "lpp_success_guard_holds lpp_finite_evaluation_result eta (lpp_result_guard (gs!i))"
    if member: "(i,receipt)\<in>set receipts" for i receipt
  proof -
    have check: "lpp_result_guard_check gs (i,receipt)"
      using checked member unfolding list_all_iff by blast
    show ?thesis by (rule lpp_result_guard_sound[OF compatible check holds])
  qed
  show ?thesis using old extra by (auto simp: lpp_enrich_result_guards_def list_all_iff)
qed


definition lpp_result_program_check where
  "lpp_result_program_check P records = (map fst records=P \<and>
    list_all (\<lambda>((h,bs,gs),receipts). list_all (lpp_result_guard_check gs) receipts) records)"
definition lpp_result_program where
  "lpp_result_program records = map (\<lambda>((h,bs,gs),receipts).
    (h,bs,lpp_enrich_result_guards gs receipts)) records"

theorem lpp_result_program_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_result_program_check P records"
    and success: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) a"
  shows "lpp_guarded_success (lpp_result_program records) lpp_finite_evaluation_result a"
using success
proof induction
  case (clause h bs gs eta)
  have coverage: "set (map fst records)=set P"
    using checked by (simp add: lpp_result_program_check_def)
  have included: "(h,bs,gs)\<in>fst ` set records"
    using clause.hyps(1) coverage by (simp only: set_map)
  obtain record_entry where first: "(h,bs,gs)=fst record_entry"
    and member_entry: "record_entry\<in>set records"
  proof (rule imageE[OF included])
    fix record_entry
    assume first: "(h,bs,gs)=fst record_entry" and member_entry: "record_entry\<in>set records"
    show thesis by (rule that[OF first member_entry])
  qed
  define receipts where "receipts=snd record_entry"
  have member: "((h,bs,gs),receipts)\<in>set records"
    using member_entry by (simp only: receipts_def first prod.collapse)
  have check: "list_all (lpp_result_guard_check gs) receipts"
    using checked member by (auto simp: lpp_result_program_check_def list_all_iff)
  have mapped: "(h,bs,lpp_enrich_result_guards gs receipts)\<in>set (lpp_result_program records)"
    unfolding lpp_result_program_def set_map
    by (rule image_eqI[where x="((h,bs,gs),receipts)"]) (simp, fact member)
  have guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta)
    (lpp_enrich_result_guards gs receipts)"
    by (rule lpp_enrich_result_guards_sound[OF compatible check clause.hyps(2)])
  show ?case by (rule lpp_guarded_success.clause[OF mapped guards])
    (use clause.IH in \<open>auto simp: list_all_iff\<close>)
qed

ML \<open>
val checked = @{thms lpp_result_guard_sound lpp_enrich_result_guards_sound lpp_result_program_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted successful-result guard dependency" else ();
\<close>
end
