theory LP_Prolog_Stable_Result_Context
 imports LP_Prolog_Stable_Result_Guards
begin

type_synonym lpp_result_records = "(string lpp_success_clause * (nat * string lpp_integer_result_receipt) list) list"

definition lpp_result_context_check where
  "lpp_result_context_check P records evidence context =
    (lpp_result_program_check P records \<and>
     lppsir_program evidence=lpp_result_program records \<and>
     lpp_check_transfer_contract (lppsir_summaries evidence) (lppsir_program evidence) (lppsir_proofs evidence) \<and>
     lpp_check_operation_context (lpp_transfer_lookup (lppsir_summaries evidence))
       (fst context) (fst (snd context)) (lppsir_facts evidence) (lppsir_integers evidence))"

theorem lpp_result_context_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_result_context_check P records evidence context"
    and observed: "lpp_stable_context_holds operation P context eta"
  shows "lpp_stable_context_holds operation P
    (lpp_context_add_integers context (lppsir_integers evidence)) eta"
proof -
  let ?T = "lpp_transfer_lookup (lppsir_summaries evidence)"
  obtain ps gs obs where context_shape: "context=(ps,gs,obs)" by (cases "context") auto
  have enrichment: "lpp_result_program_check P records"
    and identity: "lppsir_program evidence=lpp_result_program records"
    and transfer: "lpp_check_transfer_program ?T (lppsir_program evidence) (lppsir_proofs evidence)"
    and typing: "lpp_check_operation_context ?T ps gs (lppsir_facts evidence) (lppsir_integers evidence)"
    using checked by (auto simp: lpp_result_context_check_def lpp_check_transfer_contract_def context_shape)
  have guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs"
    using lpp_stable_context_finite_envelope[OF compatible observed]
    by (simp add: context_shape lpp_evaluation_context_holds_def)
  have old_facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
    (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
    using observed by (auto simp: context_shape lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
  have facts: "list_all (lpp_guarded_success (lppsir_program evidence) lpp_finite_evaluation_result)
    (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
    using old_facts lpp_result_program_sound[OF compatible enrichment]
    by (auto simp: identity list_all_iff)
  have path: "lpp_check_path_types ?T ps gs (lppsir_facts evidence)"
    using typing by (simp add: lpp_check_operation_context_def)
  have known: "lpp_integer_known (map lpp_transfer_variable (lppsir_facts evidence)) eta"
    by (rule lpp_check_path_types_sound[OF transfer path guards facts])
      (rule lpp_finite_evaluation_integer_contract)
  have integers: "lpp_integer_known (lppsir_integers evidence) eta"
    using known typing by (auto simp: lpp_check_operation_context_def lpp_integer_known_def list_all_iff)
  show ?thesis by (rule lpp_stable_add_integers_sound[OF observed integers])
qed
ML \<open>
val checked = [@{thm lpp_result_context_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted result return dependency" else ();
\<close>
end
