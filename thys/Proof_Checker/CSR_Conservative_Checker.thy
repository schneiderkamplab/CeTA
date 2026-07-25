(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Conservative_Checker
  imports
    CSR_Minimal_CSDP_Proofs
    CSR_Improved_CSDP_Proofs
begin

datatype ('f, 'l, 'v) extended_csr_termination_proof =
    Existing_CSR_Proof "('f, 'l, 'v) csr_termination_proof"
  | Conservative_CSR_Dependency_Pairs
      "('f, 'l) lab"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) csr_dp_termination_proof"

fun check_extended_csr_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   bool \<Rightarrow> showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) extended_csr_termination_proof \<Rightarrow> showsl check"
where
  "check_extended_csr_termination_proof I J a i \<mu> R
      (Existing_CSR_Proof prf) =
    check_csr_termination_proof_min I J a i \<mu> R prf"
| "check_extended_csr_termination_proof I J a i \<mu> R
      (Conservative_CSR_Dependency_Pairs U P S prf) =
    debug i (STR ''conservative CSR dependency pairs'') (do {
      dpp \<leftarrow> conservative_csr_dependency_pairs_tt J U \<mu> R P S
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': invalid conservative CSR-DP transformation\<newline>'') \<circ> s);
      check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below conservative CSR dependency pairs\<newline>'') \<circ> s)
    })"

lemma check_extended_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_extended_csr_termination_proof
      I J a i \<mu> R prf)"
  shows "SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
  using ok
proof (cases "prf")
  case (Existing_CSR_Proof old)
  from ok Existing_CSR_Proof have old_ok:
    "isOK (check_csr_termination_proof_min I J a i \<mu> R old)"
    by simp
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule check_csr_termination_proof_min_sound[OF I J old_ok])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
next
  case (Conservative_CSR_Dependency_Pairs U P S dp_prf)
  from ok Conservative_CSR_Dependency_Pairs
  obtain dpp where tt:
      "conservative_csr_dependency_pairs_tt J U \<mu> R P S = Inr dpp"
    and rec:
      "isOK (check_csr_dp_termination_proof
        I J False (add_index i 1) dpp dp_prf)"
    by auto
  have fin: "finite_dpp (dpp_ops.dpp J dpp)"
    by (rule check_csr_dp_termination_proof_sound[OF I J rec])
  show ?thesis
    by (rule conservative_csr_dependency_pairs_tt_finite_imp_SN_sig[
      OF J tt fin])
qed

end
