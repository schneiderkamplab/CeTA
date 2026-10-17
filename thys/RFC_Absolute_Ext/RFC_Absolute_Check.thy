theory RFC_Absolute_Check
  imports RFC_Absolute_Residual "Proof_Checker_Base.Check_Termination"
begin

context fixes
  I :: "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
  and J :: "('dpp, ('f,label_type) lab,string) dpp_ops"
begin

fun check_rfc_absolute where
  "check_rfc_absolute i tp (Rfc_Matchbox_Relative_Bounds info initial D child) = do {
    tp' \<leftarrow> rfc_matchbox_absolute_bounds_tt I info initial D tp;
    check_rfc_absolute (add_index i 1) tp' child
  }"
| "check_rfc_absolute i tp prf = check_trs_termination_proof I J False i tp prf"

lemma check_rfc_absolute_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_rfc_absolute i tp prf)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
  using ok
  by (induction i tp "prf" rule: check_rfc_absolute.induct)
    (auto simp del: check_trs_termination_proof.simps isOK_bind
      intro: rfc_matchbox_absolute_bounds_tt_sound[OF I _ infinite_lab]
      check_trs_termination_proof[OF I J] split: sum_bind_splits)

end
end
