theory RFC_Absolute_Cert
  imports RFC_Absolute_Check "Proof_Checker.Ceta"
begin

context fixes
  I :: "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
  and J :: "('dpp, ('f,label_type) lab,string) dpp_ops"
  and K :: "('ac_tp, ('f,label_type) lab,string) ac_tp_ops"
  and L :: "('ac_dpp, ('f,label_type) lab,string) ac_dpp_ops"
begin

fun check_cert_rfc_absolute where
  "check_cert_rfc_absolute (Inn_TRS_input Q R S) Termination (Decision True)
      (TRS_Termination_Proof p) =
    check_rfc_absolute I J (showsl_lit (STR ''1''))
      (tp_ops.mk I (strategy_to_nfs Q) (strategy_to_Q Q R) R S) p"
| "check_cert_rfc_absolute inp prop ans p = check_cert I J K L False inp prop ans p"

lemma check_cert_rfc_absolute_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J" and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and ok: "isOK (check_cert_rfc_absolute inp prop ans p)"
  shows "desired_property inp prop ans"
  using ok
  apply (induction "inp" "prop" "ans" "p" rule: check_cert_rfc_absolute.induct)
  apply (simp_all only: check_cert_rfc_absolute.simps)
  apply (drule check_rfc_absolute_sound[OF I J])
  apply (simp add: desired_property_def tp_spec.mk_sound[OF I])
  apply ((erule check_cert_with_assms_sound[OF I J K L]; simp)+)
  done

definition certify_cert_problem_rfc_absolute where
  "certify_cert_problem_rfc_absolute a inp prop ans p =
    (let old = certify_cert_problem I J K L a inp prop ans p in
      if old = Certified \<or> a then old else
        case check_cert_rfc_absolute inp prop ans p of
          Inl err \<Rightarrow> old
        | Inr _ \<Rightarrow> Certified)"

lemma certify_cert_problem_rfc_absolute_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J" and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
    and ok: "certify_cert_problem_rfc_absolute False inp prop ans p = Certified"
  shows "desired_property inp prop ans"
  using ok unfolding certify_cert_problem_rfc_absolute_def Let_def
  by (auto split: if_splits sum.splits
      intro: certify_cert_problem_sound[OF I J K L] check_cert_rfc_absolute_sound[OF I J K L])

end

definition certify_proof_rfc_absolute where
  "certify_proof_rfc_absolute a inp_o prop_o answ_o prfs =
    bind2' (parse_combined_cert_problem inp_o prop_o answ_o prfs) Unsupported
      (\<lambda>(inp,prop,answ,p).
        certify_cert_problem_rfc_absolute tp_impl dpp_impl ac_tp_impl ac_dpp_impl a inp prop answ p)"

end
