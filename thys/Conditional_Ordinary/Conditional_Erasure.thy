theory Conditional_Erasure
  imports "Proof_Checker.Ceta"
begin

hide_const (open) CPF_Proof_Parser.rstep
hide_const (open) CPF_Proof_Parser.cstep

definition check_conditional_erasure where
  "check_conditional_erasure I J R p =
    isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (map fst R) []) p)"

theorem check_conditional_erasure_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_conditional_erasure I J R p"
  shows "SN (cstep (set R))"
proof -
  interpret tp_spec I by (rule I)
  have child_ok: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (map fst R) []) p)"
    using ok unfolding check_conditional_erasure_def .
  have child: "SN (rstep (set (map fst R)))"
    using check_trs_termination_proof[OF I J child_ok]
    by (simp add: SN_qrel_def)
  have subset: "cstep (set R) \<subseteq> rstep (set (map fst R))"
    using cstep_imp_Ru_step[of "set R"] by (simp add: Ru_def)
  show ?thesis by (rule SN_subset[OF child subset])
qed

definition conditional_erasure_parser where
  "conditional_erasure_parser = XMLdo (STR ''conditionalErasureProof'') {
    inp \<leftarrow> input_parser Mapping.empty Mapping.empty;
    prf \<leftarrow> xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (inp, prf)
  }"

definition check_conditional_erasure_xml where
  "check_conditional_erasure_xml xml =
    (case parse_xml_string conditional_erasure_parser xml of
       Right (CTRS_input R, p) \<Rightarrow>
         check_conditional_erasure tp_rbt_impl dpp_rbt_impl R p
     | _ \<Rightarrow> False)"

theorem check_conditional_erasure_xml_sound:
  assumes "check_conditional_erasure_xml xml"
  obtains R p where
    "parse_xml_string conditional_erasure_parser xml = Right (CTRS_input R,p)"
    "SN (cstep (set R))"
proof -
  obtain inp p where parsed:
    "parse_xml_string conditional_erasure_parser xml = Right (inp,p)"
    using assms unfolding check_conditional_erasure_xml_def
    by (cases "parse_xml_string conditional_erasure_parser xml") (auto split: prod.splits)
  obtain R where inp: "inp = CTRS_input R"
    using assms unfolding check_conditional_erasure_xml_def parsed
    by (cases inp) auto
  have ok: "check_conditional_erasure tp_rbt_impl dpp_rbt_impl R p"
    using assms by (simp add: check_conditional_erasure_xml_def parsed inp)
  have sn: "SN (cstep (set R))"
    by (rule check_conditional_erasure_sound[OF tp_rbt_impl dpp_rbt_impl ok])
  show thesis by (rule that[OF parsed[unfolded inp] sn])
qed

end
