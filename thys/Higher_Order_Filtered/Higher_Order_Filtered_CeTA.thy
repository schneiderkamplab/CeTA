theory Higher_Order_Filtered_CeTA
  imports Higher_Order_Filtered_Check
begin

definition ho_check_ceta_filtered_delegation where
  "ho_check_ceta_filtered_delegation I J S R F P ce ranks arities priorities selections phases sorts fuel prf =
    (ho_check_filtered_delegation_side S R F P ranks arities priorities selections phases sorts fuel \<and>
      isOK (check_trs_termination_proof I J False id
        (tp_ops.mk I False [] (ho_delegation_trs P ce) []) prf))"

theorem ho_check_ceta_filtered_delegation_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "ho_check_ceta_filtered_delegation I J S R F P ce ranks arities priorities selections phases sorts fuel prf"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  interpret tp_spec I by (rule I)
  have side: "ho_check_filtered_delegation_side S R F P ranks arities priorities selections phases sorts fuel"
    and child_ok: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (ho_delegation_trs P ce) []) prf)"
    using checked by (auto simp: ho_check_ceta_filtered_delegation_def)
  have sn: "SN (rstep (set (ho_delegation_trs P ce)))"
    using check_trs_termination_proof[OF I J child_ok]
    by (simp add: SN_qrel_def)
  show ?thesis
    by (rule ho_check_filtered_delegation_side_sound[
      where rel="ho_delegation_step P ce" and ce=ce,
      OF side ho_delegation_ce_left ho_delegation_ce_right
        ho_delegation_context ho_delegation_instance ho_delegation_wf[OF sn]])
qed

definition ho_check_ceta_filtered_delegation_xml where
  "ho_check_ceta_filtered_delegation_xml S R F P ce ranks arities priorities selections phases sorts fuel xml =
    (case parse_xml_string
      (xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty) xml of
       Right prf \<Rightarrow> ho_check_ceta_filtered_delegation tp_rbt_impl dpp_rbt_impl
         S R F P ce ranks arities priorities selections phases sorts fuel prf
     | _ \<Rightarrow> False)"

theorem ho_check_ceta_filtered_delegation_xml_sound:
  assumes "ho_check_ceta_filtered_delegation_xml S R F P ce ranks arities priorities selections phases sorts fuel xml"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  obtain child where child_check:
    "ho_check_ceta_filtered_delegation tp_rbt_impl dpp_rbt_impl
       S R F P ce ranks arities priorities selections phases sorts fuel child"
    using assms unfolding ho_check_ceta_filtered_delegation_xml_def
    by (cases "parse_xml_string
      (xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty) xml") auto
  show ?thesis
    by (rule ho_check_ceta_filtered_delegation_sound[OF tp_rbt_impl dpp_rbt_impl child_check])
qed

end
