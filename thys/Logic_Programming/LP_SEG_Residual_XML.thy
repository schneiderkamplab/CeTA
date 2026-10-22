theory LP_SEG_Residual_XML
  imports LP_SEG_Residual_Check LP_SEG_XML
begin

definition lp_residual_parser where
  "lp_residual_parser = XMLdo (STR ''lpAnswerGraphTerminationProof'') {
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    fuel \<leftarrow> xml_nat (STR ''fuel'');
    root_id \<leftarrow> xml_nat (STR ''root'');
    nds \<leftarrow> xml_many (STR ''nodes'') (XMLdo (STR ''node'') {
      gs \<leftarrow> xml_many (STR ''goals'') lp_atom_parser id;
      vs \<leftarrow> xml_many (STR ''variables'') lp_seg_variable_parser id;
      f \<leftarrow> xml_singleton (STR ''symbol'') symbol_parser id;
      act \<leftarrow> lp_seg_action_parser;
      xml_return (gs,vs,f,act)
    }) id;
    child \<leftarrow> lp_tocl09_parser;
    xml_return (P,query,fuel,root_id,nds,child)
  }"

definition check_lp_residual_xml where
  "check_lp_residual_xml xml = (case parse_xml_string lp_residual_parser xml of
    Right (P,(q,n,positions),fuel,root_id,nds,
      (Q,outs,fallback,names,filters,(q',n',positions'),prf)) \<Rightarrow>
      n' = n \<and> positions' = positions \<and>
      check_lp_residual tp_rbt_impl dpp_rbt_impl fuel P nds root_id q n positions
        Q outs fallback names filters q' prf
    | _ \<Rightarrow> False)"

theorem check_lp_residual_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_residual_parser xml =
    Right (P,(q,n,positions),fuel,root_id,nds,
      (Q,outs,fallback,names,filters,(q',n',positions'),prf))"
    and checked: "check_lp_residual_xml xml" and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  have valid: "check_lp_residual tp_rbt_impl dpp_rbt_impl fuel P nds root_id q n positions
    Q outs fallback names filters q' prf"
    using parsed checked by (simp add: check_lp_residual_xml_def)
  show ?thesis by (rule check_lp_residual_sound[OF tp_rbt_impl dpp_rbt_impl valid len ground])
qed

definition check_lp_answer_full_xml where
  "check_lp_answer_full_xml xml = (check_lp_seg_full_xml xml \<or> check_lp_residual_xml xml)"

end
