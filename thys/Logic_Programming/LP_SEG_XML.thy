theory LP_SEG_XML
  imports LP_SEG_Certificate LP_Source_Graph_XML
begin

definition lp_seg_variable_parser where
  "lp_seg_variable_parser = xml_change (CPF_Input_Parser.term symbol_parser Mapping.empty)
    (\<lambda>t. case t of Var x\<Rightarrow>xml_return x
      | Fun _ _\<Rightarrow>xml_error (STR ''SEG variable expected''))"

definition lp_seg_action_parser where
  "lp_seg_action_parser =
    (XMLdo (STR ''success'') {xml_return LPSegSuccess}) XMLor
    (XMLdo (STR ''resolve'') {
      k \<leftarrow> xml_nat (STR ''prefix'');
      anchor \<leftarrow> xml_singleton (STR ''anchor'') symbol_parser id;
      children \<leftarrow> xml_many (STR ''children'') (xml_nat (STR ''index'')) id;
      xml_return (LPSegResolve k anchor (map (\<lambda>i. if i=0 then None else Some (i-1)) children))
    }) XMLor
    (XMLdo (STR ''instance'') {
      j \<leftarrow> xml_nat (STR ''target'');
      bindings \<leftarrow> xml_many (STR ''substitution'')
        (xml_pair (STR ''binding'') lp_seg_variable_parser
          (CPF_Input_Parser.term symbol_parser Mapping.empty) Pair) id;
      xml_return (LPSegInstance j bindings)
    }) XMLor
    (XMLdo (STR ''split'') {
      a \<leftarrow> xml_nat (STR ''first'');
      b \<leftarrow> xml_nat (STR ''rest'');
      xml_return (LPSegSplit a b)
    })"

definition lp_seg_parser where
  "lp_seg_parser = XMLdo (STR ''lpSymbolicGraphTerminationProof'') {
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
      gr \<leftarrow> xml_many (STR ''ground'') lp_seg_variable_parser id;
      f \<leftarrow> xml_singleton (STR ''symbol'') symbol_parser id;
      act \<leftarrow> lp_seg_action_parser;
      xml_return (gs,gr,f,act)
    }) id;
    trs_rules \<leftarrow> CPF_Input_Parser.rules symbol_parser Mapping.empty Mapping.empty;
    prf \<leftarrow> xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,query,fuel,root_id,nds,trs_rules,prf)
  }"

definition check_lp_seg_xml where
  "check_lp_seg_xml xml = (case parse_xml_string lp_seg_parser xml of
    Right (P,(q,n,positions),fuel,root_id,nds,trs_rules,prf)\<Rightarrow>
      check_lp_seg tp_rbt_impl dpp_rbt_impl fuel P nds trs_rules root_id q n positions prf
    | _\<Rightarrow>False)"

theorem check_lp_seg_xml_sound:
  assumes parsed: "parse_xml_string lp_seg_parser xml = Right (P,(q,n,positions),fuel,root_id,nds,trs_rules,prf)"
    and checked: "check_lp_seg_xml xml" and len: "length ts=n"
    and ground: "\<forall>i\<in>set positions. lp_seg_ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,ts :: ((string,nat list) lab,string) lp_iterm list)]}"
  by (rule check_lp_seg_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed checked in \<open>simp add: check_lp_seg_xml_def\<close>)

definition check_lp_seg_full_xml where
  "check_lp_seg_full_xml xml = (check_lp_graph_full_xml xml \<or> check_lp_seg_xml xml)"

end
