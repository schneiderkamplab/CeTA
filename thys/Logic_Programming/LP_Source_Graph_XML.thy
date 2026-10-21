theory LP_Source_Graph_XML
  imports LP_Source_Graph LP_Source_Loop_XML
begin

definition lp_source_graph_parser where
  "lp_source_graph_parser = XMLdo (STR ''lpTocl09SourceGraphProof'') {
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
      k \<leftarrow> xml_nat (STR ''prefix'');
      children \<leftarrow> xml_many (STR ''children'') (xml_nat (STR ''index'')) id;
      xml_return (gs,k,map (\<lambda>i. if i=0 then None else Some (i-1)) children)
    }) id;
    xml_return (P,query,fuel,root_id,nds)
  }"

definition check_lp_source_graph_xml where
  "check_lp_source_graph_xml xml = (case parse_xml_string lp_source_graph_parser xml of
    Right (P,(q,n,positions),fuel,root_id,nds) \<Rightarrow>
      list_all (\<lambda>i. i<n) positions \<and>
      lp_check_source_graph fuel P nds root_id \<and>
      fst (nds!root_id)=[(q,map Var (lp_source_query_args n))]
    | _ \<Rightarrow> False)"

theorem check_lp_source_graph_xml_sound:
  assumes parsed: "parse_xml_string lp_source_graph_parser xml = Right (P,(q,n,positions),fuel,root_id,nds)"
    and ok: "check_lp_source_graph_xml xml" and len: "length ts=n"
  shows "SN_on (lp_ild P) {[(q,ts :: ((string,nat list) lab,string) lp_iterm list)]}"
  by (rule lp_source_graph_query_sound[OF _ _ len])
    (use parsed ok in \<open>auto simp: check_lp_source_graph_xml_def\<close>)

definition check_lp_graph_full_xml where
  "check_lp_graph_full_xml xml = (check_lp_full_xml xml \<or> check_lp_source_graph_xml xml)"

end
