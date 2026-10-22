theory LP_Constructor_XML
  imports LP_Constructor_Checker LP_SEG_Residual_XML
begin

definition lp_constructor_parser where
  "lp_constructor_parser = XMLdo (STR ''lpConstructorQDpTerminationProof'') {
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    outs \<leftarrow> xml_many (STR ''returns'')
      (xml_pair (STR ''return'') symbol_parser symbol_parser Pair) id;
    fallback \<leftarrow> xml_singleton (STR ''fallback'') symbol_parser id;
    names \<leftarrow> xml_many (STR ''continuations'')
      (xml_many (STR ''clause'') symbol_parser id) id;
    marks \<leftarrow> xml_many (STR ''marks'')
      (xml_pair (STR ''mark'') symbol_parser symbol_parser Pair) id;
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    filters \<leftarrow> CPF_Proof_Parser.afs symbol_parser;
    seed \<leftarrow> xml_singleton (STR ''seed'') symbol_parser id;
    nfs \<leftarrow>[False] xml_bool (STR ''normalSubstitutions'');
    prf \<leftarrow> xml2dp_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,outs,fallback,names,marks,filters,query,seed,nfs,prf)
  }"

definition check_lp_constructor_xml where
  "check_lp_constructor_xml xml = (case parse_xml_string lp_constructor_parser xml of
    Right (P,outs,fallback,names,marks,filters,(q,n,positions),seed,nfs,prf) \<Rightarrow>
      check_lp_constructor tp_rbt_impl dpp_rbt_impl P outs fallback names marks filters q n positions seed nfs prf
    | _ \<Rightarrow> False)"

theorem check_lp_constructor_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_constructor_parser xml =
    Right (P,outs,fallback,names,marks,filters,(q,n,positions),seed,nfs,prf)"
    and ok: "check_lp_constructor_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule check_lp_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len gr])
    (use parsed ok in \<open>simp add: check_lp_constructor_xml_def\<close>)

definition check_lp_constructor_any_xml where
  "check_lp_constructor_any_xml xml = (check_lp_answer_full_xml xml \<or> check_lp_constructor_xml xml)"

end
