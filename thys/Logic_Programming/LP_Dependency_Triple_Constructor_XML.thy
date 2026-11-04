theory LP_Dependency_Triple_Constructor_XML
  imports LP_Dependency_Triple_Constructor_Checker LP_Dependency_Triple_XML
begin

definition lp_triple_constructor_parser where
  "lp_triple_constructor_parser = XMLdo (STR ''lpDependencyTriplesConstructorProof'') {
    D \<leftarrow> xml_many (STR ''triples'') (XMLdo (STR ''triple'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      ps \<leftarrow> xml_many (STR ''prefix'') lp_atom_parser id;
      b \<leftarrow> xml_singleton (STR ''call'') lp_atom_parser id;
      xml_return (h,ps,b)
    }) id;
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    outs \<leftarrow> xml_many (STR ''returns'')
      (xml_pair (STR ''return'') symbol_parser symbol_parser Pair) id;
    fallback \<leftarrow> xml_singleton (STR ''fallback'') symbol_parser id;
    dnames \<leftarrow> xml_many (STR ''tripleContinuations'')
      (xml_many (STR ''triple'') symbol_parser id) id;
    pnames \<leftarrow> xml_many (STR ''programContinuations'')
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
    xml_return (D,P,outs,fallback,dnames,pnames,marks,filters,query,seed,nfs,prf)
  }"

definition check_lp_triple_constructor_xml where
  "check_lp_triple_constructor_xml xml = (case parse_xml_string lp_triple_constructor_parser xml of
    Right (D,P,outs,fallback,dnames,pnames,marks,filters,(q,n,positions),seed,nfs,prf) \<Rightarrow>
      check_lp_triple_constructor tp_rbt_impl dpp_rbt_impl D P outs fallback dnames pnames marks filters q n positions seed nfs prf
    | _ \<Rightarrow> False)"

theorem check_lp_triple_constructor_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_triple_constructor_parser xml =
      Right (D,P,outs,fallback,dnames,pnames,marks,filters,(q,n,positions),seed,nfs,prf)"
    and ok: "check_lp_triple_constructor_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_triple_calls (set D) P) {(q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
  by (rule check_lp_triple_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len gr])
    (use parsed ok in \<open>simp add: check_lp_triple_constructor_xml_def\<close>)

end
