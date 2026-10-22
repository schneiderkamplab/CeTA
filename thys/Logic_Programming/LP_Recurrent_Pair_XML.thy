theory LP_Recurrent_Pair_XML
  imports LP_Recurrent_Pair_Check LP_Source_Trace_XML
begin

definition lp_recurrent_steps_parser where
  "lp_recurrent_steps_parser = xml_many (STR ''steps'') (XMLdo (STR ''step'') {
    c \<leftarrow> xml_nat (STR ''clauseIndex'');
    bindings \<leftarrow> lp_trace_bindings_parser;
    xml_return (c,bindings)
  }) id"

definition lp_recurrent_pair_parser where
  "lp_recurrent_pair_parser = XMLdo (STR ''lpTocl09RecurrentPairProof'') {
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
    A \<leftarrow> xml_singleton (STR ''atomContext'') lp_atom_parser id;
    C \<leftarrow> xml_singleton (STR ''termContext'') (CPF_Input_Parser.term symbol_parser Mapping.empty) id;
    x \<leftarrow> xml_singleton (STR ''firstHole'') lp_trace_variable_parser id;
    y \<leftarrow> xml_singleton (STR ''secondHole'') lp_trace_variable_parser id;
    s \<leftarrow> xml_singleton (STR ''seed'') (CPF_Input_Parser.term symbol_parser Mapping.empty) id;
    d \<leftarrow> xml_nat (STR ''stride'');
    n \<leftarrow> xml_nat (STR ''pumpBase'');
    m \<leftarrow> xml_nat (STR ''resetBase'');
    a \<leftarrow> xml_nat (STR ''pumpGrowth'');
    b \<leftarrow> xml_nat (STR ''resetGrowth'');
    c \<leftarrow> xml_nat (STR ''resetOffset'');
    keep \<leftarrow> xml_bool (STR ''keepFirst'');
    steps1 \<leftarrow> lp_recurrent_steps_parser;
    steps2 \<leftarrow> lp_recurrent_steps_parser;
    xml_return (P,query,A,C,x,y,s,d,n,m,a,b,c,keep,steps1,steps2)
  }"

definition check_lp_recurrent_pair_xml where
  "check_lp_recurrent_pair_xml xml = (case parse_xml_string lp_recurrent_pair_parser xml of
    Right (P,(q,arity,positions),A,C,x,y,s,d,n,m,a,b,c,keep,steps1,steps2) \<Rightarrow>
      lp_recurrent_pair_check P q arity positions A C x y s d n m a b c keep steps1 steps2
    | _ \<Rightarrow> False)"

theorem check_lp_recurrent_pair_xml_sound:
  assumes parsed: "parse_xml_string lp_recurrent_pair_parser xml =
    Right (P,(q,arity,positions),A,C,x,y,s,d,n,m,a,b,c,keep,steps1,steps2)"
    and ok: "check_lp_recurrent_pair_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_recurrent_pair_check_sound)
    (use parsed ok in \<open>simp add: check_lp_recurrent_pair_xml_def\<close>)

end
