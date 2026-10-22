theory LP_Pattern_Trace_XML
  imports LP_Pattern_Trace LP_Recurrent_Pair_XML
begin

definition lp_pattern_success_parser where
  "lp_pattern_success_parser = XMLdo (STR ''successPattern'') {
    tsb \<leftarrow> lp_trace_bindings_parser;
    nu \<leftarrow> lp_trace_bindings_parser;
    basetrace \<leftarrow> lp_recurrent_steps_parser;
    steps \<leftarrow> lp_recurrent_steps_parser;
    xml_return (LPPatternSuccess tsb nu basetrace steps)
  }"

definition lp_pattern_loop_parser where
  "lp_pattern_loop_parser = XMLdo (STR ''lpTocl09PatternLoopProof'') {
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
    sig \<leftarrow> lp_trace_bindings_parser;
    mu \<leftarrow> lp_trace_bindings_parser;
    firststeps \<leftarrow> lp_recurrent_steps_parser;
    steps \<leftarrow> xml_many (STR ''prefixes'') lp_pattern_success_parser id;
    xml_return (P,query,A,sig,mu,firststeps,steps)
  }"

definition check_lp_pattern_loop_xml where
  "check_lp_pattern_loop_xml xml = (case parse_xml_string lp_pattern_loop_parser xml of
    Right (P,(q,arity,positions),A,sig,mu,firststeps,steps) \<Rightarrow>
      lp_pattern_loop_check P q arity positions A sig mu firststeps steps
    | _ \<Rightarrow> False)"

theorem check_lp_pattern_loop_xml_sound:
  assumes parsed: "parse_xml_string lp_pattern_loop_parser xml =
    Right (P,(q,arity,positions),A,sig,mu,firststeps,steps)"
    and ok: "check_lp_pattern_loop_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_pattern_loop_check_sound)
    (use parsed ok in \<open>simp add: check_lp_pattern_loop_xml_def\<close>)

end
