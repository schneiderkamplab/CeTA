theory LP_Pattern_Trace_XML
  imports LP_Pattern_Acceleration LP_Recurrent_Pair_XML
begin

definition lp_pattern_success_parser where
  "lp_pattern_success_parser = XMLdo (STR ''successPattern'') {
    tsb \<leftarrow> lp_trace_bindings_parser;
    nu \<leftarrow> lp_trace_bindings_parser;
    basetrace \<leftarrow> lp_recurrent_steps_parser;
    steps \<leftarrow> lp_recurrent_steps_parser;
    xml_return (LPPatternSuccess tsb nu basetrace steps)
  }"

definition lp_pattern_instance_parser where
  "lp_pattern_instance_parser = XMLdo (STR ''successInstance'') {
    B \<leftarrow> xml_singleton (STR ''atomContext'') lp_atom_parser id;
    ls \<leftarrow> lp_trace_bindings_parser;
    lm \<leftarrow> lp_trace_bindings_parser;
    theta \<leftarrow> lp_trace_bindings_parser;
    eta \<leftarrow> lp_trace_bindings_parser;
    tsb \<leftarrow> lp_trace_bindings_parser;
    nu \<leftarrow> lp_trace_bindings_parser;
    basetrace \<leftarrow> lp_recurrent_steps_parser;
    steps \<leftarrow> lp_recurrent_steps_parser;
    xml_return (LPPatternInstance B ls lm theta eta tsb nu basetrace steps)
  }"

definition lp_pattern_acceleration_parser where
  "lp_pattern_acceleration_parser = XMLdo (STR ''acceleration'') {
    B \<leftarrow> xml_singleton (STR ''atomContext'') lp_atom_parser id;
    ls \<leftarrow> lp_trace_bindings_parser;
    lm \<leftarrow> lp_trace_bindings_parser;
    theta \<leftarrow> lp_trace_bindings_parser;
    eta \<leftarrow> lp_trace_bindings_parser;
    delta \<leftarrow> lp_trace_bindings_parser;
    k \<leftarrow> xml_nat (STR ''factor'');
    b \<leftarrow> xml_nat (STR ''offset'');
    xml_return (B,ls,lm,theta,eta,delta,k,b)
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
    steps \<leftarrow> xml_many (STR ''prefixes'')
      (xml_or lp_pattern_success_parser (xml_or lp_pattern_instance_parser
        (XMLdo (STR ''resolvePattern'') {
          trace \<leftarrow> lp_recurrent_steps_parser;
          xml_return (LPPatternResolve trace)
        }))) id;
    acc \<leftarrow>? lp_pattern_acceleration_parser;
    xml_return (P,query,A,sig,mu,firststeps,steps,acc)
  }"

definition check_lp_pattern_loop_xml where
  "check_lp_pattern_loop_xml xml = (case parse_xml_string lp_pattern_loop_parser xml of
    Right (P,(q,arity,positions),A,sig,mu,firststeps,steps,acc) \<Rightarrow>
      (case acc of None \<Rightarrow> lp_pattern_loop_check P q arity positions A sig mu firststeps steps
      | Some (B,ls,lm,theta,eta,delta,k,b) \<Rightarrow>
        k\<le>16 \<and> b\<le>16 \<and>
        lp_accelerated_loop_check P q arity positions A sig mu firststeps steps B ls lm theta eta delta k b)
    | _ \<Rightarrow> False)"

theorem check_lp_pattern_loop_xml_sound:
  assumes parsed: "parse_xml_string lp_pattern_loop_parser xml =
    Right (P,(q,arity,positions),A,sig,mu,firststeps,steps,acc)"
    and ok: "check_lp_pattern_loop_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof (cases acc)
  case None
  show ?thesis by (rule lp_pattern_loop_check_sound)
    (use parsed ok None in \<open>simp add: check_lp_pattern_loop_xml_def\<close>)
next
  case (Some witness)
  obtain B ls lm theta eta delta k b where witness: "witness=(B,ls,lm,theta,eta,delta,k,b)"
    by (cases witness) auto
  have checked: "lp_accelerated_loop_check P q arity positions A sig mu firststeps steps B ls lm theta eta delta k b"
    using parsed ok Some witness by (simp add: check_lp_pattern_loop_xml_def)
  show ?thesis by (rule lp_accelerated_loop_check_sound[OF checked])
qed

end
