theory LP_Affine_Loop_XML
  imports LP_Affine_Loop LP_Pattern_Trace_XML
begin

definition lp_affine_parser where
  "lp_affine_parser = XMLdo (STR ''affine'') {
    a \<leftarrow> xml_nat (STR ''first'');
    b \<leftarrow> xml_nat (STR ''second'');
    d \<leftarrow> xml_nat (STR ''constant'');
    xml_return (a,b,d)
  }"

definition lp_affine_environment_parser where
  "lp_affine_environment_parser = xml_many (STR ''environment'')
    (XMLdo (STR ''binding'') {
      x \<leftarrow> lp_trace_variable_parser;
      a \<leftarrow> lp_affine_parser;
      xml_return (x,a)
    }) id"

definition lp_affine_success_parser where
  "lp_affine_success_parser = XMLdo (STR ''affineSuccess'') {
    B \<leftarrow> xml_singleton (STR ''atomContext'') lp_atom_parser id;
    sig \<leftarrow> lp_trace_bindings_parser;
    mu \<leftarrow> lp_trace_bindings_parser;
    tsb \<leftarrow> lp_trace_bindings_parser;
    nu \<leftarrow> lp_trace_bindings_parser;
    basetrace \<leftarrow> lp_recurrent_steps_parser;
    steps \<leftarrow> lp_recurrent_steps_parser;
    idx \<leftarrow> lp_affine_parser;
    rho \<leftarrow> lp_affine_environment_parser;
    xml_return (LPAffineSuccess B sig mu tsb nu basetrace steps idx rho)
  }"

definition lp_affine_loop_parser where
  "lp_affine_loop_parser = XMLdo (STR ''lpTocl09AffineLoopProof'') {
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
    c \<leftarrow> xml_singleton (STR ''constructor'') symbol_parser id;
    z \<leftarrow> xml_singleton (STR ''zero'') symbol_parser id;
    env \<leftarrow> lp_affine_environment_parser;
    A \<leftarrow> xml_singleton (STR ''atomContext'') lp_atom_parser id;
    firststeps \<leftarrow> lp_recurrent_steps_parser;
    steps \<leftarrow> xml_many (STR ''prefixes'')
      (xml_or lp_affine_success_parser (XMLdo (STR ''resolvePattern'') {
        trace \<leftarrow> lp_recurrent_steps_parser;
        xml_return (LPAffineResolve trace)
      })) id;
    u \<leftarrow> lp_affine_parser;
    v \<leftarrow> lp_affine_parser;
    xml_return (P,query,c,z,env,A,firststeps,steps,u,v)
  }"

definition check_lp_affine_loop_xml where
  "check_lp_affine_loop_xml xml = (case parse_xml_string lp_affine_loop_parser xml of
    Right (P,(q,arity,positions),c,z,env,A,firststeps,steps,u,v) \<Rightarrow>
      lp_affine_loop_check P q arity positions c z env A firststeps steps u v
    | _ \<Rightarrow> False)"

theorem check_lp_affine_loop_xml_sound:
  assumes parsed: "parse_xml_string lp_affine_loop_parser xml =
    Right (P,(q,arity,positions),c,z,env,A,firststeps,steps,u,v)"
    and ok: "check_lp_affine_loop_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_affine_loop_check_sound)
    (use parsed ok in \<open>simp add: check_lp_affine_loop_xml_def\<close>)

end
