theory LP_Source_Unify_XML
  imports LP_Source_Neutral LP_Affine_Loop_XML
begin

definition lp_unify_step_parser where
  "lp_unify_step_parser = XMLdo (STR ''step'') {
    c \<leftarrow> xml_nat (STR ''clauseIndex'');
    sb \<leftarrow> lp_trace_bindings_parser;
    rb \<leftarrow> lp_trace_bindings_parser;
    xml_return (c,sb,rb)
  }"

definition lp_source_unify_parser where
  "lp_source_unify_parser = XMLdo (STR ''lpTocl09SourceUnifyProof'') {
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
    a0 \<leftarrow> xml_singleton (STR ''initial'') lp_atom_parser id;
    entry_steps \<leftarrow> xml_many (STR ''prefix'') lp_unify_step_parser id;
    steps \<leftarrow> xml_many (STR ''steps'') lp_unify_step_parser id;
    bindings \<leftarrow> lp_trace_bindings_parser;
    xml_return (P,query,a0,entry_steps,steps,bindings)
  }"

definition check_lp_source_unify_xml where
  "check_lp_source_unify_xml xml = (case parse_xml_string lp_source_unify_parser xml of
    Right (P,(q,n,positions),a0,entry_steps,steps,bindings) \<Rightarrow>
      lp_source_unify_check P q n positions a0 entry_steps steps bindings
    | _ \<Rightarrow> False)"

theorem check_lp_source_unify_xml_sound:
  assumes parsed: "parse_xml_string lp_source_unify_parser xml =
    Right (P,(q,n,positions),a0,entry_steps,steps,bindings)"
    and ok: "check_lp_source_unify_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=n \<and> (\<forall>i\<in>set positions. i<n \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_source_unify_check_sound)
    (use parsed ok in \<open>simp add: check_lp_source_unify_xml_def\<close>)

definition lp_source_neutral_parser where
  "lp_source_neutral_parser = XMLdo (STR ''lpTocl09SourceNeutralProof'') {
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
    a0 \<leftarrow> xml_singleton (STR ''initial'') lp_atom_parser id;
    entry_steps \<leftarrow> xml_many (STR ''prefix'') lp_unify_step_parser id;
    c \<leftarrow> xml_nat (STR ''clauseIndex'');
    Is \<leftarrow> xml_many (STR ''neutral'') (xml_nat (STR ''index'')) id;
    sb \<leftarrow> lp_trace_bindings_parser;
    rb \<leftarrow> lp_trace_bindings_parser;
    xml_return (P,query,a0,entry_steps,c,Is,sb,rb)
  }"

definition check_lp_source_neutral_xml where
  "check_lp_source_neutral_xml xml = (case parse_xml_string lp_source_neutral_parser xml of
    Right (P,(q,n,positions),a0,entry_steps,c,Is,sb,rb) \<Rightarrow>
      lp_source_neutral_check P q n positions a0 entry_steps c Is sb rb
    | _ \<Rightarrow> False)"

theorem check_lp_source_neutral_xml_sound:
  assumes parsed: "parse_xml_string lp_source_neutral_parser xml =
    Right (P,(q,n,positions),a0,entry_steps,c,Is,sb,rb)"
    and ok: "check_lp_source_neutral_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=n \<and> (\<forall>i\<in>set positions. i<n \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_source_neutral_check_sound)
    (use parsed ok in \<open>simp add: check_lp_source_neutral_xml_def\<close>)

definition check_lp_nontermination_all_xml where
  "check_lp_nontermination_all_xml xml =
    (check_lp_nontermination_full_xml xml \<or> check_lp_source_unify_xml xml \<or>
      check_lp_source_neutral_xml xml \<or> check_lp_recurrent_pair_xml xml \<or>
      check_lp_pattern_loop_xml xml \<or> check_lp_affine_loop_xml xml)"

end
