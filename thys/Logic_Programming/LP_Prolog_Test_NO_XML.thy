theory LP_Prolog_Test_NO_XML
  imports LP_Prolog_Test_NO LP_Cut_NO_XML
begin

definition lpp_no_action_parser where
  "lpp_no_action_parser =
    (xml_singleton (STR ''ordinary'') lpc_no_action_parser LPPNOOrdinary) XMLor
    (XMLdo (STR ''test'') {xml_return LPPNOTest})"

definition lpp_no_certificate_parser where
  "lpp_no_certificate_parser = XMLdo (STR ''prologTestSourceNonterminationProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    A\<leftarrow>xml_many (STR ''predicates'')
      (xml_pair (STR ''signature'') (xml_text (STR ''name'')) (xml_nat (STR ''arity'')) Pair) id;
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    argv\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
    a\<leftarrow>xml_singleton (STR ''core'') lpc_term_parser id;
    before\<leftarrow>xml_many (STR ''before'') lpc_entry_parser id;
    after\<leftarrow>xml_many (STR ''after'') lpc_entry_parser id;
    initial_steps\<leftarrow>xml_many (STR ''prefix'') (XMLdo (STR ''step'') {
      action\<leftarrow>lpp_no_action_parser; s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      xml_return (action,s)}) id;
    steps\<leftarrow>lpc_no_trace_parser (STR ''loop'');
    xml_return (profile,A,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)}"

definition check_lpp_test_no_xml where
  "check_lpp_test_no_xml xml = (case parse_xml_string lpp_no_certificate_parser xml of
    Right (profile,A,P,q,modes,fuel,argv,a,before,after,initial_steps,steps) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and>
      lpp_no_check_source fuel P q modes A argv a before after initial_steps steps
    | _ \<Rightarrow> False)"

theorem check_lpp_test_no_xml_sound:
  assumes parsed: "parse_xml_string lpp_no_certificate_parser xml =
    Right (profile,A,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and ok: "check_lpp_test_no_xml xml"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lp_prolog_test_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have checked: "lpp_no_check_source fuel P q modes A argv a before after initial_steps steps"
    using parsed ok by (simp add: check_lpp_test_no_xml_def)
  show ?thesis by (rule lpp_no_check_source_sound[OF checked])
qed

end
