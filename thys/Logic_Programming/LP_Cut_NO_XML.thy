theory LP_Cut_NO_XML
  imports LP_Cut_NO_Certificate LP_Cut_Table_XML
begin

definition lpc_no_action_parser where
  "lpc_no_action_parser =
    (XMLdo (STR ''admin'') {xml_return LPCNOAdmin}) XMLor
    (XMLdo (STR ''case'') {m\<leftarrow>xml_nat (STR ''scope''); xml_return (LPCNOCase m)}) XMLor
    (XMLdo (STR ''meta'') {m\<leftarrow>xml_nat (STR ''scope'');
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (LPCNOMeta m body)}) XMLor
    (XMLdo (STR ''resolve'') {k\<leftarrow>xml_nat (STR ''prefix'');
      V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
      images\<leftarrow>xml_many (STR ''images'') lpc_term_parser id; xml_return (LPCNOResolve k V images)}) XMLor
    (XMLdo (STR ''resolveSwap'') {k\<leftarrow>xml_nat (STR ''prefix'');
      V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
      images\<leftarrow>xml_many (STR ''images'') lpc_term_parser id;
      x\<leftarrow>xml_text (STR ''from''); y\<leftarrow>xml_text (STR ''to'');
      xml_return (LPCNOResolveSwap k V images x y)}) XMLor
    (XMLdo (STR ''unify'') {V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
      images\<leftarrow>xml_many (STR ''images'') lpc_term_parser id; xml_return (LPCNOUnify V images)}) XMLor
    (XMLdo (STR ''backtrack'') {k\<leftarrow>xml_nat (STR ''prefix''); xml_return (LPCNOBacktrack k)}) XMLor
    (XMLdo (STR ''unifyFail'') {xml_return LPCNOUnifyFail})"

definition lpc_no_trace_parser where
  "lpc_no_trace_parser tag = xml_many tag (XMLdo (STR ''step'') {
    a\<leftarrow>lpc_no_action_parser; s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
    xml_return (a,s)}) id"

definition lpc_no_certificate_parser where
  "lpc_no_certificate_parser = XMLdo (STR ''lpCutSourceNonterminationProof'') {
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
    initial_steps\<leftarrow>lpc_no_trace_parser (STR ''prefix'');
    steps\<leftarrow>lpc_no_trace_parser (STR ''loop'');
    xml_return (P,q,modes,fuel,argv,a,before,after,initial_steps,steps)}"

definition check_lpc_no_xml where
  "check_lpc_no_xml xml = (case parse_xml_string lpc_no_certificate_parser xml of
    Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps) \<Rightarrow>
      lpc_no_check_source fuel P q modes argv a before after initial_steps steps
    | _ \<Rightarrow> False)"

theorem check_lpc_no_xml_sound:
  assumes parsed: "parse_xml_string lpc_no_certificate_parser xml =
    Right (P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and checked: "check_lpc_no_xml xml"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lp_cut_mgu_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
  by (rule lpc_no_check_source_sound)
    (use parsed checked in \<open>simp add: check_lpc_no_xml_def\<close>)

end
