theory LP_Prolog_NO_Call_Trace_XML
 imports LP_Prolog_NO_Call_Trace_Source LP_Prolog_Binary64_NO_XML LP_Cut_Return_XML
begin

definition lpp_call_trace_edge_parser where
 "lpp_call_trace_edge_parser = XMLdo (STR ''callTrace'') {
    a\<leftarrow>xml_singleton (STR ''call'') lpc_term_parser id;
    steps\<leftarrow>xml_many (STR ''steps'') (XMLdo (STR ''step'') {
      action\<leftarrow>lpp_machine_no_action_parser;
      s\<leftarrow>lpc_return_state_parser; xml_return (action,s)}) id;
    xml_return (a,steps)}"

definition lpp_call_trace_certificate_parser where
 "lpp_call_trace_certificate_parser = XMLdo (STR ''prologCallTraceNonterminationProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    version\<leftarrow>xml_nat (STR ''version'');
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    argv\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
    initial_steps\<leftarrow>xml_many (STR ''prefix'') (XMLdo (STR ''step'') {
      action\<leftarrow>lpp_machine_no_action_parser;
      s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id; xml_return (action,s)}) id;
    a\<leftarrow>xml_singleton (STR ''core'') lpc_term_parser id;
    rest\<leftarrow>xml_many (STR ''pending'') lpc_goal_parser id;
    saved\<leftarrow>xml_many (STR ''saved'') lpc_entry_parser id;
    reserved\<leftarrow>xml_many (STR ''reserved'') (xml_nat (STR ''scope'')) id;
    vs\<leftarrow>xml_many (STR ''interface'') (xml_text (STR ''var'')) id;
    calls\<leftarrow>xml_many (STR ''calls'') lpc_term_parser id;
    edges\<leftarrow>xml_many (STR ''traces'') lpp_call_trace_edge_parser id;
    xml_return (profile,version,P,q,modes,fuel,argv,initial_steps,a,rest,saved,reserved,vs,calls,edges)}"

definition check_lpp_call_trace_xml where
 "check_lpp_call_trace_xml xml = (case parse_xml_string lpp_call_trace_certificate_parser xml of
   Right (profile,version,P,q,modes,fuel,argv,initial_steps,a,rest,saved,reserved,vs,calls,edges) \<Rightarrow>
    profile = ''iso-rational-libraries-v1'' \<and> version=1 \<and>
    lpp_no_call_trace_check_source fuel P q modes argv initial_steps a rest saved reserved vs calls edges
   | _ \<Rightarrow> False)"

theorem check_lpp_call_trace_xml_sound:
 assumes parsed: "parse_xml_string lpp_call_trace_certificate_parser xml =
   Right (profile,version,P,q,modes,fuel,argv,initial_steps,a,rest,saved,reserved,vs,calls,edges)"
   and ok: "check_lpp_call_trace_xml xml"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not> SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 have checked: "lpp_no_call_trace_check_source fuel P q modes argv initial_steps a rest saved reserved vs calls edges"
   using parsed ok by (simp add: check_lpp_call_trace_xml_def)
 show ?thesis by (rule lpp_no_call_trace_check_source_sound[OF checked])
qed

ML \<open>
val checked = [@{thm check_lpp_call_trace_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted original-query recurrence XML" else ();
\<close>
end
