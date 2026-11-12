theory LP_Prolog_Binary64_NO_XML
 imports LP_Prolog_Binary64_NO LP_Prolog_Ground_Integer_NO_XML
begin

definition lpp_machine_scalar_parser where
 "lpp_machine_scalar_parser =
   xml_change (xml_int (STR ''integer'')) (xml_return \<circ> LPPMachineInteger) XMLor
   xml_change (xml_nat (STR ''binary64'')) (xml_return \<circ> LPPMachineFloat)"

partial_function (sum_bot) lpp_machine_expression_parser :: "lpp_machine_expression xmlt" where
[code]: "lpp_machine_expression_parser x = (
   xml_singleton (STR ''machineLiteral'') lpp_machine_scalar_parser LPPMachineLiteral XMLor
   (XMLdo (STR ''machineBinary'') {f\<leftarrow>xml_text (STR ''operator'');
     a\<leftarrow>lpp_machine_expression_parser; b\<leftarrow>lpp_machine_expression_parser;
     xml_return (LPPMachineBinary f a b)})) x"

definition lpp_machine_no_action_parser where
 "lpp_machine_no_action_parser =
   xml_change lpp_ground_integer_no_action_parser (xml_return \<circ> LPPMBase) XMLor
   xml_singleton (STR ''machineIs'') lpp_machine_expression_parser LPPMIs XMLor
   (XMLdo (STR ''machineCompare'') {
     a\<leftarrow>xml_singleton (STR ''left'') lpp_machine_expression_parser id;
     b\<leftarrow>xml_singleton (STR ''right'') lpp_machine_expression_parser id;
     held\<leftarrow>xml_bool (STR ''holds''); xml_return (LPPMCompare a b held)}) XMLor
   (XMLdo (STR ''machineIntegerTest'') {
     v\<leftarrow>xml_singleton (STR ''machineLiteral'') lpp_machine_scalar_parser id;
     xml_return (LPPMInteger v)}) XMLor
   (XMLdo (STR ''opaqueProbe'') {
     m\<leftarrow>xml_nat (STR ''scope''); n\<leftarrow>xml_nat (STR ''innerScope'');
     xml_return (LPPMProbe m n)})"

definition lpp_machine_no_certificate_parser where
  "lpp_machine_no_certificate_parser = XMLdo (STR ''prologBinary64SourceNonterminationProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
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
      action\<leftarrow>lpp_machine_no_action_parser; s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      xml_return (action,s)}) id;
    steps\<leftarrow>xml_many (STR ''loop'') (XMLdo (STR ''step'') {
      action\<leftarrow>lpp_machine_no_action_parser; s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      xml_return (action,s)}) id;
    xml_return (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)}"

definition check_lpp_machine_no_xml where
  "check_lpp_machine_no_xml xml = (case parse_xml_string lpp_machine_no_certificate_parser xml of
    Right (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and>
      lpp_machine_no_check_source fuel P q modes argv a before after initial_steps steps
    | _ \<Rightarrow> False)"

theorem check_lpp_machine_no_xml_sound:
 assumes parsed: "parse_xml_string lpp_machine_no_certificate_parser xml =
   Right (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
   and ok: "check_lpp_machine_no_xml xml"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 have checked: "lpp_machine_no_check_source fuel P q modes argv a before after initial_steps steps"
   using parsed ok by (simp add: check_lpp_machine_no_xml_def)
 show ?thesis by (rule lpp_machine_no_check_source_sound[OF checked])
qed

ML \<open>
val checked = [@{thm check_lpp_machine_no_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 XML dependency" else ();
\<close>
end
