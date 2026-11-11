theory LP_Prolog_Ground_Integer_NO_XML
  imports LP_Prolog_Ground_Integer_NO_Profile LP_Prolog_Integer_NO_XML LP_Prolog_Success_Types_XML LP_Prolog_Stable_Profile_Operations
begin

definition lpp_ground_integer_no_action_parser where
  "lpp_ground_integer_no_action_parser =
    (xml_change lpp_integer_no_action_parser (\<lambda>a. xml_return (LPPGIBase a))) XMLor
    (XMLdo (STR ''integerComparison'') {
      left\<leftarrow>xml_singleton (STR ''left'') lpp_integer_expression_parser id;
      right\<leftarrow>xml_singleton (STR ''right'') lpp_integer_expression_parser id;
      held\<leftarrow>xml_bool (STR ''holds''); xml_return (LPPGICompare left right held)})"

definition lpp_ground_integer_no_certificate_parser where
  "lpp_ground_integer_no_certificate_parser = XMLdo (STR ''prologGroundIntegerSourceNonterminationProof'') {
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
      action\<leftarrow>lpp_ground_integer_no_action_parser; s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      xml_return (action,s)}) id;
    steps\<leftarrow>xml_many (STR ''loop'') (XMLdo (STR ''step'') {
      action\<leftarrow>lpp_ground_integer_no_action_parser; s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      xml_return (action,s)}) id;
    xml_return (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)}"

definition check_lpp_ground_integer_no_xml where
  "check_lpp_ground_integer_no_xml xml = (case parse_xml_string lpp_ground_integer_no_certificate_parser xml of
    Right (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and>
      lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps
    | _ \<Rightarrow> False)"

theorem check_lpp_ground_integer_no_xml_sound:
  assumes parsed: "parse_xml_string lpp_ground_integer_no_certificate_parser xml =
    Right (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and ok: "check_lpp_ground_integer_no_xml xml"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lpp_builtin_source P lpp_ground_integer_no_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have checked: "lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps"
    using parsed ok by (simp add: check_lpp_ground_integer_no_xml_def)
  show ?thesis by (rule lpp_ground_integer_no_check_source_sound[OF checked])
qed

corollary check_lpp_ground_integer_no_xml_profile_sound:
  assumes parsed: "parse_xml_string lpp_ground_integer_no_certificate_parser xml =
    Right (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and ok: "check_lpp_ground_integer_no_xml xml"
    and compatible: "lpp_stable_integer_operations operation"
  shows "\<not> SN_on (lpp_builtin_source P (lpp_stable_source_builtin operation))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have checked: "lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps"
    using parsed ok by (simp add: check_lpp_ground_integer_no_xml_def)
  show ?thesis by (rule lpp_ground_integer_no_profile_sound[OF checked compatible])
qed

corollary check_lpp_ground_integer_no_xml_fixed_profile_sound:
  assumes parsed: "parse_xml_string lpp_ground_integer_no_certificate_parser xml =
    Right (profile,P,q,modes,fuel,argv,a,before,after,initial_steps,steps)"
    and ok: "check_lpp_ground_integer_no_xml xml"
  shows "\<not> SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
  by (rule check_lpp_ground_integer_no_xml_profile_sound[OF parsed ok lpp_stable_profile_integer_compatible])

ML \<open>
val checked = [@{thm check_lpp_ground_integer_no_xml_fixed_profile_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ground integer XML dependency" else ();
\<close>

end
