theory LP_Prolog_Scalar_Recurrence_XML
 imports LP_Prolog_Scalar_Recurrence_NO LP_Prolog_Binary64_NO_XML
begin

partial_function (sum_bot) lpp_scalar_template_parser :: "lpp_scalar_template xmlt" where
[code]: "lpp_scalar_template_parser x = (
 xml_change (xml_text (STR ''parameter'')) (xml_return \<circ> LPPScalarParameter) XMLor
 xml_singleton (STR ''literal'') lpp_machine_scalar_parser LPPScalarLiteral XMLor
 (XMLdo (STR ''binary'') {f\<leftarrow>xml_text (STR ''operator'');
   a\<leftarrow>lpp_scalar_template_parser; b\<leftarrow>lpp_scalar_template_parser;
   xml_return (LPPScalarBinary f a b)})) x"

definition lpp_scalar_guard_parser where
 "lpp_scalar_guard_parser =
 (XMLdo (STR ''compare'') {f\<leftarrow>xml_text (STR ''operator'');
   a\<leftarrow>lpp_scalar_template_parser; b\<leftarrow>lpp_scalar_template_parser;
   xml_return (LPPScalarCompare f a b)}) XMLor
 (XMLdo (STR ''isLiteral'') {v\<leftarrow>lpp_machine_scalar_parser;
   e\<leftarrow>lpp_scalar_template_parser; xml_return (LPPScalarIsLiteral v e)})"

definition lpp_scalar_observation_parser where
 "lpp_scalar_observation_parser =
 xml_singleton (STR ''observed'') lpp_machine_scalar_parser Some XMLor
 xml_leaf (STR ''unobserved'') None"
definition lpp_scalar_recipe_parser where
 "lpp_scalar_recipe_parser =
 xml_singleton (STR ''observed'') lpp_scalar_template_parser Some XMLor
 xml_leaf (STR ''unobserved'') None"
definition lpp_scalar_prefix_parser where
 "lpp_scalar_prefix_parser =
 xml_singleton (STR ''guard'') lpp_scalar_guard_parser LPPScalarPrefixGuard XMLor
 xml_leaf (STR ''cut'') LPPScalarPrefixCut"

definition lpp_scalar_recurrence_parser where
 "lpp_scalar_recurrence_parser = XMLdo (STR ''prologScalarRecurrenceNonterminationProof'') {
 profile\<leftarrow>xml_text (STR ''profile'');
 P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
   h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
   body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
 q\<leftarrow>xml_text (STR ''predicate'');
 modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
 observations\<leftarrow>xml_many (STR ''observations'') lpp_scalar_observation_parser id;
 selection\<leftarrow>xml_nat (STR ''selection'');
 H\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
 actions\<leftarrow>xml_many (STR ''actions'') lpp_scalar_prefix_parser id;
 outputs\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
 recipes\<leftarrow>xml_many (STR ''recipes'') lpp_scalar_recipe_parser id;
 failures\<leftarrow>xml_many (STR ''failures'') (XMLdo (STR ''failure'') {
   V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
   guards\<leftarrow>xml_many (STR ''guards'') lpp_scalar_guard_parser id;
   failed\<leftarrow>xml_singleton (STR ''failed'') lpp_scalar_guard_parser id;
   xml_return (V,guards,failed)}) id;
 xml_return (profile,P,q,modes,observations,selection,H,actions,outputs,recipes,failures)}"

definition check_lpp_scalar_recurrence_xml where
 "check_lpp_scalar_recurrence_xml xml = (case parse_xml_string lpp_scalar_recurrence_parser xml of
 Right (profile,P,q,modes,observations,selection,H,actions,outputs,recipes,failures) \<Rightarrow>
 profile = ''iso-rational-libraries-v1'' \<and>
 lpp_check_scalar_recurrence P q modes observations selection H actions outputs recipes failures
 | _ \<Rightarrow> False)"

theorem check_lpp_scalar_recurrence_xml_sound:
 assumes parsed: "parse_xml_string lpp_scalar_recurrence_parser xml =
   Right (profile,P,q,modes,observations,selection,H,actions,outputs,recipes,failures)"
 and checked: "check_lpp_scalar_recurrence_xml xml"
 shows "\<exists>argv. length argv=length modes \<and> list_all ground argv \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 have ok: "lpp_check_scalar_recurrence P q modes observations selection H actions outputs recipes failures"
   using parsed checked by (simp add: check_lpp_scalar_recurrence_xml_def)
 show ?thesis by (rule lpp_check_scalar_recurrence_sound[OF ok])
qed

ML \<open>
val checked = [@{thm check_lpp_scalar_recurrence_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence XML dependency" else ();
\<close>
end
