theory LP_Prolog_Scalar_Domain_XML
 imports LP_Prolog_Scalar_Domain_NO LP_Prolog_Scalar_Recurrence_XML
begin

definition lpp_domain_parser where
 "lpp_domain_parser =
 xml_singleton (STR ''fixed'') lpp_machine_scalar_parser LPPRecurrentFixed XMLor
 xml_leaf (STR ''integerDomain'') LPPRecurrentInteger"
definition lpp_domain_observation_parser where
 "lpp_domain_observation_parser =
 xml_singleton (STR ''observed'') lpp_domain_parser Some XMLor
 xml_leaf (STR ''unobserved'') None"
definition lpp_domain_prefix_parser where
 "lpp_domain_prefix_parser =
 xml_singleton (STR ''guard'') lpp_scalar_guard_parser LPPDomainGuard XMLor
 (XMLdo (STR ''set'') {v\<leftarrow>xml_text (STR ''var'');
 e\<leftarrow>lpp_scalar_template_parser; xml_return (LPPDomainSet v e)})"

definition lpp_domain_recurrence_parser where
 "lpp_domain_recurrence_parser = XMLdo (STR ''prologScalarDomainRecurrenceNonterminationProof'') {
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
 core\<leftarrow>xml_text (STR ''corePredicate'');
 actuals\<leftarrow>xml_many (STR ''coreArguments'') lpc_term_parser id;
 pending\<leftarrow>xml_many (STR ''pending'') lpc_goal_parser id;
 saved\<leftarrow>xml_many (STR ''saved'') lpc_entry_parser id;
 observations\<leftarrow>xml_many (STR ''observations'') lpp_domain_observation_parser id;
 initial_recipes\<leftarrow>xml_many (STR ''initialRecipes'') lpp_scalar_recipe_parser id;
 selection\<leftarrow>xml_nat (STR ''selection'');
 H\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
 actions\<leftarrow>xml_many (STR ''actions'') lpp_domain_prefix_parser id;
 outputs\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
 recipes\<leftarrow>xml_many (STR ''recipes'') lpp_scalar_recipe_parser id;
 failures\<leftarrow>xml_many (STR ''failures'') (XMLdo (STR ''failure'') {
   V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
   guards\<leftarrow>xml_many (STR ''guards'') lpp_scalar_guard_parser id;
   failed\<leftarrow>xml_singleton (STR ''failed'') lpp_scalar_guard_parser id;
   xml_return (V,guards,failed)}) id;
 xml_return (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,selection,H,actions,outputs,recipes,failures)}"

definition check_lpp_domain_recurrence_xml where
 "check_lpp_domain_recurrence_xml xml = (case parse_xml_string lpp_domain_recurrence_parser xml of
 Right (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,selection,H,actions,outputs,recipes,failures) \<Rightarrow>
 profile = ''iso-rational-libraries-v1'' \<and> version=1 \<and>
 lpp_domain_recurrence_source_check fuel P q modes argv initial_steps core actuals pending saved observations initial_recipes selection H actions outputs recipes failures
 | _ \<Rightarrow> False)"

theorem check_lpp_domain_recurrence_xml_sound:
 assumes parsed: "parse_xml_string lpp_domain_recurrence_parser xml =
   Right (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,selection,H,actions,outputs,recipes,failures)"
 and checked: "check_lpp_domain_recurrence_xml xml"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 have ok: "lpp_domain_recurrence_source_check fuel P q modes argv initial_steps core actuals pending saved observations initial_recipes selection H actions outputs recipes failures"
   using parsed checked by (simp add: check_lpp_domain_recurrence_xml_def)
 show ?thesis by (rule lpp_domain_recurrence_source_sound[OF ok])
qed

ML \<open>
val checked = [@{thm check_lpp_domain_recurrence_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence XML dependency" else ();
\<close>
end
