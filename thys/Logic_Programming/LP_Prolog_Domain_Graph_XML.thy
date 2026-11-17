theory LP_Prolog_Domain_Graph_XML
 imports LP_Prolog_Domain_Graph_NO LP_Prolog_Scalar_Domain_XML
begin

definition lpp_head_failure_parser where
 "lpp_head_failure_parser =
 (XMLdo (STR ''failure'') {
   V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
   guards\<leftarrow>xml_many (STR ''guards'') lpp_scalar_guard_parser id;
   failed\<leftarrow>xml_singleton (STR ''failed'') lpp_scalar_guard_parser id;
   xml_return (LPPVariableFailure (V,guards,failed))}) XMLor
 (XMLdo (STR ''headApart'') {
   i\<leftarrow>xml_nat (STR ''left''); j\<leftarrow>xml_nat (STR ''right'');
   xml_return (LPPHeadApart i j)}) XMLor
 (XMLdo (STR ''patternFailure'') {
   V\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
   constants\<leftarrow>xml_many (STR ''constants'')
     (xml_leaf (STR ''variable'') None XMLor xml_singleton (STR ''constant'') (xml_text (STR ''symbol'')) Some) id;
   guards\<leftarrow>xml_many (STR ''guards'') lpp_scalar_guard_parser id;
   failed\<leftarrow>xml_singleton (STR ''failed'') lpp_scalar_guard_parser id;
   xml_return (LPPPatternFailure V constants guards failed)})"

definition lpp_domain_module_parser where
 "lpp_domain_module_parser = XMLdo (STR ''module'') {
 q\<leftarrow>xml_text (STR ''predicate'');
 observations\<leftarrow>xml_many (STR ''observations'') lpp_domain_observation_parser id;
 selection\<leftarrow>xml_nat (STR ''selection'');
 H\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
 actions\<leftarrow>xml_many (STR ''actions'') lpp_domain_prefix_parser id;
 outputs\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
 recipes\<leftarrow>xml_many (STR ''recipes'') lpp_scalar_recipe_parser id;
 failures\<leftarrow>xml_many (STR ''failures'') lpp_head_failure_parser id;
 dest\<leftarrow>xml_nat (STR ''destination'');
 xml_return (LPPDomainModule q observations selection H actions outputs recipes failures dest)}"

definition lpp_domain_graph_parser where
 "lpp_domain_graph_parser = XMLdo (STR ''prologDomainGraphNonterminationProof'') {
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
 start_index\<leftarrow>xml_nat (STR ''entry'');
 modules\<leftarrow>xml_many (STR ''modules'') lpp_domain_module_parser id;
 xml_return (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,start_index,modules)}"

definition check_lpp_domain_graph_xml where
 "check_lpp_domain_graph_xml xml = (case parse_xml_string lpp_domain_graph_parser xml of
 Right (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,start_index,modules) \<Rightarrow>
 profile = ''iso-rational-libraries-v1'' \<and> version=1 \<and>
 lpp_domain_graph_source_check fuel P q modes argv initial_steps core actuals pending saved observations initial_recipes start_index modules
 | _ \<Rightarrow> False)"

theorem check_lpp_domain_graph_xml_sound:
 assumes parsed: "parse_xml_string lpp_domain_graph_parser xml =
   Right (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,start_index,modules)"
 and checked: "check_lpp_domain_graph_xml xml"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 have ok: "lpp_domain_graph_source_check fuel P q modes argv initial_steps core actuals pending saved observations initial_recipes start_index modules"
   using parsed checked by (simp add: check_lpp_domain_graph_xml_def)
 show ?thesis by (rule lpp_domain_graph_source_sound[OF ok])
qed

ML \<open>
val checked = [@{thm check_lpp_domain_graph_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence XML dependency" else ();
\<close>
end
