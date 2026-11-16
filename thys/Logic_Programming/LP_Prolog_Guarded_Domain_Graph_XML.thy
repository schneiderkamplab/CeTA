theory LP_Prolog_Guarded_Domain_Graph_XML
 imports LP_Prolog_Guarded_Domain_Graph_NO LP_Prolog_Domain_Graph_XML
begin

definition lpp_guarded_module_parser where
 "lpp_guarded_module_parser =
  (XMLdo (STR ''cut'') {
   segments\<leftarrow>xml_many (STR ''segments'') (xml_many (STR ''segment'') lpp_domain_prefix_parser id) id;
   m\<leftarrow>lpp_domain_module_parser;
   xml_return (LPPGuardedCut segments m)}) XMLor
  xml_singleton (STR ''plain'') lpp_domain_module_parser LPPGuardedPlain XMLor
  (XMLdo (STR ''choice'') {
   g\<leftarrow>xml_singleton (STR ''guard'') lpp_scalar_guard_parser id;
   h\<leftarrow>xml_singleton (STR ''opposite'') lpp_scalar_guard_parser id;
   a\<leftarrow>xml_singleton (STR ''left'') lpp_domain_module_parser id;
   b\<leftarrow>xml_singleton (STR ''right'') lpp_domain_module_parser id;
   xml_return (LPPGuardedChoice g h a b)})"

definition lpp_guarded_domain_graph_parser where
 "lpp_guarded_domain_graph_parser = XMLdo (STR ''prologGuardedDomainGraphNonterminationProof'') {
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
 modules\<leftarrow>xml_many (STR ''modules'') lpp_guarded_module_parser id;
 xml_return (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,start_index,modules)}"

definition check_lpp_guarded_domain_graph_xml where
 "check_lpp_guarded_domain_graph_xml xml = (case parse_xml_string lpp_guarded_domain_graph_parser xml of
 Right (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,start_index,modules) \<Rightarrow>
 profile = ''iso-rational-libraries-v1'' \<and> version=1 \<and>
 lpp_guarded_domain_graph_source_check fuel P q modes argv initial_steps core actuals pending saved observations initial_recipes start_index modules
 | _ \<Rightarrow> False)"

theorem check_lpp_guarded_domain_graph_xml_sound:
 assumes parsed: "parse_xml_string lpp_guarded_domain_graph_parser xml =
   Right (profile,version,P,q,modes,fuel,argv,initial_steps,core,actuals,pending,saved,observations,initial_recipes,start_index,modules)"
 and checked: "check_lpp_guarded_domain_graph_xml xml"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 have ok: "lpp_guarded_domain_graph_source_check fuel P q modes argv initial_steps core actuals pending saved observations initial_recipes start_index modules"
   using parsed checked by (simp add: check_lpp_guarded_domain_graph_xml_def)
 show ?thesis by (rule lpp_guarded_domain_graph_source_sound[OF ok])
qed

ML \<open>
val checked = [@{thm check_lpp_guarded_domain_graph_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence XML dependency" else ();
\<close>
end
