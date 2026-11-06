theory LP_Prolog_Partial_Integer_XML
  imports LP_Prolog_Partial_Integer_Check LP_Prolog_Integer_Call_XML
begin

definition lpp_partial_call_parser where
  "lpp_partial_call_parser  =  XMLdo (STR ''callEdge'') {
    from_loc\<leftarrow>xml_text (STR ''from''); to_loc\<leftarrow>xml_text (STR ''to'');
    c\<leftarrow>xml_nat (STR ''clause'');
    xs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    ops\<leftarrow>xml_many (STR ''operations'') lpp_recurrence_operation_parser id;
    target_pred\<leftarrow>xml_text (STR ''targetPredicate'');
    outputs\<leftarrow>xml_many (STR ''outputs'') lpp_integer_expression_parser id;
    failures\<leftarrow>xml_many (STR ''failedClauses'') lpp_arithmetic_failure_parser id;
    observed_inputs\<leftarrow>xml_many (STR ''observedInputs'') (xml_nat (STR ''position'')) id;
    observed_outputs\<leftarrow>xml_many (STR ''observedOutputs'') (xml_nat (STR ''position'')) id;
    actual_terms\<leftarrow>xml_many (STR ''argumentTerms'') lpc_term_parser id;
    later_goals\<leftarrow>xml_many (STR ''pendingGoals'') lpc_goal_parser id;
    xml_return (from_loc,to_loc,\<lparr>lpp_call_clause = c,lpp_call_variables = xs,lpp_call_prefix = ops,
      lpp_call_target = target_pred,lpp_call_outputs = outputs,lpp_call_failures = failures,
      lpp_partial_inputs = observed_inputs,lpp_partial_outputs = observed_outputs,
      lpp_partial_terms = actual_terms,lpp_partial_later = later_goals\<rparr>)}"

definition lpp_partial_integer_calls_parser where
  "lpp_partial_integer_calls_parser  =  XMLdo (STR ''prologPartialIntegerCallsProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    masks\<leftarrow>xml_many (STR ''observations'') (XMLdo (STR ''observation'') {
      predicate\<leftarrow>xml_text (STR ''predicate''); arity\<leftarrow>xml_nat (STR ''arity'');
      positions\<leftarrow>xml_many (STR ''positions'') (xml_nat (STR ''position'')) id;
      xml_return ((predicate,arity),positions)}) id;
    bindings\<leftarrow>xml_many (STR ''interfaces'') (XMLdo (STR ''interface'') {
      loc\<leftarrow>xml_text (STR ''location''); predicate\<leftarrow>xml_text (STR ''predicate'');
      coordinates\<leftarrow>xml_many (STR ''coordinates'') (xml_text (STR ''var'')) id;
      xml_return (loc,predicate,coordinates)}) id;
    call_edges\<leftarrow>xml_many (STR ''callEdges'') lpp_partial_call_parser id;
    child\<leftarrow>xml_singleton (STR ''numericChild'') its4_cpf_parser id;
    xml_return (profile,P,q,modes,masks,bindings,call_edges,child)}"

definition check_lpp_partial_integer_calls_xml where
  "check_lpp_partial_integer_calls_xml xml  =  (case parse_xml_string lpp_partial_integer_calls_parser xml of
    Right (profile,P,q,modes,masks,bindings,call_edges,(child,child_answer,prf)) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and> \<not>child_answer \<and>
      lpp_check_partial_integer_calls P q modes masks bindings call_edges child prf
    | _ \<Rightarrow> False)"

theorem check_lpp_partial_integer_calls_xml_sound:
  assumes parsed: "parse_xml_string lpp_partial_integer_calls_parser xml  = 
    Right (profile,P,q,modes,masks,bindings,call_edges,(child,child_answer,prf))"
    and checked: "check_lpp_partial_integer_calls_xml xml"
  shows "\<exists>argv. length argv = length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have source_check: "lpp_check_partial_integer_calls P q modes masks bindings call_edges child prf"
    using parsed checked by (simp add: check_lpp_partial_integer_calls_xml_def)
  show ?thesis by (rule lpp_check_partial_integer_calls_sound[OF source_check])
qed

ML \<open>
val checked  =  [@{thm check_lpp_partial_integer_calls_xml_sound}];
val oracles  =  map (fst o fst) o Thm_Deps.all_oracles;
val inherited  =  oracles [@{thm check_its4_sound}];
val _  =  if Thm_Deps.has_skip_proof checked orelse
  exists (fn n  => not (member (op  = ) inherited n)) (oracles checked)
  then error "Untrusted arithmetic call XML dependency" else ();
\<close>
end
