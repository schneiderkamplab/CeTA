theory LP_Prolog_Integer_Call_XML
  imports LP_Prolog_Integer_Call_Check LP_Prolog_Integer_Recurrence_XML
begin

definition lpp_arithmetic_failure_parser where
  "lpp_arithmetic_failure_parser  =  XMLdo (STR ''failedClause'') {
    c\<leftarrow>xml_nat (STR ''clause'');
    xs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    ops\<leftarrow>xml_many (STR ''operations'') lpp_recurrence_operation_parser id;
    f\<leftarrow>xml_text (STR ''predicate''); comparison\<leftarrow>lpp_numeric_comparison_parser;
    reversed\<leftarrow>xml_bool (STR ''reversed'');
    a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser;
    xml_return \<lparr>lpp_failure_clause = c,lpp_failure_variables = xs,lpp_failure_prefix = ops,
      lpp_failure_predicate = f,lpp_failure_comparison = comparison,lpp_failure_reversed = reversed,
      lpp_failure_left = a,lpp_failure_right = b\<rparr>}"

definition lpp_arithmetic_call_parser where
  "lpp_arithmetic_call_parser  =  XMLdo (STR ''callEdge'') {
    from_loc\<leftarrow>xml_text (STR ''from''); to_loc\<leftarrow>xml_text (STR ''to'');
    c\<leftarrow>xml_nat (STR ''clause'');
    xs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    ops\<leftarrow>xml_many (STR ''operations'') lpp_recurrence_operation_parser id;
    target_pred\<leftarrow>xml_text (STR ''targetPredicate'');
    outputs\<leftarrow>xml_many (STR ''outputs'') lpp_integer_expression_parser id;
    failures\<leftarrow>xml_many (STR ''failedClauses'') lpp_arithmetic_failure_parser id;
    xml_return (from_loc,to_loc,\<lparr>lpp_call_clause = c,lpp_call_variables = xs,lpp_call_prefix = ops,
      lpp_call_target = target_pred,lpp_call_outputs = outputs,lpp_call_failures = failures\<rparr>)}"

definition lpp_integer_calls_parser where
  "lpp_integer_calls_parser  =  XMLdo (STR ''prologIntegerCallsProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    bindings\<leftarrow>xml_many (STR ''interfaces'') (XMLdo (STR ''interface'') {
      loc\<leftarrow>xml_text (STR ''location''); predicate\<leftarrow>xml_text (STR ''predicate'');
      coordinates\<leftarrow>xml_many (STR ''coordinates'') (xml_text (STR ''var'')) id;
      xml_return (loc,predicate,coordinates)}) id;
    call_edges\<leftarrow>xml_many (STR ''callEdges'') lpp_arithmetic_call_parser id;
    child\<leftarrow>xml_singleton (STR ''numericChild'') its4_cpf_parser id;
    xml_return (profile,P,q,modes,bindings,call_edges,child)}"

definition check_lpp_integer_calls_xml where
  "check_lpp_integer_calls_xml xml  =  (case parse_xml_string lpp_integer_calls_parser xml of
    Right (profile,P,q,modes,bindings,call_edges,(child,child_answer,prf)) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and> \<not>child_answer \<and>
      lpp_check_integer_calls P q modes bindings call_edges child prf
    | _ \<Rightarrow> False)"

theorem check_lpp_integer_calls_xml_sound:
  assumes parsed: "parse_xml_string lpp_integer_calls_parser xml  = 
    Right (profile,P,q,modes,bindings,call_edges,(child,child_answer,prf))"
    and checked: "check_lpp_integer_calls_xml xml"
  shows "\<exists>argv. length argv = length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have source_check: "lpp_check_integer_calls P q modes bindings call_edges child prf"
    using parsed checked by (simp add: check_lpp_integer_calls_xml_def)
  show ?thesis by (rule lpp_check_integer_calls_sound[OF source_check])
qed

ML \<open>
val checked  =  [@{thm check_lpp_integer_calls_xml_sound}];
val oracles  =  map (fst o fst) o Thm_Deps.all_oracles;
val inherited  =  oracles [@{thm check_its4_sound}];
val _  =  if Thm_Deps.has_skip_proof checked orelse
  exists (fn n  => not (member (op  = ) inherited n)) (oracles checked)
  then error "Untrusted arithmetic call XML dependency" else ();
\<close>
end
