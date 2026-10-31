theory LP_Prolog_Numeric_Row_XML
  imports LP_Prolog_Numeric_Row_Check LP_Prolog_Integer_Source
    LP_Prolog_Success_Types_XML ITS_Ext.IA4_Parser
begin

text \<open>Reuse the shared CPF4 arithmetic parser with a container-supported
encoding of transition variables, then decode the tags. This changes no parsed
arithmetic operation and introduces no category-specific arithmetic parser.\<close>
fun lpp_encode_transition_variable where
  "lpp_encode_transition_variable (Pre x) = (x,0::nat)"
| "lpp_encode_transition_variable (Post x) = (x,1)"
| "lpp_encode_transition_variable (Intermediate x) = (x,2)"
fun lpp_decode_transition_variable where
  "lpp_decode_transition_variable (x,n) = (if n=0 then Pre x else if n=1 then Post x else Intermediate x)"
lemma lpp_transition_variable_roundtrip[simp]:
  "lpp_decode_transition_variable (lpp_encode_transition_variable v)=v"
  by (cases v) simp_all

definition lpp_numeric_tatom_parser where
  "lpp_numeric_tatom_parser = xml_change
    (ia4_bexp_parser' (xml_change trans_var_parser (xml_return o lpp_encode_transition_variable)))
    (xml_return o rename_vars lpp_decode_transition_variable)"

definition lpp_numeric_comparison_parser where
  "lpp_numeric_comparison_parser =
    (XMLdo (STR ''less'') {xml_return LPPIntLess}) XMLor
    (XMLdo (STR ''lessEqual'') {xml_return LPPIntLessEqual}) XMLor
    (XMLdo (STR ''equal'') {xml_return LPPIntEqual}) XMLor
    (XMLdo (STR ''notEqual'') {xml_return LPPIntNotEqual})"

definition lpp_return_shape_parser where
  "lpp_return_shape_parser =
    (XMLdo (STR ''any'') {xml_return LPReturnAny}) XMLor
    (XMLdo (STR ''ground'') {xml_return LPReturnGround}) XMLor
    (xml_change (xml_nat (STR ''node'')) (\<lambda>i. xml_return (LPReturnShape i)))"

definition lpp_return_grammar_parser where
  "lpp_return_grammar_parser = xml_many (STR ''grammar'')
    (xml_many (STR ''shapeNode'') (XMLdo (STR ''production'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      children\<leftarrow>xml_many (STR ''arguments'') lpp_return_shape_parser id;
      xml_return (f,children)}) id) id"

definition lpp_shape_observation_parser where
  "lpp_shape_observation_parser = XMLdo (STR ''returnShape'') {
    G\<leftarrow>lpp_return_grammar_parser;
    shape\<leftarrow>xml_singleton (STR ''shape'') lpp_return_shape_parser id;
    t\<leftarrow>xml_singleton (STR ''term'') lpc_term_parser id;
    xml_return (LPPOShape G shape t)}"

definition lpp_numeric_observation_parser where
  "lpp_numeric_observation_parser = lpp_shape_observation_parser XMLor
    (XMLdo (STR ''sourceEquation'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser; xml_return (LPPOEquation a b)}) XMLor
    (xml_singleton (STR ''groundGuard'') lpc_term_parser LPPOGround) XMLor
    (XMLdo (STR ''evaluationGuard'') {e\<leftarrow>lpc_term_parser; t\<leftarrow>lpc_term_parser; xml_return (LPPOEvaluation e t)}) XMLor
    (xml_change (xml_singleton (STR ''comparisonGuard'') lpc_term_parser id)
      (\<lambda>t. case t of Fun (LPCUser f) [a,b] \<Rightarrow>
        (case lpp_source_comparison f of None \<Rightarrow> xml_error (STR ''unsupported numeric comparison'')
         | Some (comparison,reversed) \<Rightarrow> xml_return
           (LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)))
       | _ \<Rightarrow> xml_error (STR ''invalid numeric source observation'')))"

definition lpp_numeric_row_guard_parser where
  "lpp_numeric_row_guard_parser = XMLdo (STR ''prologNumericGuard'') {
    K\<leftarrow>xml_many (STR ''known'') (xml_text (STR ''var'')) id;
    observation\<leftarrow>xml_singleton (STR ''source'') lpp_numeric_observation_parser id;
    numeric_test\<leftarrow>(XMLdo (STR ''evidence'') {
      comparison\<leftarrow>lpp_numeric_comparison_parser;
      a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser;
      xml_return (comparison,a,b)});
    bindings\<leftarrow>xml_many (STR ''bindings'') (XMLdo (STR ''binding'') {
      x\<leftarrow>xml_text (STR ''var''); v\<leftarrow>trans_var_parser; xml_return (x,v)}) id;
    formula\<leftarrow>xml_singleton (STR ''formula'') (formula_parser lpp_numeric_tatom_parser) id;
    xml_return (K,observation,numeric_test,bindings,formula)}"

definition check_lpp_numeric_row_guard_xml where
  "check_lpp_numeric_row_guard_xml xml = (case parse_xml_string lpp_numeric_row_guard_parser xml of
    Right (K,observation,numeric_test,bindings,formula) \<Rightarrow>
      lpp_check_numeric_row_guard K observation numeric_test bindings formula
    | _ \<Rightarrow> False)"

theorem check_lpp_numeric_row_guard_xml_sound:
  assumes parsed: "parse_xml_string lpp_numeric_row_guard_parser xml = Right (K,observation,numeric_test,bindings,formula)"
    and checked: "check_lpp_numeric_row_guard_xml xml"
    and observed: "lpp_numeric_observation_holds eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (lpp_numeric_rename bindings x))"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula" "IA4.formula formula"
  using lpp_check_numeric_row_guard_sound[of K observation numeric_test bindings formula eta rho]
    parsed checked observed typed by (auto simp: check_lpp_numeric_row_guard_xml_def)

text \<open>This is a conditional source-to-numeric guard receipt. It is not a
root proof. The parent must reconstruct the complete graph and all numeric rows,
establish the domain before each operation, and discharge every child.\<close>
end
