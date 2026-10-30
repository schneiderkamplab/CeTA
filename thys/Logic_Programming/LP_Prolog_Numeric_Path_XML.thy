theory LP_Prolog_Numeric_Path_XML
  imports LP_Prolog_Numeric_Valuation LP_Prolog_Numeric_Row_XML
begin

definition lpp_numeric_endpoint_parser where
  "lpp_numeric_endpoint_parser = XMLdo (STR ''endpoint'') {
    coordinate\<leftarrow>xml_text (STR ''coordinate'');
    t\<leftarrow>lpc_term_parser; e\<leftarrow>lpp_integer_expression_parser;
    xml_return (coordinate,t,e)}"

definition lpp_numeric_path_parser where
  "lpp_numeric_path_parser = XMLdo (STR ''prologNumericPath'') {
    K\<leftarrow>xml_many (STR ''known'') (xml_text (STR ''var'')) id;
    inputs\<leftarrow>xml_many (STR ''inputs'') lpp_numeric_endpoint_parser id;
    outputs\<leftarrow>xml_many (STR ''outputs'') lpp_numeric_endpoint_parser id;
    observations\<leftarrow>xml_many (STR ''observations'') lpp_numeric_observation_parser id;
    numeric_tests\<leftarrow>xml_many (STR ''tests'') (XMLdo (STR ''test'') {
      comparison\<leftarrow>lpp_numeric_comparison_parser;
      a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser;
      xml_return (comparison,a,b)}) id;
    bindings\<leftarrow>xml_many (STR ''bindings'') (XMLdo (STR ''binding'') {
      x\<leftarrow>xml_text (STR ''var''); v\<leftarrow>trans_var_parser; xml_return (x,v)}) id;
    formula\<leftarrow>xml_singleton (STR ''formula'') (formula_parser lpp_numeric_tatom_parser) id;
    xml_return (K,inputs,outputs,observations,numeric_tests,bindings,formula)}"

definition check_lpp_numeric_path_xml where
  "check_lpp_numeric_path_xml xml = (case parse_xml_string lpp_numeric_path_parser xml of
    Right (K,inputs,outputs,observations,numeric_tests,bindings,formula) \<Rightarrow>
      lpp_check_numeric_path K inputs outputs observations numeric_tests bindings formula \<and>
      lpp_check_numeric_bindings inputs outputs bindings \<and>
      list_all (\<lambda>b. fst b\<in>set K) bindings
    | _ \<Rightarrow> False)"

lemma check_lpp_numeric_path_xml_sound:
  assumes parsed: "parse_xml_string lpp_numeric_path_parser xml =
      Right (K,inputs,outputs,observations,numeric_tests,bindings,formula)"
    and checked: "check_lpp_numeric_path_xml xml"
    and observed: "list_all (lpp_numeric_observation_holds eta) observations"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (lpp_numeric_rename bindings x))"
    and inputs: "\<And>name t e. (name,t,e)\<in>set inputs \<Longrightarrow> lp_ieval t eta=lpp_integer_value (rho (Pre name))"
    and outputs: "\<And>name t e. (name,t,e)\<in>set outputs \<Longrightarrow> lp_ieval t eta=lpp_integer_value (rho (Post name))"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula"
proof -
  have path: "lpp_check_numeric_path K inputs outputs observations numeric_tests bindings formula"
    using parsed checked by (auto simp: check_lpp_numeric_path_xml_def)
  show ?thesis by (rule lpp_check_numeric_path_sound[where eta=eta, OF path observed typed inputs outputs])
qed

text \<open>The parser returns the complete subject for binding by the parent
source graph. Acceptance is conditional on the source observations, integer
context and endpoint interpretation; it is not a standalone source verdict.\<close>
end
