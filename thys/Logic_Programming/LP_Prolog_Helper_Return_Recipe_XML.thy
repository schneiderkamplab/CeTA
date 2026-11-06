theory LP_Prolog_Helper_Return_Recipe_XML
  imports LP_Prolog_Helper_Return_Recipe_Controls LP_Prolog_Integer_Recurrence_XML
begin

text \<open>Recipe evidence is parsed inside its parent source proof. The
original program is supplied by that parent to the recipe checker; no standalone
termination or nontermination conclusion is exposed here.\<close>

definition lpp_helper_return_recipe_parser where
  "lpp_helper_return_recipe_parser = XMLdo (STR ''helperRecipe'') {
    c\<leftarrow>xml_nat (STR ''clause'');
    f\<leftarrow>xml_text (STR ''predicate'');
    hs\<leftarrow>xml_many (STR ''headVariables'') (xml_text (STR ''var'')) id;
    ins\<leftarrow>xml_many (STR ''integerInputs'') (xml_text (STR ''var'')) id;
    ops\<leftarrow>xml_many (STR ''operations'') lpp_recurrence_operation_parser id;
    out_var\<leftarrow>xml_text (STR ''output'');
    e\<leftarrow>xml_singleton (STR ''expression'') lpp_integer_expression_parser id;
    xml_return \<lparr>lpphr_clause = c,lpphr_predicate = f,lpphr_head = hs,lpphr_inputs = ins,
      lpphr_prefix = ops,lpphr_output = out_var,lpphr_expression = e\<rparr>}"

end
