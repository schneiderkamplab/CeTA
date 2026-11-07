theory LP_Prolog_Stable_Return_XML
 imports LP_Prolog_Stable_Return_Component LP_Prolog_Success_Magnitude_XML LP_Prolog_Stable_Numeric_XML
begin

definition lpp_return_constraint_parser where
  "lpp_return_constraint_parser =
    (XMLdo (STR ''magnitudeNonnegative'') {t\<leftarrow>lpc_term_parser; xml_return (LPPReturnNonnegative t)}) XMLor
    (XMLdo (STR ''magnitudeConstant'') {n\<leftarrow>xml_int (STR ''integer''); xml_return (LPPReturnConstant n)}) XMLor
    (XMLdo (STR ''magnitudeQuotient'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      xml_return (LPPReturnQuotient a b)}) XMLor
    (XMLdo (STR ''magnitudeStrictQuotient'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      xml_return (LPPReturnStrictQuotient a b)}) XMLor
    (XMLdo (STR ''magnitudeHelper'') {i\<leftarrow>xml_nat (STR ''call''); j\<leftarrow>xml_nat (STR ''argument'');
      xml_return (LPPReturnHelper i j)})"

definition lpp_return_row_parser where
  "lpp_return_row_parser = XMLdo (STR ''returnRow'') {
    row_constraints\<leftarrow>xml_many (STR ''constraints'') lpp_return_constraint_parser id;
    formula\<leftarrow>xml_singleton (STR ''formula'') (formula_parser lpp_numeric_tatom_parser) id;
    xml_return (row_constraints,formula)}"

text \<open>The enclosing source backend must bind the parsed complete success
program, the exact projected triples and every return row before using this
component. These parsers introduce no unchecked termination terminal.\<close>
end
