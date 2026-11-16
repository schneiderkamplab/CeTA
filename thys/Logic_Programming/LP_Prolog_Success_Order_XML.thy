theory LP_Prolog_Success_Order_XML
  imports LP_Prolog_Success_Order_Program LP_Prolog_Success_Transfer_XML
begin

partial_function (sum_bot) lpp_order_bound_parser :: "lpp_order_bound xmlt" where
[code]: "lpp_order_bound_parser x = (
  (XMLdo (STR ''knownOrder'') {i\<leftarrow>xml_nat (STR ''position''); xml_return (LPPOrderKnown i)}) XMLor
  (XMLdo (STR ''shiftOrder'') {p\<leftarrow>lpp_order_bound_parser; k\<leftarrow>xml_int (STR ''integer'');
    xml_return (LPPOrderShift p k)}) XMLor
  (XMLdo (STR ''subtractOrder'') {p\<leftarrow>lpp_order_bound_parser; k\<leftarrow>xml_int (STR ''integer'');
    xml_return (LPPOrderSubtract p k)})) x"

definition lpp_order_base_parser where
  "lpp_order_base_parser =
    (XMLdo (STR ''argumentBase'') {i\<leftarrow>xml_nat (STR ''position''); xml_return (LPPOrderArgument i)}) XMLor
    (XMLdo (STR ''constantBase'') {k\<leftarrow>xml_int (STR ''integer''); xml_return (LPPOrderConstant k)})"

definition lpp_order_fact_parser where
  "lpp_order_fact_parser =
    (XMLdo (STR ''comparedEvaluationOrder'') {i\<leftarrow>xml_nat (STR ''guard''); j\<leftarrow>xml_nat (STR ''comparison'');
      p\<leftarrow>lpp_order_bound_parser; v\<leftarrow>xml_text (STR ''var''); xml_return (LPPOrderComparedEvaluation i j p v)}) XMLor
    (XMLdo (STR ''evaluationOrder'') {i\<leftarrow>xml_nat (STR ''guard''); p\<leftarrow>lpp_order_bound_parser;
      v\<leftarrow>xml_text (STR ''var''); xml_return (LPPOrderEvaluation i p v)}) XMLor
    (XMLdo (STR ''helperOrder'') {i\<leftarrow>xml_nat (STR ''call''); r\<leftarrow>xml_nat (STR ''rule'');
      p\<leftarrow>lpp_order_bound_parser; v\<leftarrow>xml_text (STR ''var''); xml_return (LPPOrderHelper i r p v)})"

definition lpp_order_contract_parser where
  "lpp_order_contract_parser = XMLdo (STR ''prologSuccessOrderContract'') {
    summaries\<leftarrow>xml_many (STR ''summaries'') (XMLdo (STR ''summary'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity'');
      rules\<leftarrow>xml_many (STR ''rules'') (XMLdo (STR ''rule'') {
        direction\<leftarrow>xml_nat (STR ''increasing''); selector\<leftarrow>lpp_order_base_parser;
        j\<leftarrow>xml_nat (STR ''output''); xml_return (direction=1,selector,j)}) id;
      xml_return ((p,n),rules)}) id;
    P\<leftarrow>xml_many (STR ''successProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpp_success_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpp_success_atom_parser id;
      gs\<leftarrow>xml_many (STR ''guards'') lpp_success_guard_parser id;
      xml_return (h,bs,gs)}) id;
    receipts\<leftarrow>xml_many (STR ''proofs'') (XMLdo (STR ''clause'') {
      outputs\<leftarrow>xml_many (STR ''outputs'') (XMLdo (STR ''output'') {
        fs\<leftarrow>xml_many (STR ''facts'') lpp_order_fact_parser id;
        k\<leftarrow>xml_nat (STR ''result''); xml_return (fs,k)}) id;
      xml_return outputs}) id;
    xml_return (summaries,P,receipts)}"

definition lpp_order_summary_lookup where
  "lpp_order_summary_lookup summaries signature = (case map_of summaries signature of None \<Rightarrow> [] | Some rs \<Rightarrow> rs)"

end
