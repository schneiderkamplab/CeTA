theory LP_Prolog_Observer_Plan_XML
 imports LP_Prolog_Observer_Plan
begin

definition lpp_observer_row_role_parser where
 "lpp_observer_row_role_parser =
 (XMLdo (STR ''local'') {xml_return LPPORLocal}) XMLor
 (XMLdo (STR ''acquired'') {i\<leftarrow>nat; xml_return (LPPORAcquired i)}) XMLor
 (XMLdo (STR ''internal'') {i\<leftarrow>nat; xml_return (LPPORInternal i)}) XMLor
 (XMLdo (STR ''returned'') {i\<leftarrow>nat; xml_return (LPPORReturned i)}) XMLor
 (XMLdo (STR ''empty'') {xml_return LPPOREmpty}) XMLor
 (XMLdo (STR ''boundary'') {xml_return LPPORBoundary})"

definition lpp_observer_plan_parser where
 "lpp_observer_plan_parser = XMLdo (STR ''observerPlan'') {
  version\<leftarrow>xml_nat (STR ''version'');
  plan_rows\<leftarrow>xml_many (STR ''rows'') (XMLdo (STR ''row'') {
   i\<leftarrow>xml_nat (STR ''index''); role\<leftarrow>lpp_observer_row_role_parser;
   xml_return (i,role)}) id;
  frontier_indices\<leftarrow>xml_many (STR ''frontier'') (xml_nat (STR ''index'')) id;
  xml_return (version,plan_rows,frontier_indices)}"

definition lpp_decode_observer_plan where
 "lpp_decode_observer_plan xml = parse_xml_string lpp_observer_plan_parser xml"

text \<open>Decoding retains all pending references. Neither parsing nor successful
local assembly discharges the pending contracts or residual termination.\<close>
end
