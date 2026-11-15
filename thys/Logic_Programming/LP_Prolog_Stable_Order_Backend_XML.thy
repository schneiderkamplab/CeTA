theory LP_Prolog_Stable_Order_Backend_XML
  imports LP_Prolog_Stable_Order_Backends LP_Prolog_Success_Order_XML LP_Prolog_Stable_Field_Backend_XML
begin

definition lpp_order_use_parser where
  "lpp_order_use_parser = XMLdo (STR ''use'') {
    i\<leftarrow>xml_nat (STR ''call''); r\<leftarrow>xml_nat (STR ''rule''); xml_return (i,r)}"

definition lpp_order_row_parser where
  "lpp_order_row_parser =
    (xml_many (STR ''row'') lpp_order_use_parser (\<lambda>uses. (None,uses))) XMLor
    (XMLdo (STR ''positionedRow'') {
      position\<leftarrow>xml_nat (STR ''observationPosition'');
      uses\<leftarrow>xml_many (STR ''uses'') lpp_order_use_parser id;
      xml_return (Some position,uses)})"

definition lpp_order_backend_parser where
  "lpp_order_backend_parser =
    (xml_change lpp_field_backend_parser (\<lambda>child. xml_return (Inl child))) XMLor
    (XMLdo (STR ''orderBackend'') {
      contract\<leftarrow>lpp_order_contract_parser;
      uses\<leftarrow>xml_many (STR ''orderUses'') lpp_order_row_parser id;
      child\<leftarrow>lpp_field_backend_parser;
      xml_return (Inr (contract,uses,child))})"

fun lpp_decode_order_backend where
  "lpp_decode_order_backend transfer source_rows (Inl child) =
    map_option (\<lambda>backend. (None,backend)) (lpp_decode_field_backend transfer source_rows child)"
| "lpp_decode_order_backend transfer source_rows (Inr ((summaries,P,receipts),uses,child)) =
    (if P=fst (snd transfer) \<and> distinct (map fst summaries) \<and> length uses=length source_rows then
      (let table=lpp_order_summary_lookup summaries in
        map_option (\<lambda>backend. (Some (table,receipts,uses),backend))
          (lpp_decode_field_backend transfer (lpp_enrich_order_rows table uses source_rows) child))
     else None)"

definition lpp_decode_order_backends where
  "lpp_decode_order_backends transfer OD ranks raw = map (\<lambda>n.
    lpp_decode_order_backend transfer (lpp_stable_rank_row_list (lpp_mixed_rank_lookup ranks) n OD) (raw!n))
      [0..<length raw]"

end
