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
      insert_at\<leftarrow>xml_nat (STR ''observationPosition'');
      uses\<leftarrow>xml_many (STR ''uses'') lpp_order_use_parser id;
      xml_return (Some insert_at,uses)})"

definition lpp_legacy_order_backend_parser where
  "lpp_legacy_order_backend_parser =
    (xml_change lpp_field_backend_parser (\<lambda>child. xml_return (Inl child))) XMLor
    (XMLdo (STR ''orderBackend'') {
      contract\<leftarrow>lpp_order_contract_parser;
      uses\<leftarrow>xml_many (STR ''orderUses'') lpp_order_row_parser id;
      child\<leftarrow>lpp_field_backend_parser;
      xml_return (Inr (contract,uses,child))})"

fun lpp_decode_legacy_order_backend where
  "lpp_decode_legacy_order_backend transfer source_rows (Inl child) =
    map_option (\<lambda>backend. (None,backend)) (lpp_decode_field_backend transfer source_rows child)"
| "lpp_decode_legacy_order_backend transfer source_rows (Inr ((summaries,P,receipts),uses,child)) =
    (if P=fst (snd transfer) \<and> distinct (map fst summaries) \<and> length uses=length source_rows then
      (let table=lpp_order_summary_lookup summaries in
        map_option (\<lambda>backend. (Some (table,receipts,uses),backend))
          (lpp_decode_field_backend transfer (lpp_enrich_order_rows table uses source_rows) child))
     else None)"


definition lpp_value_summary_parser where
 "lpp_value_summary_parser = XMLdo (STR ''summary'') {
   p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity'');
   positions\<leftarrow>xml_many (STR ''positions'') (xml_nat (STR ''position'')) id;
   xml_return ((p,n),positions)}"

definition lpp_value_order_row_parser where
 "lpp_value_order_row_parser = XMLdo (STR ''row'') {
   insert_at\<leftarrow>xml_nat (STR ''observationPosition'');
   return_terms\<leftarrow>xml_many (STR ''terms'') lpc_term_parser id;
   uses\<leftarrow>xml_many (STR ''uses'') lpp_order_use_parser id;
   xml_return (Some insert_at,return_terms,uses)}"

definition lpp_order_backend_parser where
 "lpp_order_backend_parser =
   (xml_change lpp_legacy_order_backend_parser (\<lambda>child. xml_return (Inl child))) XMLor
   (XMLdo (STR ''valueOrderBackend'') {
     value_table\<leftarrow>xml_many (STR ''valueSummaries'') lpp_value_summary_parser id;
     contract\<leftarrow>lpp_order_contract_parser;
     uses\<leftarrow>xml_many (STR ''valueOrderUses'') lpp_value_order_row_parser id;
     child\<leftarrow>lpp_field_backend_parser;
     xml_return (Inr (value_table,contract,uses,child))})"

definition lpp_value_summary_lookup where
 "lpp_value_summary_lookup table signature = (case map_of table signature of None \<Rightarrow> [] | Some positions \<Rightarrow> positions)"

fun lpp_decode_order_backend where
 "lpp_decode_order_backend transfer source_rows (Inl child) =
   map_option Inl (lpp_decode_legacy_order_backend transfer source_rows child)"
| "lpp_decode_order_backend transfer source_rows (Inr (value_table,(summaries,P,receipts),uses,child)) =
   (if P=fst (snd transfer) \<and> distinct (map fst value_table) \<and> distinct (map fst summaries) \<and>
      length uses=length source_rows then
     (let value_table=lpp_value_summary_lookup value_table; table=lpp_order_summary_lookup summaries in
       map_option (\<lambda>backend. Inr (value_table,table,receipts,uses,backend))
         (lpp_decode_field_backend transfer (lpp_enrich_value_order_rows value_table table uses source_rows) child))
    else None)"

definition lpp_decode_order_backends where
  "lpp_decode_order_backends transfer OD ranks raw = map (\<lambda>n.
    lpp_decode_order_backend transfer (lpp_stable_rank_row_list (lpp_mixed_rank_lookup ranks) n OD) (raw!n))
      [0..<length raw]"

end
