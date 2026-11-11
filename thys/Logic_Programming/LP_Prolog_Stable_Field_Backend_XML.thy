theory LP_Prolog_Stable_Field_Backend_XML
 imports LP_Prolog_Stable_Field_Backends LP_Prolog_Stable_Mixed_XML
begin

definition lpp_field_backend_parser where
  "lpp_field_backend_parser =
    (xml_change lpp_mixed_backend_parser (\<lambda>child. xml_return (None,child))) XMLor
    (XMLdo (STR ''fieldBackend'') {
      fuel\<leftarrow>xml_nat (STR ''endpointNormalizationFuel'');
      field_plan\<leftarrow>xml_many (STR ''fields'') (XMLdo (STR ''entry'') {
        p\<leftarrow>xml_text (STR ''predicate'');
        paths\<leftarrow>xml_many (STR ''paths'') (XMLdo (STR ''path'') {
          i\<leftarrow>xml_nat (STR ''argument'');
          steps\<leftarrow>xml_many (STR ''steps'') (xml_nat (STR ''position'')) id;
          xml_return (i,steps)}) id;
        xml_return (p,paths)}) id;
      child\<leftarrow>lpp_mixed_backend_parser;
      xml_return (Some (fuel,field_plan),child)})"

fun lpp_decode_field_backend where
  "lpp_decode_field_backend transfer source_rows (None,child) =
    map_option (\<lambda>backend. (None,backend)) (lpp_decode_mixed_backend transfer source_rows child)"
| "lpp_decode_field_backend transfer source_rows (Some (fuel,field_plan),child) =
    (if distinct (map fst field_plan) \<and>
      list_all (\<lambda>((h,ps,b,gs),os). fst h\<in>set (map fst field_plan) \<and>
        fst b\<in>set (map fst field_plan)) source_rows then
      (let meta=Some (fuel,lpp_numeric_coordinate_lookup field_plan) in
        map_option (\<lambda>backend. (meta,backend))
          (lpp_decode_mixed_backend transfer (lpp_field_backend_rows meta source_rows) child))
     else None)"

definition lpp_decode_field_backends where
  "lpp_decode_field_backends transfer OD ranks raw = map (\<lambda>n.
    lpp_decode_field_backend transfer (lpp_stable_rank_row_list (lpp_mixed_rank_lookup ranks) n OD) (raw!n))
      [0..<length raw]"

end
