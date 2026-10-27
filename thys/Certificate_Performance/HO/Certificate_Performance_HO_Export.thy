theory Certificate_Performance_HO_Export
 imports "Usable_Rules_HO_Export.Usable_Rules_HO_Export"
   "Certificate_Performance.Certificate_Performance"
begin
code_identifier code_module Code_Abstract_Char \<rightharpoonup> (Haskell) Arith
  | code_module String \<rightharpoonup> (Haskell) Arith
  | code_module Char_ord \<rightharpoonup> (Haskell) Arith
  | code_module Higher_Order_Filtered_Code \<rightharpoonup> (Haskell) Higher_Order_Algebraic_Embedding
  | code_module Usable_Rules_Membership \<rightharpoonup> (Haskell) Usable_Rules_Impl
  | code_module XML_Performance \<rightharpoonup> (Haskell) Xmlt
  | code_module Rule_Bucket_Performance \<rightharpoonup> (Haskell) Multimap

export_code ho_check_ceta_filtered_delegation_xml ho_check_ceta_semantic_delegation_xml ho_check_ceta_delegation_xml ho_check_delegation_side
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HFOVar HFOFun HPVar HPNumber HPAdd HPMultiply HPApply HPAbstract nat_of_integer in Haskell
end
