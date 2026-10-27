theory Usable_Rules_HO_Export
 imports "Higher_Order_Filtered_Code.Higher_Order_Filtered_Code" "Usable_Rules_Membership.Usable_Rules_Membership"
begin

text \<open>The indexed worker and the original matching helper are mutually
dependent after code refinement; retain them in one Haskell module.\<close>
code_identifier code_module Code_Abstract_Char \<rightharpoonup> (Haskell) Arith
  | code_module Char_ord \<rightharpoonup> (Haskell) Arith
  | code_module String \<rightharpoonup> (Haskell) Arith
  | code_module Higher_Order_Filtered_Code \<rightharpoonup> (Haskell) Higher_Order_Algebraic_Embedding
  | code_module Usable_Rules_Membership \<rightharpoonup> (Haskell) Usable_Rules_Impl

export_code ho_check_ceta_filtered_delegation_xml ho_check_ceta_semantic_delegation_xml ho_check_ceta_delegation_xml ho_check_delegation_side
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HFOVar HFOFun HPVar HPNumber HPAdd HPMultiply HPApply HPAbstract nat_of_integer in Haskell


end
