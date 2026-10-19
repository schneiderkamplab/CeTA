theory Higher_Order_CeTA_Code
  imports "Higher_Order_CeTA_Check.Higher_Order_CeTA_Check"
begin

text \<open>The HO import also loads Code_Abstract_Char. Restore CeTA's
module grouping after that import to avoid a Str/Arith import cycle.\<close>
code_identifier code_module Code_Abstract_Char \<rightharpoonup> (Haskell) Arith
  | code_module String \<rightharpoonup> (Haskell) Arith
  | code_module Higher_Order_CeTA_Code \<rightharpoonup> (Haskell) Higher_Order_Algebraic_Embedding

derive (eq) ceq ho_type ho_term ho_pattern ho_fo_tree
derive compare ho_type ho_term ho_pattern ho_fo_tree
derive (compare) ccompare ho_type ho_term ho_pattern ho_fo_tree
derive (rbt) set_impl ho_type ho_term ho_pattern ho_fo_tree
derive (no) cenum ho_type ho_term ho_pattern ho_fo_tree

text \<open>The production checker represents naturals by target integers.
This uniform equation avoids mixed zero/type-constructor patterns.\<close>
declare ho_drop_type.simps[code del]
lemma ho_drop_type_target_code [code]:
  "ho_drop_type n A = (if n=0 then A else
     case A of HBase b \<Rightarrow> HBase b | HArrow T C \<Rightarrow> ho_drop_type (n-1) C)"
  by (cases n; cases A) simp_all

lemma ho_finitely_matching_rules_code [code]:
  "ho_finitely_matching_rules R = list_all (\<lambda>(G,l,r).
    ho_zero_arity_pattern l \<and> ho_zero_arity_pattern r \<and>
    ho_free_support (ho_erase_pattern r) \<subseteq> ho_free_support (ho_erase_pattern l)) R"
  by (auto simp: ho_finitely_matching_rules_def list_all_iff)

export_code ho_check_ceta_delegation_xml ho_check_delegation_side
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HFOVar HFOFun nat_of_integer in Haskell

end
