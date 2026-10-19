theory Higher_Order_CeTA_Semantic_Code
  imports "Higher_Order_CeTA_Semantic.Higher_Order_CeTA_Semantic_Check"
begin

text \<open>The HO import also loads Code_Abstract_Char. Restore CeTA's
module grouping after that import to avoid a Str/Arith import cycle.\<close>
code_identifier code_module Code_Abstract_Char \<rightharpoonup> (Haskell) Arith
  | code_module String \<rightharpoonup> (Haskell) Arith
  | code_module Higher_Order_CeTA_Semantic_Code \<rightharpoonup> (Haskell) Higher_Order_Algebraic_Embedding

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

declare ho_polynomial_normalize.simps[code del]
lemma ho_polynomial_normalize_target_code [code]:
  "ho_polynomial_normalize n p = (if n=0 then p else
    case p of
      HPVar k \<Rightarrow> HPVar k
    | HPNumber b k \<Rightarrow> HPNumber b k
    | HPAdd b q r \<Rightarrow> ho_polynomial_contract
        (HPAdd b (ho_polynomial_normalize (n-1) q) (ho_polynomial_normalize (n-1) r))
    | HPMultiply b q r \<Rightarrow> ho_polynomial_contract
        (HPMultiply b (ho_polynomial_normalize (n-1) q) (ho_polynomial_normalize (n-1) r))
    | HPApply A B f x \<Rightarrow>
        (let q = HPApply A B (ho_polynomial_normalize (n-1) f) (ho_polynomial_normalize (n-1) x);
             r = ho_polynomial_contract q
         in if r=q then q else ho_polynomial_normalize (n-1) r)
    | HPAbstract A B t \<Rightarrow> HPAbstract A B (ho_polynomial_normalize (n-1) t))"
  by (cases n; cases p) simp_all

export_code ho_check_ceta_semantic_delegation_xml ho_check_ceta_delegation_xml ho_check_delegation_side
  HBase HArrow HBound HFree HConst HApp HAbs PBound PConst PApp PAbs PMeta
  HFOVar HFOFun HPVar HPNumber HPAdd HPMultiply HPApply HPAbstract nat_of_integer in Haskell

end
