theory Relative_ADP_Composition_Parser
  imports Relative_ADP_Composition
begin

text \<open>The envelope contains an ordinary recursive proof and explicit ADP
discharges. The ordinary proof names its child obligations using CPF termination
assumptions; the composition checker closes all of them before certification.
The rule lists in a discharge are part of the checked obligation, not annotations.
Existing ordinary and root-ADP certificate parsers remain unchanged.\<close>

definition relative_adp_discharge_parser :: "relative_adp_discharge xmlt" where
  "relative_adp_discharge_parser = XMLdo (STR ''relativeAdpDischarge'') {
    R \<leftarrow> xml_singleton (STR ''strictRules'')
      (rules symbol_parser Mapping.empty Mapping.empty) id;
    B \<leftarrow> xml_singleton (STR ''weakRules'')
      (rules symbol_parser Mapping.empty Mapping.empty) id;
    p \<leftarrow> xml2relative_adp_root;
    xml_return (R,B,p)
  }"

definition relative_adp_composition_parser where
  "relative_adp_composition_parser termIndexMap ruleMap =
    xml_singleton (STR ''proof'')
      (XMLdo (STR ''relativeAdpComposition'') {
        prf \<leftarrow> proof_parser termIndexMap ruleMap;
        discharges \<leftarrow> xml_many (STR ''discharges'') relative_adp_discharge_parser id;
        xml_return (prf, discharges)
      }) id"

definition composition_aware_proof_parser where
  "composition_aware_proof_parser termIndexMap ruleMap x =
    (case fst x of XML name attrs (XML child child_attrs children # rest) \<Rightarrow>
      if child = String.explode (STR ''relativeAdpComposition'') then
        xml_change (relative_adp_composition_parser termIndexMap ruleMap)
          (xml_return \<circ> Inr) x
      else xml_change (integrated_proof_parser termIndexMap ruleMap)
        (xml_return \<circ> Inl) x
    | _ \<Rightarrow> xml_change (integrated_proof_parser termIndexMap ruleMap)
        (xml_return \<circ> Inl) x)"

definition composed_certification_problem_parser where
  "composed_certification_problem_parser =
    XMLdo (STR ''certificationProblem'') {
      version \<leftarrow> xml_text (STR ''cpfVersion'');
      (termIndexMap,ruleMap) \<leftarrow> lookupTables symbol_parser;
      inp \<leftarrow>? input_parser termIndexMap ruleMap;
      prop \<leftarrow>? property_parser;
      ans \<leftarrow>? answer_parser termIndexMap ruleMap;
      prf \<leftarrow> composition_aware_proof_parser termIndexMap ruleMap;
      meta_info \<leftarrow>? xml_any;
      xml_return (inp,prop,ans,prf)
    }"

definition parse_combined_composed_cert_problem where
  "parse_combined_composed_cert_problem inp1 prop1 ans1 text = do {
    (inp2,prop2,ans2,prf) \<leftarrow>
      parse_from_string composed_certification_problem_parser text;
    inp \<leftarrow> parse_merge (STR ''input'') parse_input inp1 inp2;
    prop \<leftarrow> parse_merge (STR ''property'') parse_property prop1 prop2;
    ans \<leftarrow> parse_merge (STR ''answer'') parse_answer ans1 ans2;
    return (inp,prop,ans,prf)
  }"

definition certify_composed_cert_problem where
  "certify_composed_cert_problem assumptions inp prop ans certificate =
    (case certificate of
       Inl ordinary \<Rightarrow> certify_integrated_cert_problem assumptions inp prop ans ordinary
     | Inr (prf,discharges) \<Rightarrow> certify_relative_adp_composition inp prop ans prf discharges)"

lemma certify_composed_cert_problem_sound:
  assumes "certify_composed_cert_problem False inp prop ans certificate = Certified"
  shows "desired_property inp prop ans"
  using assms unfolding certify_composed_cert_problem_def
  by (cases certificate; auto intro: certify_integrated_cert_problem_sound
      certify_relative_adp_composition_sound split: prod.splits)

definition certify_proof_composed where
  "certify_proof_composed assumptions inp_o prop_o ans_o text =
    bind2' (parse_combined_composed_cert_problem inp_o prop_o ans_o text) Unsupported
      (\<lambda>(inp,prop,ans,prf).
        certify_composed_cert_problem assumptions inp prop ans prf)"

end
