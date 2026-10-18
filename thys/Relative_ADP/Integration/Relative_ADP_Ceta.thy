theory Relative_ADP_Ceta
  imports
    Relative_ADP_Integration_Base.Relative_ADP_Integration_Base
begin

partial_function (sum_bot) relative_adp_com_symbol_parser ::
  "lsymbol adp_com_symbol xmlt" where
  [code]: "relative_adp_com_symbol_parser x = (
    xml_change (xml_text (STR ''name''))
      (xml_return \<circ> ADP_Symbol \<circ> adp_symbol.Plain \<circ> UnLab)
    XMLor xml_change
      (xml_singleton (STR ''sharp'') symbol_parser id)
      (xml_return \<circ> ADP_Symbol \<circ> adp_symbol.Sharp)
    XMLor XMLdo (STR ''adpCom0'') {
      xml_return Com0
    }
    XMLor XMLdo (STR ''adpCom2'') {
      xml_return Com2
    }
  ) x"

partial_function (sum_bot) relative_adp_drp1_symbol_parser ::
  "(lsymbol adp_symbol, nat list) lab xmlt" where
  [code]: "relative_adp_drp1_symbol_parser x = (
    xml_change (xml_text (STR ''name''))
      (xml_return \<circ> UnLab \<circ> Plain \<circ> UnLab)
    XMLor xml_change
      (xml_singleton (STR ''sharp'') symbol_parser id)
      (xml_return \<circ> UnLab \<circ> adp_symbol.Sharp)
    XMLor xml_pair (STR ''labeledSymbol'')
      relative_adp_drp1_symbol_parser
      (xml_many (STR ''numberLabel'') (xml_nat (STR ''number'')) Inl
       XMLor xml_many (STR ''symbolLabel'')
         relative_adp_drp1_symbol_parser Inr)
      (\<lambda>f l. case l of
        Inl ls \<Rightarrow> Lab f ls
      | Inr ls \<Rightarrow> FunLab f ls)
  ) x"

partial_function (sum_bot) xml2relative_adp_termination_proof ::
  "lsymbol relative_adp_termination_proof xmlt" where
  [code]: "xml2relative_adp_termination_proof x =
    xml_singleton (STR ''relativeAdpTerminationProof'')
      (XMLdo (STR ''relativeAdpEmpty'') {
        xml_return Relative_ADP_Empty
      } XMLor XMLdo (STR ''relativeAdpErasureReductionPair'') {
        redp \<leftarrow> redtriple symbol_parser lab.Sharp False;
        main_indices \<leftarrow> XMLdo (STR ''mainIndices'') {
          indices \<leftarrow>* xml_nat (STR ''index'');
          xml_return indices
        };
        base_indices \<leftarrow> XMLdo (STR ''baseIndices'') {
          indices \<leftarrow>* xml_nat (STR ''index'');
          xml_return indices
        };
        continuation \<leftarrow> xml2relative_adp_termination_proof;
        xml_return (Relative_ADP_Erasure_Redpair redp
          main_indices base_indices continuation)
      } XMLor XMLdo (STR ''relativeAdpComReductionPair'') {
        redp \<leftarrow> redtriple relative_adp_com_symbol_parser id False;
        main_indices \<leftarrow> XMLdo (STR ''mainIndices'') {
          indices \<leftarrow>* xml_nat (STR ''index'');
          xml_return indices
        };
        base_indices \<leftarrow> XMLdo (STR ''baseIndices'') {
          indices \<leftarrow>* xml_nat (STR ''index'');
          xml_return indices
        };
        continuation \<leftarrow> xml2relative_adp_termination_proof;
        xml_return (Relative_ADP_Com_Redpair redp
          main_indices base_indices continuation)
      } XMLor XMLdo (STR ''relativeAdpDependencyGraph'') {
        proofs \<leftarrow>* xml2relative_adp_termination_proof;
        xml_return (Relative_ADP_Dependency_Graph False proofs)
      } XMLor XMLdo (STR ''relativeAdpRootDependencyGraph'') {
        proofs \<leftarrow>* xml2relative_adp_termination_proof;
        xml_return (Relative_ADP_Dependency_Graph True proofs)
      } XMLor XMLdo (STR ''relativeAdpDerelatification'') {
        ordinary_proof \<leftarrow> xml2dp_termination_proof
          relative_adp_drp1_symbol_parser Mapping.empty Mapping.empty;
        xml_return (Relative_ADP_Derelatification ordinary_proof)
      }) id x"

definition integrated_proof_parser where
  "integrated_proof_parser termIndexMap ruleMap x =
    (let ordinary = xml_change (proof_parser termIndexMap ruleMap)
        (\<lambda>p. xml_return (Inl p)) in
     case fst x of XML name attrs (XML child child_attrs children # rest) \<Rightarrow>
       if child = String.explode (STR ''relativeAdpTerminationProof'') then
         xml_change (xml_singleton (STR ''proof'')
           xml2relative_adp_termination_proof id)
           (\<lambda>p. xml_return (Inr p)) x
       else ordinary x
     | _ \<Rightarrow> ordinary x)"

definition integrated_certification_problem_parser ::
  "((lsymbol,string) input option \<times>
    (lsymbol,string) property option \<times>
    (lsymbol,string) answer option \<times>
    ((string,label_type,string) proof + lsymbol relative_adp_termination_proof)) xmlt" where
  "integrated_certification_problem_parser =
    XMLdo (STR ''certificationProblem'') {
      version \<leftarrow> xml_text (STR ''cpfVersion'');
      (term_index_map, rule_map) \<leftarrow> lookupTables symbol_parser;
      inp \<leftarrow>? input_parser term_index_map rule_map;
      prop \<leftarrow>? property_parser;
      ans \<leftarrow>? answer_parser term_index_map rule_map;
      proof \<leftarrow> integrated_proof_parser term_index_map rule_map;
      meta_info \<leftarrow>? xml_any;
      xml_return (inp, prop, ans, proof)
    }"

definition parse_integrated_cert_problem where
  "parse_integrated_cert_problem =
    parse_from_string integrated_certification_problem_parser"

definition parse_combined_integrated_cert_problem where
  "parse_combined_integrated_cert_problem inp1 prop1 answ1 prfs = do {
    (inp2, prop2, answ2, proof) \<leftarrow>
      parse_integrated_cert_problem prfs;
    inp \<leftarrow> parse_merge (STR ''input'') parse_input inp1 inp2;
    prop \<leftarrow> parse_merge (STR ''property'') parse_property prop1 prop2;
    answ \<leftarrow> parse_merge (STR ''answer'') parse_answer answ1 answ2;
    return (inp, prop, answ, proof)
  }"

definition check_relative_adp_cert_problem ::
  "(lsymbol,string) input \<Rightarrow> (lsymbol,string) property \<Rightarrow>
   (lsymbol,string) answer \<Rightarrow>
   lsymbol relative_adp_termination_proof \<Rightarrow> showsl check" where
  "check_relative_adp_cert_problem inp_value property_value answer_value certificate =
    (case (inp_value, property_value, answer_value) of
      (Inn_TRS_input No_Strategy R B, Termination, Decision True) \<Rightarrow>
        check_relative_adp_from_trs R B certificate
    | _ \<Rightarrow> Inl (showsl_lit
        (STR ''relative ADP proofs require a standard relative TRS YES problem'')))"

definition certify_relative_adp_cert_problem ::
  "(lsymbol,string) input \<Rightarrow> (lsymbol,string) property \<Rightarrow>
   (lsymbol,string) answer \<Rightarrow>
   lsymbol relative_adp_termination_proof \<Rightarrow> cert_result" where
  "certify_relative_adp_cert_problem inp_value property_value answer_value certificate =
    (case check_relative_adp_cert_problem inp_value property_value answer_value certificate of
      Inl err \<Rightarrow> Error (err (STR ''''))
    | Inr _ \<Rightarrow> Certified)"

lemma check_relative_adp_cert_problem_sound:
  assumes checked:
    "isOK (check_relative_adp_cert_problem inp_value property_value answer_value certificate)"
  shows "desired_property inp_value property_value answer_value"
proof -
  from checked obtain R B where inp_def:
      "inp_value = Inn_TRS_input No_Strategy R B"
    and prop_def: "property_value = Termination"
    and ans_def: "answer_value = Decision True"
    by (cases inp_value;
        auto simp: check_relative_adp_cert_problem_def
        split: strategy.splits property.splits answer.splits bool.splits)
  from checked have checked_adp:
      "isOK (check_relative_adp_from_trs R B certificate)"
    unfolding inp_def prop_def ans_def check_relative_adp_cert_problem_def
    by simp
  from checked_adp have termination_result:
      "SN_rel (Trs.rstep (set R)) (Trs.rstep (set B))"
    by (rule check_relative_adp_from_trs_sound)
  show ?thesis
    unfolding inp_def prop_def ans_def desired_property_def
    using termination_result by simp
qed

lemma certify_relative_adp_cert_problem_sound:
  assumes certified:
    "certify_relative_adp_cert_problem inp_value property_value answer_value certificate = Certified"
  shows "desired_property inp_value property_value answer_value"
  using certified
  unfolding certify_relative_adp_cert_problem_def
  by (cases "check_relative_adp_cert_problem inp_value property_value answer_value certificate";
      auto intro: check_relative_adp_cert_problem_sound)

text \<open>Parse the certificate once and dispatch on its parsed proof type.
The structural choice inspects only the proof node's first child tag; each
selected parser still validates the complete proof. No fallback retains the
original certificate string throughout checking.\<close>

definition certify_integrated_cert_problem where
  "certify_integrated_cert_problem assumptions inp prop ans certificate =
    (case certificate of
       Inl ordinary \<Rightarrow> certify_cert_problem_rfc_absolute
         tp_impl dpp_impl ac_tp_impl ac_dpp_impl assumptions inp prop ans ordinary
     | Inr adp \<Rightarrow> certify_relative_adp_cert_problem inp prop ans adp)"

lemma certify_integrated_cert_problem_sound:
  assumes "certify_integrated_cert_problem False inp prop ans certificate = Certified"
  shows "desired_property inp prop ans"
  using assms unfolding certify_integrated_cert_problem_def
  by (cases certificate; auto intro:
      certify_cert_problem_rfc_absolute_sound[OF tp_rbt_impl dpp_rbt_impl
        ac_tp_list_impl ac_dpp_rbt_impl]
      certify_relative_adp_cert_problem_sound)

definition certify_proof_integrated ::
  "bool \<Rightarrow> string option \<Rightarrow> string option \<Rightarrow>
   string option \<Rightarrow> string \<Rightarrow> cert_result" where
  "certify_proof_integrated assumptions inp_o prop_o answ_o proof_string =
    bind2' (parse_combined_integrated_cert_problem
      inp_o prop_o answ_o proof_string) Unsupported
      (\<lambda>(inp, prop, answ, proof).
        certify_integrated_cert_problem assumptions inp prop answ proof)"

end
