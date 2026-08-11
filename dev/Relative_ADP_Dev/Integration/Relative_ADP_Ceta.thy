theory Relative_ADP_Ceta
  imports
    Relative_ADP_Checker_Dev.Relative_ADP_Checker_Adapter
    Proof_Checker.Ceta_Verifier
begin

partial_function (sum_bot) xml2relative_adp_termination_proof ::
  "lsymbol relative_adp_termination_proof xmlt" where
  [code]: "xml2relative_adp_termination_proof x =
    xml_singleton (STR ''relativeAdpTerminationProof'')
      (XMLdo (STR ''relativeAdpEmpty'') {
        xml_return Relative_ADP_Empty
      } XMLor XMLdo (STR ''relativeAdpErasureReductionPair'') {
        redp \<leftarrow> redtriple symbol_parser Sharp False;
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
      } XMLor XMLdo (STR ''relativeAdpDependencyGraph'') {
        proofs \<leftarrow>* xml2relative_adp_termination_proof;
        xml_return (Relative_ADP_Dependency_Graph proofs)
      }) id x"

definition relative_adp_certification_problem_parser ::
  "((lsymbol,string) input option \<times>
    (lsymbol,string) property option \<times>
    (lsymbol,string) answer option \<times>
    lsymbol relative_adp_termination_proof) xmlt" where
  "relative_adp_certification_problem_parser =
    XMLdo (STR ''certificationProblem'') {
      version \<leftarrow> xml_text (STR ''cpfVersion'');
      (term_index_map, rule_map) \<leftarrow> lookupTables symbol_parser;
      inp \<leftarrow>? input_parser term_index_map rule_map;
      prop \<leftarrow>? property_parser;
      ans \<leftarrow>? answer_parser term_index_map rule_map;
      proof \<leftarrow> XMLdo (STR ''proof'') {
        p \<leftarrow> xml2relative_adp_termination_proof;
        xml_return p
      };
      meta_info \<leftarrow>? xml_any;
      xml_return (inp, prop, ans, proof)
    }"

definition parse_relative_adp_cert_problem where
  "parse_relative_adp_cert_problem =
    parse_from_string relative_adp_certification_problem_parser"

definition parse_combined_relative_adp_cert_problem where
  "parse_combined_relative_adp_cert_problem inp1 prop1 answ1 prfs = do {
    (inp2, prop2, answ2, proof) \<leftarrow>
      parse_relative_adp_cert_problem prfs;
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

definition certify_proof_integrated ::
  "bool \<Rightarrow> string option \<Rightarrow> string option \<Rightarrow>
   string option \<Rightarrow> string \<Rightarrow> cert_result" where
  "certify_proof_integrated assumptions inp_o prop_o answ_o proof_string =
    bind2' (parse_combined_relative_adp_cert_problem
      inp_o prop_o answ_o proof_string)
      (\<lambda>_. certify_proof assumptions inp_o prop_o answ_o proof_string)
      (\<lambda>(inp, prop, answ, proof).
        certify_relative_adp_cert_problem inp prop answ proof)"

end
