(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Improved_CSDP_Checker
  imports
    CSR_Improved_CSDP_Proofs
    "Proof_Checker.Ceta"
begin

datatype ('f, 'l, 'v) extended_csr_termination_proof =
    Existing_CSR_Proof "('f, 'l, 'v) csr_termination_proof"
  | Conservative_CSR_Dependency_Pairs
      "('f, 'l) lab"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) csr_dp_termination_proof"

context
  fixes xml2name ::
    "('f::{showl,compare_order}, 'l::{showl,compare_order}) lab xmlt"
    and termIndexMap :: "('f,'l) lab termIndexMap"
    and ruleMap :: "('f,'l) lab ruleIndexMap"
begin

definition xml2conservative_csr_termination_proof ::
  "('f, 'l, string) extended_csr_termination_proof xmlt"
where
  "xml2conservative_csr_termination_proof =
    xml_singleton (STR ''nativeConservativeCsrTerminationProof'')
      (XMLdo (STR ''csrConservativeDependencyPairs'') {
        U \<leftarrow> xml_singleton (STR ''unhidingSymbol'') xml2name id;
        P \<leftarrow> xml_singleton (STR ''dps'')
          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap) id;
        S \<leftarrow> xml_singleton (STR ''auxiliaryRules'')
          (CPF_Input_Parser.rules xml2name termIndexMap ruleMap) id;
        prf \<leftarrow> xml2csr_dp_termination_proof xml2name termIndexMap ruleMap;
        xml_return (Conservative_CSR_Dependency_Pairs U P S prf)
      }) id"

definition xml2extended_csr_termination_proof ::
  "('f, 'l, string) extended_csr_termination_proof xmlt"
where
  "xml2extended_csr_termination_proof =
    xml2conservative_csr_termination_proof
    XMLor
    xml_change (xml2csr_termination_proof xml2name termIndexMap ruleMap)
      (\<lambda>p. xml_return (Existing_CSR_Proof p))"

end

fun check_extended_csr_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   bool \<Rightarrow> showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) extended_csr_termination_proof \<Rightarrow> showsl check"
where
  "check_extended_csr_termination_proof I J a i \<mu> R
      (Existing_CSR_Proof prf) =
    check_csr_termination_proof I J a i \<mu> R prf"
| "check_extended_csr_termination_proof I J a i \<mu> R
      (Conservative_CSR_Dependency_Pairs U P S prf) =
    debug i (STR ''conservative CSR dependency pairs'') (do {
      dpp \<leftarrow> conservative_csr_dependency_pairs_tt J U \<mu> R P S
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': invalid conservative CSR-DP transformation\<newline>'') \<circ> s);
      check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below conservative CSR dependency pairs\<newline>'') \<circ> s)
    })"

lemma check_extended_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_extended_csr_termination_proof
      I J a i \<mu> R prf)"
  shows "SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
  using ok
proof (cases "prf")
  case (Existing_CSR_Proof old)
  from ok Existing_CSR_Proof have old_ok:
    "isOK (check_csr_termination_proof I J a i \<mu> R old)"
    by simp
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule check_csr_termination_proof_sound[OF I J old_ok])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
next
  case (Conservative_CSR_Dependency_Pairs U P S dp_prf)
  from ok Conservative_CSR_Dependency_Pairs
  obtain dpp where tt:
      "conservative_csr_dependency_pairs_tt J U \<mu> R P S = Inr dpp"
    and rec:
      "isOK (check_csr_dp_termination_proof
        I J False (add_index i 1) dpp dp_prf)"
    by auto
  have fin: "finite_dpp (dpp_ops.dpp J dpp)"
    by (rule check_csr_dp_termination_proof_sound[OF I J rec])
  show ?thesis
    by (rule conservative_csr_dependency_pairs_tt_finite_imp_SN_sig[
      OF J tt fin])
qed

datatype extended_certification_proof =
    Standard_Certification_Proof "(string,label_type,string) proof"
  | Extended_CSR_Certification_Proof
      "(string,label_type,string) extended_csr_termination_proof"

definition extended_proof_parser ::
  "lsymbol termIndexMap \<Rightarrow> lsymbol ruleIndexMap \<Rightarrow>
    extended_certification_proof xmlt"
where
  "extended_proof_parser termIndexMap ruleMap =
    XMLdo (STR ''proof'') {
      p \<leftarrow>
        xml_change
          (xml2conservative_csr_termination_proof
            symbol_parser termIndexMap ruleMap)
          (\<lambda>p. xml_return (Extended_CSR_Certification_Proof p))
        XMLor
        xml_change
          (proof_content symbol_parser termIndexMap ruleMap)
          (\<lambda>p. xml_return (Standard_Certification_Proof p));
      xml_return p
    }"

definition extended_certification_problem_parser ::
  "((lsymbol,string) input option \<times>
    (lsymbol,string) property option \<times>
    (lsymbol,string) answer option \<times>
    extended_certification_proof) xmlt"
where
  "extended_certification_problem_parser =
    XMLdo (STR ''certificationProblem'') {
      version \<leftarrow> xml_text (STR ''cpfVersion'');
      (termIndexMap,ruleMap) \<leftarrow> lookupTables symbol_parser;
      inp \<leftarrow>? input_parser termIndexMap ruleMap;
      prop \<leftarrow>? property_parser;
      ans \<leftarrow>? answer_parser termIndexMap ruleMap;
      prf \<leftarrow> extended_proof_parser termIndexMap ruleMap;
      meta_info \<leftarrow>? xml_any;
      xml_return (inp,prop,ans,prf)
    }"

definition parse_extended_cert_problem where
  "parse_extended_cert_problem =
    parse_from_string extended_certification_problem_parser"

definition parse_combined_extended_cert_problem where
  "parse_combined_extended_cert_problem inp1 prop1 answ1 prfs = do {
    (inp2,prop2,answ2,prf) \<leftarrow> parse_extended_cert_problem prfs;
    inp \<leftarrow> parse_merge (STR ''input'') parse_input inp1 inp2;
    prop \<leftarrow> parse_merge (STR ''property'') parse_property prop1 prop2;
    answ \<leftarrow> parse_merge (STR ''answer'') parse_answer answ1 answ2;
    return (inp,prop,answ,prf)
  }"

definition certify_extended_cert_problem ::
  "bool \<Rightarrow> (lsymbol,string) input \<Rightarrow>
    (lsymbol,string) property \<Rightarrow> (lsymbol,string) answer \<Rightarrow>
    extended_certification_proof \<Rightarrow> cert_result"
where
  "certify_extended_cert_problem a inp prop answ prf =
    (case prf of
      Standard_Certification_Proof p \<Rightarrow>
        certify_cert_problem tp_impl dpp_impl ac_tp_impl ac_dpp_impl
          a inp prop answ p
    | Extended_CSR_Certification_Proof p \<Rightarrow>
        (case (inp,prop,answ) of
          (FP_TRS_input (Context_Sensitive \<mu>) R,
            Termination, Decision True) \<Rightarrow>
            (case check_extended_csr_termination_proof
                tp_impl dpp_impl a (showsl_lit (STR ''1'')) \<mu> R p of
              Inl e \<Rightarrow> Error (e (STR ''''))
            | Inr _ \<Rightarrow> Certified)
        | _ \<Rightarrow> Error (STR ''CSR proof does not match input and claim'')))"

definition certify_proof_csr ::
  "bool \<Rightarrow> string option \<Rightarrow> string option \<Rightarrow>
    string option \<Rightarrow> string \<Rightarrow> cert_result"
where
  "certify_proof_csr a inp_o prop_o answ_o prfs =
    bind2' (parse_combined_extended_cert_problem
      inp_o prop_o answ_o prfs)
      Unsupported
      (\<lambda>(inp,prop,answ,prf).
        certify_extended_cert_problem a inp prop answ prf)"

end
