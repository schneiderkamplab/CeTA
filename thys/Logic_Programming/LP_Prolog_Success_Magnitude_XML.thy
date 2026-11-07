theory LP_Prolog_Success_Magnitude_XML
 imports LP_Prolog_Success_Magnitude_Program LP_Prolog_Success_Transfer_XML
begin

partial_function (sum_bot) lpp_magnitude_bound_parser :: "lpp_magnitude_bound xmlt" where
[code]: "lpp_magnitude_bound_parser x = (
  (XMLdo (STR ''knownBound'') {i\<leftarrow>xml_nat (STR ''position''); xml_return (LPPMKnown i)}) XMLor
  (XMLdo (STR ''zeroBound'') {xml_return LPPMZero}) XMLor
  (XMLdo (STR ''quotientBound'') {p\<leftarrow>lpp_magnitude_bound_parser; xml_return (LPPMQuotient p)})) x"

definition lpp_magnitude_fact_parser where
  "lpp_magnitude_fact_parser =
    (XMLdo (STR ''evaluationBound'') {i\<leftarrow>xml_nat (STR ''guard'');
      e\<leftarrow>lpc_term_parser; r\<leftarrow>lpc_term_parser; p\<leftarrow>lpp_magnitude_bound_parser;
      xml_return (LPPMGEvaluate i e r p)}) XMLor
    (XMLdo (STR ''moduloBound'') {i\<leftarrow>xml_nat (STR ''guard'');
      a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser; r\<leftarrow>lpc_term_parser;
      p\<leftarrow>lpp_magnitude_bound_parser; xml_return (LPPMGModulo i a b r p)}) XMLor
    (XMLdo (STR ''helperBound'') {i\<leftarrow>xml_nat (STR ''call''); j\<leftarrow>xml_nat (STR ''argument'');
      a\<leftarrow>lpp_success_atom_parser;
      ps\<leftarrow>xml_many (STR ''inputs'') lpp_magnitude_bound_parser id;
      xml_return (LPPMGHelper i j a ps)})"

definition lpp_magnitude_contract_parser where
  "lpp_magnitude_contract_parser = XMLdo (STR ''prologSuccessMagnitudeContract'') {
    summaries\<leftarrow>xml_many (STR ''summaries'') (XMLdo (STR ''summary'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity'');
      positions\<leftarrow>xml_many (STR ''positions'') (xml_nat (STR ''position'')) id;
      xml_return ((p,n),positions)}) id;
    P\<leftarrow>xml_many (STR ''successProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpp_success_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpp_success_atom_parser id;
      gs\<leftarrow>xml_many (STR ''guards'') lpp_success_guard_parser id;
      xml_return (h,bs,gs)}) id;
    receipts\<leftarrow>xml_many (STR ''proofs'') (XMLdo (STR ''clause'') {
      rs\<leftarrow>xml_many (STR ''outputs'') (XMLdo (STR ''output'') {
        fs\<leftarrow>xml_many (STR ''facts'') lpp_magnitude_fact_parser id;
        p\<leftarrow>xml_singleton (STR ''result'') lpp_magnitude_bound_parser id;
        xml_return (fs,p)}) id;
      xml_return rs}) id;
    xml_return (summaries,P,receipts)}"

definition lpp_check_magnitude_contract where
  "lpp_check_magnitude_contract summaries P receipts =
    (distinct (map fst summaries) \<and> lpp_check_magnitude_program (lpp_summary_lookup summaries) P receipts)"

definition check_lpp_success_magnitude_xml where
  "check_lpp_success_magnitude_xml xml = (case parse_xml_string lpp_magnitude_contract_parser xml of
    Right (summaries,P,receipts) \<Rightarrow> lpp_check_magnitude_contract summaries P receipts | _ \<Rightarrow> False)"

theorem check_lpp_success_magnitude_xml_sound:
  assumes parsed: "parse_xml_string lpp_magnitude_contract_parser xml = Right (summaries,P,receipts)"
    and checked: "check_lpp_success_magnitude_xml xml"
    and compatible: "lpp_stable_integer_operations operation"
    and success: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) a"
  shows "lpp_magnitude_holds operation (lpp_summary_lookup summaries) a"
proof -
  have program: "lpp_check_magnitude_program (lpp_summary_lookup summaries) P receipts"
    using checked parsed by (simp add: check_lpp_success_magnitude_xml_def lpp_check_magnitude_contract_def)
  show ?thesis by (rule lpp_check_magnitude_program_sound[OF compatible program success])
qed

text \<open>This is a conditional successful-return contract. Source assembly
must bind the complete program and separately discharge termination children.\<close>

definition lpp_check_bound_magnitude_contract where
  "lpp_check_bound_magnitude_contract expected summaries P receipts =
    (P=expected \<and> lpp_check_magnitude_contract summaries P receipts)"

theorem lpp_check_bound_magnitude_contract_sound:
  assumes checked: "lpp_check_bound_magnitude_contract expected summaries P receipts"
    and compatible: "lpp_stable_integer_operations operation"
    and success: "lpp_guarded_success expected (lpp_stable_scalar_evaluation operation) a"
  shows "lpp_magnitude_holds operation (lpp_summary_lookup summaries) a"
  using checked lpp_check_magnitude_program_sound[OF compatible, of
    "lpp_summary_lookup summaries" expected receipts a] success
  by (auto simp: lpp_check_bound_magnitude_contract_def lpp_check_magnitude_contract_def)

ML \<open>
val checked = [@{thm check_lpp_success_magnitude_xml_sound},
  @{thm lpp_check_bound_magnitude_contract_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted magnitude XML dependency" else ();
\<close>
end
