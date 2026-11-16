theory LP_Prolog_Success_Types_XML
  imports LP_Prolog_Success_Types LP_Prolog_Integer_NO_XML
begin

partial_function (sum_bot) lpp_integer_expression_parser :: "string lpp_integer_expression xmlt" where
[code]: "lpp_integer_expression_parser x = (
  xml_change (xml_int (STR ''integer'')) (xml_return \<circ> LPPEConstant) XMLor
  xml_change (xml_text (STR ''var'')) (xml_return \<circ> LPPEVariable) XMLor
  (XMLdo (STR ''positive'') {a\<leftarrow>lpp_integer_expression_parser; xml_return (LPPEPositive a)}) XMLor
  (XMLdo (STR ''negate'') {a\<leftarrow>lpp_integer_expression_parser; xml_return (LPPENegate a)}) XMLor
  (XMLdo (STR ''add'') {a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser; xml_return (LPPEAdd a b)}) XMLor
  (XMLdo (STR ''subtract'') {a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser; xml_return (LPPESubtract a b)}) XMLor
  (XMLdo (STR ''multiply'') {a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser; xml_return (LPPEMultiply a b)}) XMLor
  (XMLdo (STR ''divide'') {a\<leftarrow>lpp_integer_expression_parser; d\<leftarrow>xml_int (STR ''divisor''); xml_return (LPPEDivide a d)}) XMLor
  (XMLdo (STR ''modulo'') {a\<leftarrow>lpp_integer_expression_parser; d\<leftarrow>xml_int (STR ''divisor''); xml_return (LPPEModulo a d)})) x"

definition lpp_success_atom_parser where
  "lpp_success_atom_parser = XMLdo (STR ''atom'') {
    p\<leftarrow>xml_text (STR ''predicate''); ts\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
    xml_return (p,ts)}"

definition lpp_success_guard_parser where
  "lpp_success_guard_parser =
    (xml_singleton (STR ''integerGuard'') lpc_term_parser LPPSInteger) XMLor
    (XMLdo (STR ''evaluationGuard'') {e\<leftarrow>lpc_term_parser; t\<leftarrow>lpc_term_parser; xml_return (LPPSEvaluates e t)}) XMLor
    (XMLdo (STR ''numericSuccessGuard'') {c\<leftarrow>xml_nat (STR ''comparison'');
      a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser; xml_return (LPPSNumeric c a b)}) XMLor
    (xml_singleton (STR ''opaqueGuard'') lpc_term_parser LPPSOpaque)"

definition lpp_integer_fact_parser where
  "lpp_integer_fact_parser =
    (XMLdo (STR ''guardFact'') {i\<leftarrow>xml_nat (STR ''guard''); x\<leftarrow>xml_text (STR ''var''); xml_return (LPPSGuard i x)}) XMLor
    (XMLdo (STR ''helperFact'') {i\<leftarrow>xml_nat (STR ''call''); j\<leftarrow>xml_nat (STR ''argument''); x\<leftarrow>xml_text (STR ''var''); xml_return (LPPSHelper i j x)}) XMLor
    (XMLdo (STR ''evaluationFact'') {i\<leftarrow>xml_nat (STR ''guard''); e\<leftarrow>lpp_integer_expression_parser; x\<leftarrow>xml_text (STR ''result''); xml_return (LPPSEvaluation i e x)})"

definition lpp_integer_output_parser where
  "lpp_integer_output_parser =
    (xml_change (xml_text (STR ''var'')) (xml_return \<circ> LPPSVariable)) XMLor
    (xml_change (xml_int (STR ''integer'')) (xml_return \<circ> LPPSConstant))"

definition lpp_success_contract_parser where
  "lpp_success_contract_parser = XMLdo (STR ''prologSuccessTypeContract'') {
    summaries\<leftarrow>xml_many (STR ''summaries'') (XMLdo (STR ''summary'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity'');
      positions\<leftarrow>xml_many (STR ''positions'') (xml_nat (STR ''position'')) id;
      xml_return ((p,n),positions)}) id;
    P\<leftarrow>xml_many (STR ''successProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpp_success_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpp_success_atom_parser id;
      gs\<leftarrow>xml_many (STR ''guards'') lpp_success_guard_parser id;
      xml_return (h,bs,gs)}) id;
    proofs\<leftarrow>xml_many (STR ''proofs'') (XMLdo (STR ''clause'') {
      fs\<leftarrow>xml_many (STR ''facts'') lpp_integer_fact_parser id;
      os\<leftarrow>xml_many (STR ''outputs'') lpp_integer_output_parser id;
      xml_return (fs,os)}) id;
    xml_return (summaries,P,proofs)}"

definition lpp_summary_lookup where
  "lpp_summary_lookup summaries sig = (case map_of summaries sig of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)"

definition lpp_check_success_contract where
  "lpp_check_success_contract summaries P proofs =
    (distinct (map fst summaries) \<and> lpp_check_success_program (lpp_summary_lookup summaries) P proofs)"

definition check_lpp_success_contract_xml where
  "check_lpp_success_contract_xml xml = (case parse_xml_string lpp_success_contract_parser xml of
    Right (summaries,P,proofs) \<Rightarrow> lpp_check_success_contract summaries P proofs | _ \<Rightarrow> False)"

theorem check_lpp_success_contract_xml_sound:
  assumes parsed: "parse_xml_string lpp_success_contract_parser xml = Right (summaries,P,proofs)"
    and checked: "check_lpp_success_contract_xml xml"
    and evaluation: "lpp_eval_integer_contract TYPE(string) E"
    and success: "lpp_guarded_success P E a"
  shows "lpp_success_summary_holds (lpp_summary_lookup summaries) a"
proof -
  have check: "lpp_check_success_program (lpp_summary_lookup summaries) P proofs"
    using checked parsed by (simp add: check_lpp_success_contract_xml_def lpp_check_success_contract_def)
  show ?thesis by (rule lpp_check_success_program_sound[OF check evaluation success])
qed

text \<open>This checker validates a conditional helper-return contract. It is
not a root proof and is deliberately absent from the source-verdict dispatcher.
The enclosing source bridge must bind the full extracted program, instantiate
the evaluation contract, and discharge every helper termination obligation.\<close>

ML \<open>
val success_type_theorems = [@{thm lpp_check_success_program_sound},
  @{thm check_lpp_success_contract_xml_sound}, @{thm lpp_success_summary_subst}];
val success_type_oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = success_type_oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof success_type_theorems orelse
  exists (fn n => not (member (op =) inherited n)) (success_type_oracles success_type_theorems)
  then error "Untrusted helper-return contract dependency" else ();
\<close>
end
