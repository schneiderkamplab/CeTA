theory LP_Prolog_Success_Transfer_XML
  imports LP_Prolog_Success_Transfer LP_Prolog_Success_Types_XML
begin

definition lpp_transfer_fact_parser where
  "lpp_transfer_fact_parser =
    (XMLdo (STR ''inputFact'') {i\<leftarrow>xml_nat (STR ''argument''); x\<leftarrow>xml_text (STR ''var''); xml_return (LPPTInput i x)}) XMLor
    (xml_singleton (STR ''baseFact'') lpp_integer_fact_parser LPPTBase) XMLor
    (XMLdo (STR ''helperTransferFact'') {i\<leftarrow>xml_nat (STR ''call''); r\<leftarrow>xml_nat (STR ''rule'');
      j\<leftarrow>xml_nat (STR ''argument''); x\<leftarrow>xml_text (STR ''var'');
      ws\<leftarrow>xml_many (STR ''inputs'') lpp_integer_output_parser id; xml_return (LPPTHelper i r j x ws)})"

definition lpp_transfer_contract_parser where
  "lpp_transfer_contract_parser = XMLdo (STR ''prologSuccessTransferContract'') {
    summaries\<leftarrow>xml_many (STR ''summaries'') (XMLdo (STR ''summary'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity'');
      rules\<leftarrow>xml_many (STR ''contexts'') (XMLdo (STR ''context'') {
        req\<leftarrow>xml_many (STR ''required'') (xml_nat (STR ''position'')) id;
        outs\<leftarrow>xml_many (STR ''outputs'') (xml_nat (STR ''position'')) id;
        xml_return (req,outs)}) id;
      xml_return ((p,n),rules)}) id;
    P\<leftarrow>xml_many (STR ''successProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpp_success_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpp_success_atom_parser id;
      gs\<leftarrow>xml_many (STR ''guards'') lpp_success_guard_parser id;
      xml_return (h,bs,gs)}) id;
    proofs\<leftarrow>xml_many (STR ''proofs'') (XMLdo (STR ''clause'') {
      rs\<leftarrow>xml_many (STR ''contexts'') (XMLdo (STR ''context'') {
        fs\<leftarrow>xml_many (STR ''facts'') lpp_transfer_fact_parser id;
        os\<leftarrow>xml_many (STR ''outputs'') lpp_integer_output_parser id;
        xml_return (fs,os)}) id;
      xml_return rs}) id;
    xml_return (summaries,P,proofs)}"

definition lpp_transfer_lookup where
  "lpp_transfer_lookup summaries sig = (case map_of summaries sig of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)"
definition lpp_check_transfer_contract where
  "lpp_check_transfer_contract summaries P proofs =
    (distinct (map fst summaries) \<and> lpp_check_transfer_program (lpp_transfer_lookup summaries) P proofs)"
definition check_lpp_success_transfer_xml where
  "check_lpp_success_transfer_xml xml = (case parse_xml_string lpp_transfer_contract_parser xml of
    Right (summaries,P,proofs) \<Rightarrow> lpp_check_transfer_contract summaries P proofs | _ \<Rightarrow> False)"

theorem check_lpp_success_transfer_xml_sound:
  assumes parsed: "parse_xml_string lpp_transfer_contract_parser xml = Right (summaries,P,proofs)"
    and checked: "check_lpp_success_transfer_xml xml"
    and evaluation: "lpp_eval_integer_contract TYPE(string) E"
    and success: "lpp_guarded_success P E a"
  shows "lpp_transfer_holds (lpp_transfer_lookup summaries) a"
proof -
  have check: "lpp_check_transfer_program (lpp_transfer_lookup summaries) P proofs"
    using checked parsed by (simp add: check_lpp_success_transfer_xml_def lpp_check_transfer_contract_def)
  show ?thesis by (rule lpp_check_transfer_program_sound[OF check evaluation success])
qed

ML \<open>
val transfer_theorems = [@{thm lpp_check_transfer_program_sound}, @{thm check_lpp_success_transfer_xml_sound}];
val transfer_oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = transfer_oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof transfer_theorems orelse
  exists (fn n => not (member (op =) inherited n)) (transfer_oracles transfer_theorems)
  then error "Untrusted input-dependent return contract" else ();
\<close>
end
