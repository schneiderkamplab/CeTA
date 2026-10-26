theory ITS_Parser
  imports IA_Nontermination LTS.LTS_Parser
begin

definition ia_ground_state_parser :: "string ia_ground_state xmlt" where
  "ia_ground_state_parser = XMLdo (STR ''state'') {
    loc \<leftarrow> xml_text (STR ''locationId'');
    vs \<leftarrow> XMLdo (STR ''substitution'') {
      entries \<leftarrow>* XMLdo (STR ''substEntry'') {
        v \<leftarrow> variable_parser;
        n \<leftarrow> xml_int (STR ''constant'');
        xml_return (v,n)
      };
      xml_return entries
    };
    xml_return (vs,loc)
  }"

definition ia_ground_step_parser :: "string ia_ground_step xmlt" where
  "ia_ground_step_parser = XMLdo (STR ''transitionStep'') {
    tr \<leftarrow> transition_parser (location_parser xml_text) (trans_id xml_text) tatom_parser;
    tgt \<leftarrow> ia_ground_state_parser;
    xml_return (tr,tgt)
  }"

definition lts_nontermination_proof_parser :: "string ia_nontermination_proof xmlt" where
  "lts_nontermination_proof_parser = XMLdo (STR ''equivalentState'') {
    init \<leftarrow> ia_ground_state_parser;
    stem \<leftarrow> xml_do (STR ''stem'') (xml_take_many 0 \<infinity> ia_ground_step_parser xml_return);
    loop \<leftarrow> xml_do (STR ''loop'') (xml_take_many 1 \<infinity> ia_ground_step_parser xml_return);
    xml_return (IA_EquivalentState init stem loop)
  }"

datatype its_proof = ITS_Termination
  "(IA.sig,string,IA.ty,string,string,la_solver_type) termination_proof"
  | ITS_Nontermination "string ia_nontermination_proof"

definition its_proof_parser :: "its_proof xmlt" where
  "its_proof_parser = XMLdo (STR ''proof'') {
    prf \<leftarrow> (XMLdo (STR ''ltsTerminationProof'') {
      p \<leftarrow> lts_termination_proof_parser;
      xml_return (ITS_Termination p)
    }) XMLor (XMLdo (STR ''ltsNonterminationProof'') {
      p \<leftarrow> lts_nontermination_proof_parser;
      xml_return (ITS_Nontermination p)
    });
    xml_return prf
  }"

definition its_cpf_parser where
  "its_cpf_parser = XMLdo (STR ''certificationProblem'') {
    version \<leftarrow> xml_text (STR ''cpfVersion'');
    tables \<leftarrow> XMLdo (STR ''lookupTables'') {
      t \<leftarrow> XMLdo (STR ''ruleTable'') {xml_return ()};
      xml_return t
    };
    input \<leftarrow> XMLdo (STR ''input'') {p \<leftarrow> lts_input_parser; xml_return p};
    property \<leftarrow> XMLdo (STR ''property'') {
      p \<leftarrow> XMLdo (STR ''termination'') {xml_return ()}; xml_return p
    };
    answer \<leftarrow> XMLdo (STR ''answer'') {
      a \<leftarrow> (XMLdo (STR ''yes'') {xml_return True}) XMLor (XMLdo (STR ''no'') {xml_return False});
      xml_return a
    };
    proof \<leftarrow> its_proof_parser;
    xml_return (input,answer,proof)
  }"

fun check_its where
  "check_its P True (ITS_Termination proof) = IA.check_termination P proof"
| "check_its P False (ITS_Nontermination proof) = IA.check_ground_nontermination P proof"
| "check_its _ _ _ = Inl (showsl_lit (STR ''ITS verdict/proof mismatch''))"

lemma check_its_sound:
  "isOK (check_its P answer proof) \<Longrightarrow> IA.lts_termination (lts_of P) = answer"
  by (cases "proof"; cases answer; auto dest: IA.check_termination IA.check_ground_nontermination)

definition check_its_string :: "string \<Rightarrow> string + unit" where
  "check_its_string s = (case parse_xml_string its_cpf_parser s of
      Bottom \<Rightarrow> Inl ''ITS parser did not terminate''
    | Left message \<Rightarrow> Inl message
    | Right (p,a,proof) \<Rightarrow> (case check_its p a proof of
        Inl message \<Rightarrow> Inl (String.explode (message (STR '''')))
      | Inr () \<Rightarrow> Inr ()))"

export_code check_its_string Inl Inr char_of_integer integer_of_char in Haskell module_name ITS_Checker
end
