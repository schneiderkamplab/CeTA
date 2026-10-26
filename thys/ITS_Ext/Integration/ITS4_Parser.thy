theory ITS4_Parser
  imports IA4_Nontermination IA4_Parser
begin

definition ia4_ground_state_parser :: "string ia4_ground_state xmlt" where
  "ia4_ground_state_parser = XMLdo (STR ''state'') {
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

definition ia4_ground_step_parser :: "string ia4_ground_step xmlt" where
  "ia4_ground_step_parser = XMLdo (STR ''transitionStep'') {
    tr \<leftarrow> transition_parser (location_parser xml_text) (trans_id xml_text) ia4_tatom_parser;
    tgt \<leftarrow> ia4_ground_state_parser;
    xml_return (tr,tgt)
  }"

definition ia4_lts_nontermination_proof_parser :: "string ia4_nontermination_proof xmlt" where
  "ia4_lts_nontermination_proof_parser = XMLdo (STR ''equivalentState'') {
    init \<leftarrow> ia4_ground_state_parser;
    stem \<leftarrow> xml_do (STR ''stem'') (xml_take_many 0 \<infinity> ia4_ground_step_parser xml_return);
    loop \<leftarrow> xml_do (STR ''loop'') (xml_take_many 1 \<infinity> ia4_ground_step_parser xml_return);
    xml_return (IA4_EquivalentState init stem loop)
  }"

datatype its4_proof = ITS4_Termination
  "(ia4_sig,string,IA.ty,string,string,la_solver_type) termination_proof"
  | ITS4_Nontermination "string ia4_nontermination_proof"

definition its4_proof_parser :: "its4_proof xmlt" where
  "its4_proof_parser = XMLdo (STR ''proof'') {
    prf \<leftarrow> (XMLdo (STR ''ltsTerminationProof'') {
      p \<leftarrow> ia4_lts_termination_proof_parser;
      xml_return (ITS4_Termination p)
    }) XMLor (XMLdo (STR ''ltsNonterminationProof'') {
      p \<leftarrow> ia4_lts_nontermination_proof_parser;
      xml_return (ITS4_Nontermination p)
    });
    xml_return prf
  }"

definition its4_cpf_parser where
  "its4_cpf_parser = XMLdo (STR ''certificationProblem'') {
    version \<leftarrow> xml_text (STR ''cpfVersion'');
    tables \<leftarrow> XMLdo (STR ''lookupTables'') {
      t \<leftarrow> XMLdo (STR ''ruleTable'') {xml_return ()};
      xml_return t
    };
    input \<leftarrow> XMLdo (STR ''input'') {p \<leftarrow> ia4_lts_input_parser; xml_return p};
    property \<leftarrow> XMLdo (STR ''property'') {
      p \<leftarrow> XMLdo (STR ''termination'') {xml_return ()}; xml_return p
    };
    answer \<leftarrow> XMLdo (STR ''answer'') {
      a \<leftarrow> (XMLdo (STR ''yes'') {xml_return True}) XMLor (XMLdo (STR ''no'') {xml_return False});
      xml_return a
    };
    proof \<leftarrow> its4_proof_parser;
    xml_return (input,answer,proof)
  }"

fun check_its4 where
  "check_its4 P True (ITS4_Termination proof) = ia4_check_termination P proof"
| "check_its4 P False (ITS4_Nontermination proof) = ia4_check_ground_nontermination P proof"
| "check_its4 _ _ _ = Inl (showsl_lit (STR ''ITS verdict/proof mismatch''))"

lemma check_its4_sound:
  "isOK (check_its4 P answer proof) \<Longrightarrow> IA4Termination.lts_termination (lts_of P) = answer"
  by (cases "proof"; cases answer; auto dest: ia4_check_termination_sound ia4_check_ground_nontermination)

definition check_its4_string :: "string \<Rightarrow> string + unit" where
  "check_its4_string s = (case parse_xml_string its4_cpf_parser s of
      Bottom \<Rightarrow> Inl ''ITS parser did not terminate''
    | Left message \<Rightarrow> Inl message
    | Right (p,a,proof) \<Rightarrow> (case check_its4 p a proof of
        Inl message \<Rightarrow> Inl (String.explode (message (STR '''')))
      | Inr () \<Rightarrow> Inr ()))"

export_code check_its4_string Inl Inr char_of_integer integer_of_char in Haskell module_name ITS_Checker
end
