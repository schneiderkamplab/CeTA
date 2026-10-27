theory ITS4_Parser
  imports IA4_Recurrent_Cycle IA4_Parser
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

definition ia4_policy_parser :: "string ia4_policy xmlt" where
  "ia4_policy_parser = XMLdo (STR ''policy'') {
    entries \<leftarrow>* XMLdo (STR ''assignment'') {
      v \<leftarrow> variable_parser;
      e \<leftarrow> ia4_exp_parser;
      xml_return ((v,IA.IntT),e)
    };
    xml_return entries
  }"

definition ia4_policy_step_parser :: "string ia4_policy_step xmlt" where
  "ia4_policy_step_parser = XMLdo (STR ''policyStep'') {
    tr \<leftarrow> transition_parser (location_parser xml_text) (trans_id xml_text) ia4_tatom_parser;
    post \<leftarrow> ia4_policy_parser;
    local \<leftarrow> ia4_policy_parser;
    xml_return (tr,post,local)
  }"

datatype its4_proof = ITS4_Termination
  "(ia4_sig,string,IA.ty,string,string,la_solver_type) termination_proof"
  | ITS4_Nontermination "string ia4_nontermination_proof"
  | ITS4_Recurrent "string ia4_ground_state" "string ia4_ground_step list"
      "string ia4_exp formula" "string \<times> (ia4_sig,string,IA.ty,string) transition_rule"
      "string ia4_policy" "string ia4_policy"
  | ITS4_RecurrentCycle "string ia4_ground_state" "string ia4_ground_step list"
      "string ia4_exp formula" "string ia4_policy_step list"

definition its4_proof_parser :: "its4_proof xmlt" where
  "its4_proof_parser = XMLdo (STR ''proof'') {
    prf \<leftarrow> (XMLdo (STR ''ltsTerminationProof'') {
      p \<leftarrow> ia4_lts_termination_proof_parser;
      xml_return (ITS4_Termination p)
    }) XMLor (XMLdo (STR ''ltsNonterminationProof'') {
      p \<leftarrow> (xml_change ia4_lts_nontermination_proof_parser (xml_return \<circ> ITS4_Nontermination))
        XMLor (XMLdo (STR ''recurrentSet'') {
          init \<leftarrow> ia4_ground_state_parser;
          stem \<leftarrow> xml_do (STR ''stem'') (xml_take_many 0 \<infinity> ia4_ground_step_parser xml_return);
          region \<leftarrow> xml_do (STR ''region'') (xml_take (formula_parser ia4_atom_parser) xml_return);
          tr \<leftarrow> transition_parser (location_parser xml_text) (trans_id xml_text) ia4_tatom_parser;
          post \<leftarrow> ia4_policy_parser;
          local \<leftarrow> ia4_policy_parser;
          xml_return (ITS4_Recurrent init stem region tr post local)
        }) XMLor (XMLdo (STR ''recurrentCycle'') {
          init \<leftarrow> ia4_ground_state_parser;
          stem \<leftarrow> xml_do (STR ''stem'') (xml_take_many 0 \<infinity> ia4_ground_step_parser xml_return);
          region \<leftarrow> xml_do (STR ''region'') (xml_take (formula_parser ia4_atom_parser) xml_return);
          steps \<leftarrow> xml_do (STR ''cycle'') (xml_take_many 1 \<infinity> ia4_policy_step_parser xml_return);
          xml_return (ITS4_RecurrentCycle init stem region steps)
        });
      xml_return p
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
| "check_its4 P False (ITS4_Recurrent init stem region tr post local) = ia4_check_recurrent P init stem region tr post local"
| "check_its4 P False (ITS4_RecurrentCycle init stem region steps) = ia4_check_recurrent_cycle P init stem region steps"
| "check_its4 _ _ _ = Inl (showsl_lit (STR ''ITS verdict/proof mismatch''))"

lemma check_its4_sound:
  "isOK (check_its4 P answer proof) \<Longrightarrow> IA4Termination.lts_termination (lts_of P) = answer"
  by (cases "proof"; cases answer; auto dest: ia4_check_termination_sound ia4_check_ground_nontermination ia4_check_recurrent_sound ia4_check_recurrent_cycle_sound)

definition check_its4_string :: "string \<Rightarrow> string + unit" where
  "check_its4_string s = (case parse_xml_string its4_cpf_parser s of
      Bottom \<Rightarrow> Inl ''ITS parser did not terminate''
    | Left message \<Rightarrow> Inl message
    | Right (p,a,proof) \<Rightarrow> (case check_its4 p a proof of
        Inl message \<Rightarrow> Inl (String.explode (message (STR '''')))
      | Inr () \<Rightarrow> Inr ()))"

export_code check_its4_string Inl Inr char_of_integer integer_of_char in Haskell module_name ITS_Checker
end
