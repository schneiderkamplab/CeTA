theory Checkpoint_Certificate_Parser
 imports "Proof_Checker.CPF_Input_Parser" "Proof_Checker_Base.DP_Checkpoint_Proof"
begin

abbreviation checkpoint_xml_pair where
 "checkpoint_xml_pair tag p1 p2 f \<equiv> XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; xml_return (f a b)}"
abbreviation checkpoint_xml_many where
 "checkpoint_xml_many tag p f \<equiv> XMLdo tag {a \<leftarrow>* p; xml_return (f a)}"
abbreviation checkpoint_xml_tuple4 where
 "checkpoint_xml_tuple4 tag p1 p2 p3 p4 f \<equiv>
 XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; c \<leftarrow> p3; d \<leftarrow> p4; xml_return (f a b c d)}"

context fixes xml2name :: "('f :: {showl,compare_order}, 'l :: {showl,compare_order}) lab xmlt"
 and termIndexMap :: "('f,'l) lab termIndexMap"
begin

partial_function (sum_bot) checkpoint_template_parser :: "(('f,'l) lab,nat) term xmlt"
where [code]: "checkpoint_template_parser x = (
 XMLdo (STR ''funapp'') {
  f \<leftarrow> xml2name;
  ts \<leftarrow>* checkpoint_template_parser;
  xml_return (Fun f ts)
 } XMLor xml_change (xml_nat (STR ''var'')) (\<lambda>i. xml_return (Var i))) x"

definition checkpoint_schema_receipt_parser where
 "checkpoint_schema_receipt_parser = (
 XMLdo (STR ''unrestricted'') {xml_return None} XMLor
 XMLdo (STR ''instance'') {
  i \<leftarrow> xml_nat (STR ''schema'');
  ts \<leftarrow> checkpoint_xml_many (STR ''images'') (term xml2name termIndexMap) id;
  xml_return (Some (i,ts))})"

definition checkpoint_index_map_parser where
 "checkpoint_index_map_parser tag = checkpoint_xml_many tag
 (checkpoint_xml_pair (STR ''entry'') xml2name (xml_nat (STR ''index'')) Pair) id"
definition checkpoint_atom_parser where
 "checkpoint_atom_parser = (
 XMLdo (STR ''exact'') {
  i0 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Exact i0)
 } XMLor
 XMLdo (STR ''split'') {
  i0 \<leftarrow> xml_nat (STR ''index'');
  i1 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Split i0 i1)
 } XMLor
 XMLdo (STR ''prefix'') {
  i0 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Prefix i0)
 } XMLor
 XMLdo (STR ''strict'') {
  i0 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Strict i0)
 } XMLor
 XMLdo (STR ''guard'') {
  i0 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Guard i0)
 } XMLor
 XMLdo (STR ''arguments'') {
  f \<leftarrow> xml2name;
  i0 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Arguments f i0)
 } XMLor
 XMLdo (STR ''ground'') {
  f \<leftarrow> xml2name;
  i0 \<leftarrow> xml_nat (STR ''index'');
  i1 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_Ground f i0 i1)
 } XMLor
 XMLdo (STR ''list'') {
  f \<leftarrow> xml2name;
  i0 \<leftarrow> xml_nat (STR ''index'');
  i1 \<leftarrow> xml_nat (STR ''index'');
  xml_return (CP_List f i0 i1)
 })"
definition checkpoint_argument_registration_parser where
 "checkpoint_argument_registration_parser = XMLdo (STR ''summary'') {
  (f0,f1,f2) \<leftarrow> XMLdo (STR ''signature'') {
   f0 \<leftarrow> xml2name;
   f1 \<leftarrow> xml2name;
   f2 \<leftarrow> xml2name;
   xml_return (f0,f1,f2)
  };
  witnesses \<leftarrow> checkpoint_xml_many (STR ''rules'') checkpoint_schema_receipt_parser id;
  xml_return (f0,f1,f2,witnesses)
 }"
definition checkpoint_ground_registration_parser where
 "checkpoint_ground_registration_parser = XMLdo (STR ''summary'') {
  (f0,f1,f2,f3,f4,f5,f6) \<leftarrow> XMLdo (STR ''signature'') {
   f0 \<leftarrow> xml2name;
   f1 \<leftarrow> xml2name;
   f2 \<leftarrow> xml2name;
   f3 \<leftarrow> xml2name;
   f4 \<leftarrow> xml2name;
   f5 \<leftarrow> xml2name;
   f6 \<leftarrow> xml2name;
   xml_return (f0,f1,f2,f3,f4,f5,f6)
  };
  witnesses \<leftarrow> checkpoint_xml_many (STR ''rules'') checkpoint_schema_receipt_parser id;
  xml_return (f0,f1,f2,f3,f4,f5,f6,witnesses)
 }"
definition checkpoint_list_registration_parser where
 "checkpoint_list_registration_parser = XMLdo (STR ''summary'') {
  (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10) \<leftarrow> XMLdo (STR ''signature'') {
   f0 \<leftarrow> xml2name;
   f1 \<leftarrow> xml2name;
   f2 \<leftarrow> xml2name;
   f3 \<leftarrow> xml2name;
   f4 \<leftarrow> xml2name;
   f5 \<leftarrow> xml2name;
   f6 \<leftarrow> xml2name;
   f7 \<leftarrow> xml2name;
   f8 \<leftarrow> xml2name;
   f9 \<leftarrow> xml2name;
   f10 \<leftarrow> xml2name;
   xml_return (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10)
  };
  templates \<leftarrow> checkpoint_xml_many (STR ''templates'') checkpoint_template_parser id;
  witnesses \<leftarrow> checkpoint_xml_many (STR ''rules'') checkpoint_schema_receipt_parser id;
  domains \<leftarrow> checkpoint_xml_many (STR ''domains'') checkpoint_schema_receipt_parser id;
  xml_return (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,templates,witnesses,domains)
 }"

definition checkpoint_clause_parser where
 "checkpoint_clause_parser = XMLdo (STR ''clause'') {
  f \<leftarrow> xml2name;
  n \<leftarrow> xml_nat (STR ''arity'');
  atoms \<leftarrow> checkpoint_xml_many (STR ''atoms'') checkpoint_atom_parser id;
  xml_return (f,n,atoms)
 }"

definition checkpoint_claim_parser where
 "checkpoint_claim_parser = XMLdo (STR ''claim'') {
  atom \<leftarrow> checkpoint_atom_parser;
  ts \<leftarrow> checkpoint_xml_many (STR ''terms'') (term xml2name termIndexMap) id;
  xml_return (atom,ts)
 }"

definition checkpoint_inference_parser where
 "checkpoint_inference_parser = XMLdo (STR ''step'') {
  code \<leftarrow> xml_nat (STR ''code'');
  fs \<leftarrow> checkpoint_xml_many (STR ''symbols'') xml2name id;
  ts \<leftarrow> checkpoint_xml_many (STR ''terms'') (term xml2name termIndexMap) id;
  refs \<leftarrow> checkpoint_xml_many (STR ''references'') (xml_nat (STR ''index'')) id;
  claim \<leftarrow> checkpoint_claim_parser;
  xml_return ((code,fs,ts,refs),claim)
 }"

definition checkpoint_transition_parser where
 "checkpoint_transition_parser = XMLdo (STR ''transition'') {
  i \<leftarrow> xml_nat (STR ''pair'');
  antecedents \<leftarrow> checkpoint_xml_many (STR ''before'') checkpoint_atom_parser id;
  derivation \<leftarrow> checkpoint_xml_many (STR ''derivation'') checkpoint_inference_parser id;
  after \<leftarrow> checkpoint_xml_many (STR ''after'') checkpoint_atom_parser id;
  xml_return (i,antecedents,derivation,after)
 }"

definition checkpoint_ranking_certificate_parser where
 "checkpoint_ranking_certificate_parser = XMLdo (STR ''checkpointRankingProc'') {
  version \<leftarrow> xml_nat (STR ''version'');
  ordered_pairs \<leftarrow> checkpoint_xml_many (STR ''orderedPairs'') (rule xml2name termIndexMap Mapping.empty) id;
  ordered_support \<leftarrow> checkpoint_xml_many (STR ''orderedSupport'') (rule xml2name termIndexMap Mapping.empty) id;
  constructors \<leftarrow> checkpoint_xml_many (STR ''constructors'') xml2name id;
  roles \<leftarrow> checkpoint_xml_tuple4 (STR ''roles'') xml2name xml2name xml2name xml2name (\<lambda>a b c d. (a,b,c,d));
  controls \<leftarrow> checkpoint_xml_many (STR ''controls'') xml2name id;
  checkpoints \<leftarrow> checkpoint_xml_many (STR ''checkpoints'') xml2name id;
  heights \<leftarrow> checkpoint_index_map_parser (STR ''heights'');
  coordinates \<leftarrow> checkpoint_index_map_parser (STR ''coordinates'');
  arguments \<leftarrow> checkpoint_xml_many (STR ''arguments'') checkpoint_argument_registration_parser id;
  grounds \<leftarrow> checkpoint_xml_many (STR ''grounds'') checkpoint_ground_registration_parser id;
  list_regs \<leftarrow> checkpoint_xml_many (STR ''lists'') checkpoint_list_registration_parser id;
  annotation \<leftarrow> checkpoint_xml_many (STR ''annotation'') checkpoint_clause_parser id;
  receipts \<leftarrow> checkpoint_xml_many (STR ''transitions'') checkpoint_transition_parser id;
  xml_return (Checkpoint_Certificate version ordered_pairs ordered_support constructors roles controls checkpoints heights coordinates
   arguments grounds list_regs annotation receipts)
 }"

end
end
