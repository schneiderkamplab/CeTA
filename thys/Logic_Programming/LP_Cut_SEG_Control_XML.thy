theory LP_Cut_SEG_Control_XML
  imports LP_Cut_SEG_Control LP_Cut_Return_Module_XML
begin

record 'f lpc_seg_control_data =
  lpcsc_program :: "('f lp_cut_symbol,string) lp_clause list"
  lpcsc_nodes :: "'f lpc_node list"
  lpcsc_states :: "'f lpc_return_state list"
  lpcsc_returned :: "'f lp_cut_symbol"
  lpcsc_arity :: nat
  lpcsc_actions :: "'f lpc_return_module_action option list"
  lpcsc_ranks :: "('f lp_cut_symbol * nat) list"
  lpcsc_boundaries :: "(nat * nat) list"

definition lpc_seg_control_parser where
  "lpc_seg_control_parser = XMLdo (STR ''segControl'') {
    Q\<leftarrow>xml_many (STR ''controlProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    actions\<leftarrow>xml_many (STR ''actions'')
      ((XMLdo (STR ''boundary'') {xml_return None}) XMLor
       (xml_change lpc_return_module_action_parser (\<lambda>a. xml_return (Some a)))) id;
    ranks\<leftarrow>xml_many (STR ''ranks'') (XMLdo (STR ''rank'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''value''); xml_return (f,n)}) id;
    boundaries\<leftarrow>xml_many (STR ''boundaries'') (xml_pair (STR ''boundary'')
      (xml_nat (STR ''local'')) (xml_nat (STR ''target'')) Pair) id;
    xml_return \<lparr>lpcsc_program=Q,lpcsc_nodes=nds,lpcsc_states=states,
      lpcsc_returned=returned,lpcsc_arity=arity,lpcsc_actions=actions,
      lpcsc_ranks=ranks,lpcsc_boundaries=boundaries\<rparr>}"

definition lpc_seg_control_rank where
  "lpc_seg_control_rank data f = (case map_of (lpcsc_ranks data) f of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

definition lpc_seg_control_data_check where
  "lpc_seg_control_data_check fuel P data =
    (distinct (map fst (lpcsc_ranks data)) \<and>
     distinct (map fst (lpcsc_boundaries data)) \<and>
     set (map fst (lpcsc_boundaries data)) =
       set (filter (\<lambda>i. lpcsc_actions data!i=None) [0..<length (lpcsc_actions data)]) \<and>
     lpc_seg_ranked_control (lpc_seg_control_rank data) (lpcsc_program data) \<and>
     lpc_seg_check_control fuel P (lpcsc_program data) (lpcsc_nodes data)
       (lpcsc_states data) (lpcsc_returned data) (lpcsc_arity data) (lpcsc_actions data))"

text \<open>This diagnostic checks only the local operations and finite ranks.
It deliberately has no source-termination conclusion: boundary contracts and
connection/Split rules must be discharged by the source-bound root checker.\<close>
definition lpc_seg_control_diagnostic_parser where
  "lpc_seg_control_diagnostic_parser = XMLdo (STR ''lpCutSEGControl'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); data\<leftarrow>lpc_seg_control_parser;
    xml_return (P,fuel,data)}"

definition check_lpc_seg_control_xml where
  "check_lpc_seg_control_xml xml = (case parse_xml_string lpc_seg_control_diagnostic_parser xml of
    Right (P,fuel,data) \<Rightarrow> lpc_seg_control_data_check fuel P data | _ \<Rightarrow> False)"

end
