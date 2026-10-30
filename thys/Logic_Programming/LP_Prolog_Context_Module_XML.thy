theory LP_Prolog_Context_Module_XML
 imports LP_Prolog_Context_XML LP_Prolog_Context_Module_Domain
begin

definition lpp_finite_comparison_parser where
  "lpp_finite_comparison_parser = XMLdo (STR ''finiteComparison'') {
    f\<leftarrow>xml_text (STR ''predicate''); comparison\<leftarrow>lpp_numeric_comparison_parser;
    reversed\<leftarrow>xml_bool (STR ''reversed''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
    gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
    active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
    saved\<leftarrow>lpc_return_state_parser;
    yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser; error\<leftarrow>lpc_link_parser;
    xml_return \<lparr>lppfc_predicate = f, lppfc_comparison = comparison, lppfc_reversed = reversed,
      lppfc_left = a, lppfc_right = b, lppfc_goals = gs, lppfc_active = active, lppfc_saved = saved,
      lppfc_yes = yes, lppfc_no = no, lppfc_error = error\<rparr>}"

definition lpp_context_module_action_parser where
  "lpp_context_module_action_parser =
    (xml_change lpp_finite_comparison_parser (xml_return o LPPCMFiniteComparison)) XMLor
    (xml_change lpp_context_source_action_parser (xml_return o LPPCMPrimitive)) XMLor
    (XMLdo (STR ''trimBarriers'') {successor\<leftarrow>lpc_return_state_parser;
      barriers\<leftarrow>lpc_return_state_parser; e\<leftarrow>lpc_link_parser;
      xml_return (LPPCMTrim successor barriers e)}) XMLor
    (XMLdo (STR ''parallelAlternatives'') {links\<leftarrow>xml_many (STR ''links'') lpc_link_parser id;
      xml_return (LPPCMParallel links)})"

text \<open>This component checks modular return coverage. Source-query and
arithmetic-domain closure plus the residual proof are still required.\<close>
definition lpp_context_module_parser where
  "lpp_context_module_parser = XMLdo (STR ''prologContextModule'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); r\<leftarrow>xml_nat (STR ''root'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    contexts\<leftarrow>xml_many (STR ''contexts'') lpp_source_context_parser id;
    typings\<leftarrow>xml_many (STR ''typings'') (xml_many (STR ''facts'') lpp_transfer_fact_parser id) id;
    transfer\<leftarrow>lpp_transfer_contract_parser;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    actions\<leftarrow>xml_many (STR ''actions'') lpp_context_module_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,fuel,r,nds,states,contexts,typings,transfer,returned,arity,actions,Q)}"

definition check_lpp_context_module_xml where
  "check_lpp_context_module_xml xml = (case parse_xml_string lpp_context_module_parser xml of
    Right (P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,actions,Q) \<Rightarrow>
      lp_cut_source_program P \<and> lpp_check_transfer_contract summaries SP receipts \<and>
      (r<length nds \<and> contexts!r=([],[],[]) \<and> lpp_check_context_module fuel P Q nds states contexts (lpp_transfer_lookup summaries) typings returned arity actions)
    | _ \<Rightarrow> False)"

theorem check_lpp_context_module_xml_contract:
  assumes parsed: "parse_xml_string lpp_context_module_parser xml =
    Right (P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,actions,Q)"
    and checked: "check_lpp_context_module_xml xml"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!r))) (lpcn_guards (nds!r)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!r),map eta (lpcn_vars (nds!r)))]}"
  shows "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin
    (lpc_return_eval eta (states!r)) (lp_ild Q)
    [(lpcn_pred (nds!r),map eta (lpcn_vars (nds!r)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
  by (rule lpp_check_context_module_contract[OF _ _ _ _ _ known residual])
    (use parsed checked in \<open>auto simp: check_lpp_context_module_xml_def lpp_check_transfer_contract_def lpp_path_context_holds_def\<close>)

theorem check_lpp_context_module_xml_domain_SN:
  assumes parsed: "parse_xml_string lpp_context_module_parser xml =
    Right (P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,actions,Q)"
    and checked: "check_lpp_context_module_xml xml"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!r))) (lpcn_guards (nds!r)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!r),map eta (lpcn_vars (nds!r)))]}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta (states!r))}"
proof -
  have contract: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    (lpc_return_eval eta (states!r)) (lp_ild Q)
    [(lpcn_pred (nds!r),map eta (lpcn_vars (nds!r)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_check_context_module_domain_contract[OF _ _ _ _ _ known residual])
      (use parsed checked in \<open>auto simp: check_lpp_context_module_xml_def lpp_check_transfer_contract_def lpp_path_context_holds_def\<close>)
  show ?thesis by (rule lpp_domain_instrumentation_SN)
    (use contract in \<open>simp add: lp_answer_contract_def\<close>)
qed

end
