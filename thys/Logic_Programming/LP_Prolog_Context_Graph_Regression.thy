theory LP_Prolog_Context_Graph_Regression
  imports LP_Prolog_Context_Graph LP_Prolog_Integer_Node_Regression
begin

definition lpp_reg_graph_states :: "string lpc_return_state list" where
  "lpp_reg_graph_states = [lpp_reg_source ''1:integer'' [lpp_integer_term 7],[(LPCGoals [],[])],[]]"
definition lpp_reg_graph_nodes where
  "lpp_reg_graph_nodes = [lpp_reg_node (map fst (lpp_reg_graph_states!0)) ''source'',
    lpp_reg_node [LPCGoals []] ''yes'',lpp_reg_node [] ''no'']"
definition lpp_reg_graph_program :: "(string lp_cut_symbol,string) lp_clause list" where
  "lpp_reg_graph_program = lpp_reg_program @ [((LPCUser ''yes'',[]),[(LPCUser ''no'',[])]),
    ((LPCUser ''yes'',[]),[(LPCUser ''returned'',[])])]"
definition lpp_reg_graph_contexts :: "string lpp_source_context list" where
  "lpp_reg_graph_contexts = [([],[],[]),([],[LPPSInteger (lpp_integer_term 7)],[LPPOInteger (lpp_integer_term 7)]),([],[],[])]"
definition lpp_reg_graph_actions where
  "lpp_reg_graph_actions = map LPPCSPrimitive [LPPIRTest (lpp_integer_term 7) [] [] [] (lpp_reg_link 1 [LPCGoals []]) (lpp_reg_link 2 []),
    LPPIRCut (LPCRAdmin (Some []) [] (lpp_reg_link 2 [])),LPPIRCut LPCRTerminal]"
definition lpp_reg_graph_check where
  "lpp_reg_graph_check Q contexts actions = lpp_check_context_graph 40 ([]::(string,string) lp_cut_program)
    Q lpp_reg_graph_nodes lpp_reg_graph_states contexts (\<lambda>_. []) [[],[],[]] (LPCUser ''returned'') 0 actions"
definition lpp_reg_root_check where
  "lpp_reg_root_check contexts i = lpp_check_context_root 40 ([]::(string,string) lp_cut_program)
    lpp_reg_graph_program lpp_reg_graph_nodes lpp_reg_graph_states contexts (\<lambda>_. []) [[],[],[]]
    (LPCUser ''returned'') 0 lpp_reg_graph_actions i"
definition lpp_reg_staged_state :: "string lpc_return_state" where
  "lpp_reg_staged_state = [(LPCGoals [LPCUnify (lpp_integer_term 1) (Var ''r'')],[])]"
definition lpp_reg_staged_nodes where
  "lpp_reg_staged_nodes = [(lpp_reg_node (map fst lpp_reg_staged_state) ''stage'')\<lparr>lpcn_ground:=[''r'']\<rparr>,
    lpp_reg_node [LPCGoals []] ''yes'',lpp_reg_node [] ''no'']"
definition lpp_reg_staged_program :: "(string lp_cut_symbol,string) lp_clause list" where
  "lpp_reg_staged_program = [((LPCUser ''source'',[]),[(LPCUser ''stage'',[])]),
    ((LPCUser ''stage'',[]),[(LPCUser ''yes'',[])]),((LPCUser ''stage'',[]),[(LPCUser ''no'',[])])]"
definition lpp_reg_staged_check where
  "lpp_reg_staged_check Q K evidence expression (source_context::string lpp_source_context) middle =
    (let ss=lpp_reg_source ''2:is'' [lpp_integer_term 1,expression] in
      lpp_check_context_is_staged 40 ([]::(string,string) lp_cut_program) Q lpp_reg_staged_nodes
      [lpp_reg_staged_state,[(LPCGoals [],[])],[]]
      [([],[LPPSEvaluates (lpp_integer_term 1) (Var ''r'')],[LPPOEvaluation (lpp_integer_term 1) (Var ''r'')]),([],[],[]),([],[],[])]
      (lpp_reg_node (map fst ss) ''source'') ss source_context K evidence (lpp_integer_term 1) expression [] [] [] ''r'' middle
      (LPCUser ''returned'') 0
      (LPCREquality (lpp_integer_term 1) (Var ''r'') [] [] [] 8 16 [] LPCBoth []
        (lpp_reg_link 1 [LPCGoals []]) (lpp_reg_link 2 [])))"
abbreviation lpp_reg_staged_link where
  "lpp_reg_staged_link \<equiv> (lpp_reg_link 0 (map fst lpp_reg_staged_state))\<lparr>lpcl_ground:=[''r'']\<rparr>"
definition lpp_context_staged_regressions where
  "lpp_context_staged_regressions = [
    (''staged-is'',lpp_reg_staged_check lpp_reg_staged_program [] (LPPEConstant 1) (lpp_integer_term 1) ([],[],[]) lpp_reg_staged_link),
    (''staged-is-missing-first-edge'',\<not>lpp_reg_staged_check (tl lpp_reg_staged_program) [] (LPPEConstant 1) (lpp_integer_term 1) ([],[],[]) lpp_reg_staged_link),
    (''staged-is-missing-equality-branch'',\<not>lpp_reg_staged_check (take 2 lpp_reg_staged_program) [] (LPPEConstant 1) (lpp_integer_term 1) ([],[],[]) lpp_reg_staged_link),
    (''staged-is-captured-context'',\<not>lpp_reg_staged_check lpp_reg_staged_program [] (LPPEConstant 1) (lpp_integer_term 1) ([],[LPPSInteger (Var ''r'')],[]) lpp_reg_staged_link),
    (''staged-is-missing-input-type'',\<not>lpp_reg_staged_check lpp_reg_staged_program [] (LPPEVariable ''x'') (Var ''x'') ([],[],[]) lpp_reg_staged_link)]"

definition lpp_context_graph_regressions where
  "lpp_context_graph_regressions = [
    (''empty-root-context'',lpp_reg_root_check lpp_reg_graph_contexts 0),
    (''unproved-root-context'',\<not>lpp_reg_root_check ([([],[LPPSInteger (Var ''x'')],[])]@tl lpp_reg_graph_contexts) 0),
    (''root-index-bound'',\<not>lpp_reg_root_check lpp_reg_graph_contexts 3),
    (''complete-context-table'',lpp_reg_graph_check lpp_reg_graph_program lpp_reg_graph_contexts lpp_reg_graph_actions),
    (''missing-source-branch'',\<not>lpp_reg_graph_check (tl lpp_reg_graph_program) lpp_reg_graph_contexts lpp_reg_graph_actions),
    (''missing-context-row'',\<not>lpp_reg_graph_check lpp_reg_graph_program (tl lpp_reg_graph_contexts) lpp_reg_graph_actions),
    (''missing-action-row'',\<not>lpp_reg_graph_check lpp_reg_graph_program lpp_reg_graph_contexts (tl lpp_reg_graph_actions)),
    (''invented-success-context'',\<not>lpp_reg_graph_check lpp_reg_graph_program
      [([],[],[]),([],[LPPSInteger (Var ''x'')],[]),([],[],[])] lpp_reg_graph_actions),
    (''lost-successful-return'',\<not>lpp_reg_graph_check (take 3 lpp_reg_graph_program) lpp_reg_graph_contexts lpp_reg_graph_actions)]"
end
