theory LP_Prolog_Integer_Node_Regression
  imports LP_Prolog_Context_Is
begin

text \<open>Executable local-node regressions, not source-root certificates.
The source graph must separately establish every integer-domain premise.\<close>

definition lpp_reg_node :: "string lpc_state \<Rightarrow> string \<Rightarrow> string lpc_node" where
  "lpp_reg_node ss p = \<lparr>lpcn_state=ss,lpcn_ground=[],lpcn_guards=[],lpcn_vars=[],lpcn_pred=LPCUser p\<rparr>"
definition lpp_reg_link :: "nat \<Rightarrow> string lpc_state \<Rightarrow> string lpc_link" where
  "lpp_reg_link i ss = \<lparr>lpcl_target=i,lpcl_vars=[],lpcl_terms=[],lpcl_state=ss,
    lpcl_ground=[],lpcl_guards=[],lpcl_bindings=[],lpcl_swaps=[],lpcl_lhs=[],lpcl_rhs=[]\<rparr>"
definition lpp_reg_nodes where
  "lpp_reg_nodes = [lpp_reg_node [LPCGoals []] ''yes'',lpp_reg_node [] ''no'']"
definition lpp_reg_states :: "string lpc_return_state list" where
  "lpp_reg_states = [[(LPCGoals [],[])],[]]"
definition lpp_reg_program :: "(string lp_cut_symbol,string) lp_clause list" where
  "lpp_reg_program = [((LPCUser ''source'',[]),[(LPCUser ''yes'',[])]),
    ((LPCUser ''source'',[]),[(LPCUser ''no'',[])])]"
definition lpp_reg_source :: "string \<Rightarrow> string lpc_term list \<Rightarrow> string lpc_return_state" where
  "lpp_reg_source f ts = [(LPCGoals [LPCAtom (Fun (LPCUser f) ts)],[])]"
abbreviation lpp_reg_yes where "lpp_reg_yes \<equiv> lpp_reg_link 0 [LPCGoals []]"
abbreviation lpp_reg_no where "lpp_reg_no \<equiv> lpp_reg_link 1 []"

definition lpp_reg_integer_test where
  "lpp_reg_integer_test Q yes no = (let ss=lpp_reg_source ''1:integer'' [lpp_integer_term 7] in
    lpp_check_integer_test_node 40 Q lpp_reg_nodes lpp_reg_states (lpp_reg_node (map fst ss) ''source'')
      ss (lpp_integer_term 7) [] [] [] yes no)"
definition lpp_reg_comparison where
  "lpp_reg_comparison Q comparison reversed yes no = (let ss=lpp_reg_source ''2:<'' [lpp_integer_term 7,lpp_integer_term 9] in
    lpp_check_integer_comparison_node 40 Q lpp_reg_nodes lpp_reg_states (lpp_reg_node (map fst ss) ''source'')
      ss [] ''2:<'' comparison reversed (lpp_integer_term 7) (lpp_integer_term 9)
      (LPPEConstant 7) (LPPEConstant 9) [] [] [] yes no)"
definition lpp_reg_is where
  "lpp_reg_is Q K evidence a e result_var yes no = (let ss=lpp_reg_source ''2:is'' [a,e] in
    lpp_check_integer_is_node 40 ([]::(string,string) lp_cut_program) Q lpp_reg_nodes lpp_reg_states (lpp_reg_node (map fst ss) ''source'')
      ss K evidence a e [] [] [] result_var 8 16 [] LPCBoth [] yes no)"

definition lpp_integer_node_regressions where
  "lpp_integer_node_regressions = [
    (''integer-test'',lpp_reg_integer_test lpp_reg_program lpp_reg_yes lpp_reg_no),
    (''comparison'',lpp_reg_comparison lpp_reg_program LPPIntLess False lpp_reg_yes lpp_reg_no),
    (''closed-is'',lpp_reg_is lpp_reg_program [] (LPPEConstant 1) (lpp_integer_term 1) (lpp_integer_term 1) ''r'' lpp_reg_yes lpp_reg_no),
    (''symbolic-is'',lpp_reg_is lpp_reg_program [''x''] (LPPEVariable ''x'') (lpp_integer_term 1) (Var ''x'') ''r'' lpp_reg_yes lpp_reg_no),
    (''missing-test-branch'',\<not>lpp_reg_integer_test (take 1 lpp_reg_program) lpp_reg_yes lpp_reg_no),
    (''swapped-test-links'',\<not>lpp_reg_integer_test lpp_reg_program lpp_reg_no lpp_reg_yes),
    (''changed-comparator'',\<not>lpp_reg_comparison lpp_reg_program LPPIntEqual False lpp_reg_yes lpp_reg_no),
    (''changed-orientation'',\<not>lpp_reg_comparison lpp_reg_program LPPIntLess True lpp_reg_yes lpp_reg_no),
    (''lost-is-type-premise'',\<not>lpp_reg_is lpp_reg_program [] (LPPEVariable ''x'') (lpp_integer_term 1) (Var ''x'') ''r'' lpp_reg_yes lpp_reg_no),
    (''captured-result-variable'',\<not>lpp_reg_is lpp_reg_program [] (LPPEConstant 1) (Var ''r'') (lpp_integer_term 1) ''r'' lpp_reg_yes lpp_reg_no),
    (''changed-is-source'',\<not>lpp_reg_is lpp_reg_program [] (LPPEConstant 2) (lpp_integer_term 1) (lpp_integer_term 1) ''r'' lpp_reg_yes lpp_reg_no),
    (''missing-is-branch'',\<not>lpp_reg_is (take 1 lpp_reg_program) [] (LPPEConstant 1) (lpp_integer_term 1) (lpp_integer_term 1) ''r'' lpp_reg_yes lpp_reg_no)]"


definition lpp_reg_action where
  "lpp_reg_action Q f ts action = (let ss=lpp_reg_source f ts in
    lpp_check_integer_return_action 40 ([]::(string,string) lp_cut_program) Q
      lpp_reg_nodes lpp_reg_states (lpp_reg_node (map fst ss) ''source'') ss (LPCUser ''return'') 0 action)"

definition lpp_integer_action_regressions where
  "lpp_integer_action_regressions = [
    (''action-integer-test'',lpp_reg_action lpp_reg_program ''1:integer'' [lpp_integer_term 7]
      (LPPIRTest (lpp_integer_term 7) [] [] [] lpp_reg_yes lpp_reg_no)),
    (''action-missing-branch'',\<not>lpp_reg_action (take 1 lpp_reg_program) ''1:integer'' [lpp_integer_term 7]
      (LPPIRTest (lpp_integer_term 7) [] [] [] lpp_reg_yes lpp_reg_no)),
    (''action-comparison'',lpp_reg_action lpp_reg_program ''2:<'' [lpp_integer_term 7,lpp_integer_term 9]
      (LPPIRCompare [] ''2:<'' LPPIntLess False (lpp_integer_term 7) (lpp_integer_term 9)
        (LPPEConstant 7) (LPPEConstant 9) [] [] [] lpp_reg_yes lpp_reg_no)),
    (''action-symbolic-is'',lpp_reg_action lpp_reg_program ''2:is'' [lpp_integer_term 1,Var ''x'']
      (LPPIRIs [''x''] (LPPEVariable ''x'') (lpp_integer_term 1) (Var ''x'') [] [] [] ''r'' 8 16 [] LPCBoth [] lpp_reg_yes lpp_reg_no)),
    (''action-lost-is-domain'',\<not>lpp_reg_action lpp_reg_program ''2:is'' [lpp_integer_term 1,Var ''x'']
      (LPPIRIs [] (LPPEVariable ''x'') (lpp_integer_term 1) (Var ''x'') [] [] [] ''r'' 8 16 [] LPCBoth [] lpp_reg_yes lpp_reg_no)),
    (''action-cannot-use-plain-cut-rule'',\<not>lpp_reg_action lpp_reg_program ''1:integer'' [lpp_integer_term 7]
      (LPPIRCut LPCRTerminal))]"


definition lpp_reg_context_test :: "string lpp_source_context list \<Rightarrow> bool" where
  "lpp_reg_context_test contexts = (let ss=lpp_reg_source ''1:integer'' [lpp_integer_term 7] in
    lpp_check_context_integer_test 40 lpp_reg_program lpp_reg_nodes lpp_reg_states contexts
      (lpp_reg_node (map fst ss) ''source'') ss ([],[],[]) (lpp_integer_term 7)
      [] [] [] lpp_reg_yes lpp_reg_no)"

definition lpp_context_node_regressions where
  "lpp_context_node_regressions = [
    (''context-integer-success'',lpp_reg_context_test
      [([],[LPPSInteger (lpp_integer_term 7)],[LPPOInteger (lpp_integer_term 7)]),([],[],[])]),
    (''context-no-fact-on-failure'',\<not>lpp_reg_context_test
      [([],[],[]),([],[LPPSInteger (lpp_integer_term 7)],[])]),
    (''context-no-unrelated-variable'',\<not>lpp_reg_context_test
      [([],[LPPSInteger (Var ''x'')],[]),([],[],[])]),
    (''context-no-invented-evaluation'',\<not>lpp_reg_context_test
      [([],[],[LPPOEvaluation (lpp_integer_term 0) (lpp_integer_term 1)]),([],[],[])])]"

definition lpp_reg_context_comparison :: "string lpp_source_context list \<Rightarrow> bool" where
  "lpp_reg_context_comparison contexts = (let ss=lpp_reg_source ''2:<'' [lpp_integer_term 7,lpp_integer_term 9] in
    lpp_check_context_comparison 40 lpp_reg_program lpp_reg_nodes lpp_reg_states contexts
      (lpp_reg_node (map fst ss) ''source'') ss ([],[],[]) [] ''2:<'' LPPIntLess False
      (lpp_integer_term 7) (lpp_integer_term 9) (LPPEConstant 7) (LPPEConstant 9)
      [] [] [] lpp_reg_yes lpp_reg_no)"

definition lpp_reg_context_is :: "string lpp_source_context \<Rightarrow> string lpp_source_context list \<Rightarrow> nat \<Rightarrow> bool" where
  "lpp_reg_context_is source_context contexts k = (let ss=lpp_reg_source ''2:is'' [lpp_integer_term 1,lpp_integer_term 1] in
    lpp_check_context_is_node 40 ([]::(string,string) lp_cut_program) lpp_reg_program lpp_reg_nodes lpp_reg_states contexts
      (lpp_reg_node (map fst ss) ''source'') ss source_context [] (LPPEConstant 1)
      (lpp_integer_term 1) (lpp_integer_term 1) [] [] [] ''r'' k (2 * k) [] LPCBoth [] lpp_reg_yes lpp_reg_no)"

definition lpp_context_arithmetic_regressions where
  "lpp_context_arithmetic_regressions = [
    (''comparison-observation'',lpp_reg_context_comparison
      [([],[],[LPPOComparison LPPIntLess (lpp_integer_term 7) (lpp_integer_term 9)]),([],[],[])]),
    (''comparison-no-fact-on-failure'',\<not>lpp_reg_context_comparison
      [([],[],[]),([],[],[LPPOComparison LPPIntLess (lpp_integer_term 7) (lpp_integer_term 9)])]),
    (''comparison-no-reversed-fact'',\<not>lpp_reg_context_comparison
      [([],[],[LPPOComparison LPPIntLess (lpp_integer_term 9) (lpp_integer_term 7)]),([],[],[])]),
    (''context-is'',lpp_reg_context_is ([],[],[]) [([],[],[]),([],[],[])] 8),
    (''context-is-result-observation'',lpp_reg_context_is ([],[],[])
      [([],[LPPSEvaluates (lpp_integer_term 1) (Var ''r'')],[LPPOEvaluation (lpp_integer_term 1) (Var ''r'')]),([],[],[])] 8),
    (''context-is-captured-annotation-variable'',\<not>lpp_reg_context_is ([],[LPPSInteger (Var ''r'')],[]) [([],[],[]),([],[],[])] 8),
    (''context-is-too-small-refresh'',\<not>lpp_reg_context_is ([],[LPPSInteger (Var ''longcontextvariable'')],[]) [([],[],[]),([],[],[])] 8),
    (''context-is-invented-value'',\<not>lpp_reg_context_is ([],[],[])
      [([],[],[LPPOEvaluation (lpp_integer_term 1) (lpp_integer_term 2)]),([],[],[])] 8)]"

ML \<open>
val checked = [@{thm lpp_integer_is_node_sound}, @{thm lpp_integer_test_node_sound},
  @{thm lpp_integer_comparison_node_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer source-node dependency" else ();
\<close>
end
