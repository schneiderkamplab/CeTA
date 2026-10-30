theory LP_Prolog_Numeric_Calls_Regression
 imports LP_Prolog_Numeric_Code_Setup
begin

abbreviation lppnc_rx where "lppnc_rx \<equiv> Var (''X''::string)"
abbreviation lppnc_ry where "lppnc_ry \<equiv> Var (''Y''::string)"
abbreviation lppnc_decrement where
  "lppnc_decrement \<equiv> LPPESubtract (LPPEVariable (''X''::string)) (LPPEConstant 1)"

definition lppnc_regression_row :: "string lpp_observed_triple" where
  "lppnc_regression_row = (((''loop'',[lppnc_rx]),[],(''loop'',[lppnc_ry]),
    [LPPSInteger lppnc_rx,LPPSEvaluates (lpp_expression_term lppnc_decrement) lppnc_ry]),
    [LPPOInteger lppnc_rx,
     LPPOComparison LPPIntLess (lpp_expression_term (LPPEConstant 0)) lppnc_rx,
     LPPOEvaluation (lpp_expression_term lppnc_decrement) lppnc_ry])"

definition lppnc_regression_receipt :: "string lpp_numeric_call_receipt" where
  "lppnc_regression_receipt =
    (let inputs=[(''v0'',lppnc_rx,LPPEVariable ''X'')];
         outputs=[(''v0'',lppnc_ry,LPPEVariable ''Y'')];
         tests=[(LPPIntLess,LPPEConstant 0,LPPEVariable ''X''),
           (LPPIntEqual,LPPEVariable ''Y'',lppnc_decrement)];
         bindings=[(''X'',Pre ''v0''),(''Y'',Post ''aux'')]
     in \<lparr>lppnc_facts=[LPPTBase (LPPSGuard 0 ''X''),LPPTBase (LPPSEvaluation 1 lppnc_decrement ''Y'')],
       lppnc_inputs= inputs,lppnc_outputs= outputs,lppnc_tests= tests,lppnc_bindings= bindings,
       lppnc_formula= lpp_numeric_path_formula inputs outputs tests bindings\<rparr>)"

definition lppnc_regression_system where
  "lppnc_regression_system = \<lparr>lts.initial={''loop''},
    transition_rules={Transition ''loop'' ''loop'' (lppnc_formula lppnc_regression_receipt)},
    assertion=(\<lambda>_. Conjunction [])\<rparr>"

definition lppnc_regression_check where
  "lppnc_regression_check system D receipts =
    lpp_check_numeric_calls (\<lambda>_. []) (\<lambda>_. [''v0'']) id system D receipts"

definition lpp_numeric_call_regressions :: "(string * bool) list" where
  "lpp_numeric_call_regressions =
    [(''complete typed countdown'',
      lppnc_regression_check lppnc_regression_system [lppnc_regression_row] [lppnc_regression_receipt]),
     (''missing path receipt'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row] []),
     (''missing transition'',
      \<not>lppnc_regression_check (lppnc_regression_system\<lparr>transition_rules:={}\<rparr>)
        [lppnc_regression_row] [lppnc_regression_receipt]),
     (''lost integer context'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row]
        [lppnc_regression_receipt\<lparr>lppnc_facts:=[]\<rparr>]),
     (''incorrect input correspondence'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row]
        [lppnc_regression_receipt\<lparr>lppnc_inputs:=[(''v0'',lppnc_ry,LPPEVariable ''Y'')]\<rparr>]),
     (''incorrect output correspondence'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row]
        [lppnc_regression_receipt\<lparr>lppnc_outputs:=[(''v0'',lppnc_rx,LPPEVariable ''X'')]\<rparr>]),
     (''corrupted decrement'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row]
        [lppnc_regression_receipt\<lparr>lppnc_formula:= Conjunction []\<rparr>]),
     (''missing observed guard'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row]
        [lppnc_regression_receipt\<lparr>lppnc_tests:= tl (lppnc_tests lppnc_regression_receipt)\<rparr>]),
     (''post auxiliary overwrites call coordinate'',
      \<not>lppnc_regression_check lppnc_regression_system [lppnc_regression_row]
        [lppnc_regression_receipt\<lparr>lppnc_bindings:=[(''X'',Pre ''v0''),(''Y'',Post ''v0'')]\<rparr>]) ]"

end
