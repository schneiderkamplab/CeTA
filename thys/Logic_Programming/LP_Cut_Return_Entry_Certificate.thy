theory LP_Cut_Return_Entry_Certificate
 imports LP_Cut_Return_Residual_Query LP_Cut_Return_Split_Check
begin

type_synonym lpc_child_symbol = "(string,nat list) lab"

record 'f lpc_residual_certificate =
  lpcrc_source :: "('f lp_cut_symbol,string) lp_clause list"
  lpcrc_predicates :: "('f lp_cut_symbol \<times> lpc_child_symbol) list"
  lpcrc_constructors :: "('f lp_cut_symbol \<times> lpc_child_symbol) list"
  lpcrc_program :: "(lpc_child_symbol,string) lp_clause list"
  lpcrc_outs :: "(lpc_child_symbol \<times> lpc_child_symbol) list"
  lpcrc_fallback :: lpc_child_symbol
  lpcrc_names :: "lpc_child_symbol list list"
  lpcrc_marks :: "(lpc_child_symbol \<times> lpc_child_symbol) list"
  lpcrc_filters :: "((lpc_child_symbol \<times> nat) \<times> af_entry) list"
  lpcrc_query :: lpc_child_symbol
  lpcrc_arity :: nat
  lpcrc_positions :: "nat list"
  lpcrc_seed :: lpc_child_symbol
  lpcrc_nfs :: bool
  lpcrc_proof :: "(string,nat list,string) dp_termination_proof"

definition lpc_check_residual_certificate where
  "lpc_check_residual_certificate I J nd c =
    lpc_check_residual_query I J (lpcrc_source c) nd (lpcrc_predicates c) (lpcrc_constructors c)
      (lpcrc_program c) (lpcrc_outs c) (lpcrc_fallback c) (lpcrc_names c) (lpcrc_marks c)
      (lpcrc_filters c) (lpcrc_query c) (lpcrc_arity c) (lpcrc_positions c) (lpcrc_seed c)
      (lpcrc_nfs c) (lpcrc_proof c)"

lemma lpc_check_residual_certificate_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "lpc_check_residual_certificate I J nd c"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
  shows "SN_on (lp_ild (lpcrc_source c)) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  by (rule lpc_check_residual_query_sound[OF I J _ known])
    (use checked in \<open>simp add: lpc_check_residual_certificate_def\<close>)

definition lpc_check_return_entry_certificate where
  "lpc_check_return_entry_certificate I J fuel P nd original m e c =
    (lp_cut_source_program P \<and>
     lpc_check_return_module_data fuel P (lpcrc_source c) m \<and>
     lpc_check_return_table_link fuel (lpcrc_source c) (lpcrm_nodes m) (lpcrm_states m)
       nd original (lpcn_ground nd) (lpcn_guards nd) [] e \<and>
     lpc_check_residual_certificate I J nd c)"

theorem lpc_check_return_entry_certificate_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "lpc_check_return_entry_certificate I J fuel P nd original m e c"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
  shows "lpc_return_contract P (lpc_return_eval eta original) (lp_ild (lpcrc_source c))
    [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(lpcrm_returned m,map rho [0..<lpcrm_arity m])])"
proof -
  have residual: "SN_on (lp_ild (lpcrc_source c)) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
    by (rule lpc_check_residual_certificate_sound[OF I J _ known])
      (use checked in \<open>simp add: lpc_check_return_entry_certificate_def\<close>)
  show ?thesis by (rule lpc_return_module_link_contract[OF _ _ _ known residual])
    (use checked in \<open>auto simp: lpc_check_return_entry_certificate_def lpc_check_return_module_data_def\<close>)
qed

end
