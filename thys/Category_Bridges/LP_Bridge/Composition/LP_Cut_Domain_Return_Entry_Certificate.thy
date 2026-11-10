theory LP_Cut_Domain_Return_Entry_Certificate
 imports LP_Cut_Domain_Return_Residual_Query
begin

context cut_runtime_domain
begin

lemma precise_check_residual_certificate_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "lpc_check_residual_certificate I J nd c"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
  shows "SN_on (lp_ild (lpcrc_source c)) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  by (rule precise_check_residual_query_sound[OF I J _ known])
    (use checked in \<open>simp add: lpc_check_residual_certificate_def\<close>)



theorem precise_check_return_entry_certificate_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "lpc_check_return_entry_certificate I J fuel P nd original m e c"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
  shows "precise_return_contract P (lpc_return_eval eta original) (lp_ild (lpcrc_source c))
    [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(lpcrm_returned m,map rho [0..<lpcrm_arity m])])"
proof -
  have residual: "SN_on (lp_ild (lpcrc_source c)) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
    by (rule precise_check_residual_certificate_sound[OF I J _ known])
      (use checked in \<open>simp add: lpc_check_return_entry_certificate_def\<close>)
  show ?thesis by (rule precise_return_module_link_contract[OF _ _ _ known residual])
    (use checked in \<open>auto simp: lpc_check_return_entry_certificate_def lpc_check_return_module_data_def\<close>)
qed



end
end
