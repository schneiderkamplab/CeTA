theory LP_Cut_Domain_Return_Overapproximation
 imports LP_Cut_Domain_Return_Independent_Certificate
begin

context cut_runtime_domain
begin

theorem precise_independent_return_contract:
  assumes checked: "lpc_check_universal_return_edge Q nd returned arity outputs"
    and source: "SN_on (precise_source P) {map fst (lpc_return_eval eta original)}"
  shows "precise_return_contract P (lpc_return_eval eta original) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
  using source lpc_universal_return_edge_sound[OF checked, of eta]
  by (auto simp: precise_return_contract_def intro: r_into_rtrancl)



end
end
