theory LP_Cut_Domain_Return_Module_Link
  imports LP_Cut_Domain_Return_Domain_Compose
begin

context cut_runtime_domain
begin

theorem precise_return_module_link_contract:
  assumes module: "lpc_check_return_module fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P"
    and link: "lpc_check_return_table_link fuel Q nds states nd ss G guards [] e"
    and known: "knowledge (set G) guards eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  shows "precise_return_contract P (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
    and represented: "precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta ss)) u"
    using precise_return_table_link_sound[OF link equations refl known] by blast
  obtain j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps (lpc_return_eval eta ss)=lpc_return_eval nu (states!j)"
    and knowledge: "knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and u: "u=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: precise_return_rep_def)
  have child_sn: "SN_on (lp_ild Q) {u}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
      (use trancl_into_rtrancl[OF strict] in auto)
  have child: "precise_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q) u
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding u by (rule precise_check_return_module_contract[OF module program bound knowledge])
      (use child_sn u in simp)
  have restored: "precise_return_contract P
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) u
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule precise_return_contract_scopes[OF program child])
  have original: "precise_return_contract P (lpc_return_eval eta ss) (lp_ild Q) u
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  show ?thesis by (rule precise_return_contract_start[OF trancl_into_rtrancl[OF strict] original])
qed


end
end
