theory LP_Cut_Domain_SEG_Interfaces
 imports LP_Cut_Domain_SEG_TRS_Returns
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_instance_return_contract:
  assumes child: "precise_return_contract P (lpc_return_eval eta ss) R u ret"
    and entry: "(t,u)\<in>R\<^sup>*"
    and bridge: "\<And>rho. (ret rho,final (lpc_seg_observe templates rho))\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_return_eval eta (lpc_seg_reinterface templates ss)) R t final"
proof -
  have projected: "precise_return_contract P
    (lpc_reinterface (lpc_seg_observe templates) (lpc_return_eval eta ss)) R u final"
    by (rule precise_return_contract_project[where F="lpc_seg_observe templates", OF lpc_seg_observe_commutes child bridge])
  have renamed: "precise_return_contract P (lpc_return_eval eta (lpc_seg_reinterface templates ss)) R u final"
    using projected by (simp only: lpc_seg_reinterface_sound)
  show ?thesis by (rule precise_return_contract_start[OF entry renamed])
qed


end
end
