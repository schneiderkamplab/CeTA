theory LP_Cut_Domain_SEG_Projected_Certificate
 imports LP_Cut_Domain_SEG_Projected_Graph
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_check_lpc_seg_projected_certificate_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lpc_seg_projected_certificate I J fuel P roots Fs regions q modes continuations controls data_map fallback filters trs_rules prf"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
    and domains: "list_all D ts"
  shows "SN_on (precise_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  interpret tp_spec I by (rule I)
  obtain filtering where filter: "afs_of filters=Some filtering"
    using checked unfolding check_lpc_seg_projected_certificate_def
    by (cases "afs_of filters") auto
  have graph: "lpc_seg_check_projected_graph fuel P roots Fs regions q modes filtering
      (\<lambda>f. f\<in>set continuations) (lpc_lookup fallback controls)
      (lpc_lookup fallback data_map) (set trs_rules)"
    and child: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (map (af_rule filtering) trs_rules) []) prf)"
    using checked by (auto simp: check_lpc_seg_projected_certificate_def filter)
  have sn: "SN (rstep (set (map (af_rule filtering) trs_rules)))"
    using check_trs_termination_proof[OF I J child] by (simp add: SN_qrel_def)
  show ?thesis by (rule precise_seg_projected_graph_root_sound[OF graph sn[simplified] len ground domains])
qed


end
end
