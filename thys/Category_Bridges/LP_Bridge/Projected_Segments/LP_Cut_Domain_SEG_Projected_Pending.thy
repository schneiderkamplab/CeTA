theory LP_Cut_Domain_SEG_Projected_Pending
 imports LP_Cut_Domain_SEG_Projected_Region_Check
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_projected_pending_actual:
  fixes filtering :: "'g afs" and depth :: nat
  assumes checked: "lpc_seg_check_projected_pair filtering 2 depth is_cont c d R
      (Fun u (outp#caps)) next"
    and cont: "is_cont u"
    and actual: "precise_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term outp \<subseteq> set vs" "vars_term next \<subseteq> set vs"
    and keep: "lpc_seg_projected_continuation_filter filtering (c u) (Suc (length caps))"
    and observed: "lpc_seg_has_projection filtering
      (lpc_seg_runtime_pending c d u caps eta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs outp) rho))"
  shows "(lpc_seg_runtime_pending c d u caps eta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs outp) rho),
      lpc_seg_role_value depth is_cont c d (lp_ieval (lpc_seg_position_template vs next) rho))
      \<in>lpc_seg_projected_rel filtering R"
proof -
  let ?caps="map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) caps"
  obtain indices where af: "afs filtering (c u,Suc (length caps))=AFList (0#map Suc indices)"
    by (rule lpc_seg_projected_continuation_filterD[OF keep]) blast
  have af': "afs filtering (c u,Suc (length ?caps))=AFList (0#map Suc indices)" using af by simp
  obtain n :: "('g,string) term" and ms :: "('g,string) term list"
    where pr: "lp_iproject filtering (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template vs outp) rho) n"
      and captured: "list_all2 (\<lambda>i m. i<length ?caps \<and> lp_iproject filtering (?caps!i) m) indices ms"
    by (rule lpc_seg_projected_pending_components[OF af' observed[unfolded lpc_seg_runtime_pending_def]]) blast
  have captures: "list_all2 (\<lambda>i m. i<length caps \<and>
    lp_iproject filtering (map_lp_iterm d id (lp_ieval (caps!i) eta)) m) indices ms"
    using captured by (auto simp: list_all2_conv_all_nth)
  show ?thesis using precise_seg_projected_actual_step[OF checked cont actual distinct vars af captures
      pr[unfolded lpc_seg_runtime_value_def]]
    by (simp only: lpc_seg_runtime_pending_def lpc_seg_runtime_value_def)
qed


end
end
