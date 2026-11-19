theory LP_Cut_Domain_SEG_Projected_Relation
 imports LP_Cut_Domain_SEG_Projected_Captured
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_projected_recursive_split:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs v out. (t,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      rep vs v out \<Longrightarrow> precise_return_contract P vs (lpc_seg_projected_rel filtering R) v out"
    and entry: "(t,p)\<in>(lpc_seg_projected_rel filtering R)\<^sup>+"
    and prefix_rep: "rep ss p ret"
    and initial: "lpc_seg_has_projection filtering p"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. (p,ret eta)\<in>(lpc_seg_projected_rel filtering R)\<^sup>* \<Longrightarrow>
      lpc_seg_has_projection filtering (ret eta) \<Longrightarrow> \<exists>v.
      (ret eta,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>* \<and>
      rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v final"
  shows "precise_return_contract P (lpc_attach_answers rest ss) (lpc_seg_projected_rel filtering R) t final"
proof (rule precise_seg_split_lower_actual[where rep=rep and R="lpc_seg_projected_rel filtering R"
    and t=t and p=p and ss=ss and ret=ret and final=final and rest=rest,
    OF program lower entry prefix_rep valid separated])
  fix eta assume actual: "precise_actual_return P ss eta"
  have prefix: "precise_return_contract P ss (lpc_seg_projected_rel filtering R) p ret"
    by (rule lower[OF entry prefix_rep])
  have reached: "(p,ret eta)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    by (rule precise_actual_return_residual[OF prefix actual])
  have observed: "lpc_seg_has_projection filtering (ret eta)"
    by (rule lpc_seg_projected_reachable[OF reached initial])
  show "\<exists>v out. (ret eta,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>* \<and>
    rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] v out \<and>
    (\<forall>mu. precise_actual_return P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] mu \<longrightarrow>
      (out mu,final mu)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*)"
    using continuation[OF reached observed] by blast
qed


lemma precise_seg_projected_contract_answer:
  assumes contract: "precise_return_contract P ss (lpc_seg_projected_rel filtering R) t ret"
    and initial: "lpc_seg_has_projection filtering t"
    and actual: "precise_actual_return P ss eta"
  shows "lpc_seg_has_projection filtering (ret eta)"
proof -
  have reached: "(t,ret eta)\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    using contract actual by (auto simp: precise_return_contract_def precise_actual_return_def)
  show ?thesis by (rule lpc_seg_projected_reachable[OF reached initial])
qed


end
end
