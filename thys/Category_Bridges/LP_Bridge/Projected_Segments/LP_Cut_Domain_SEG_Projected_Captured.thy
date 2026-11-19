theory LP_Cut_Domain_SEG_Projected_Captured
 imports Category_LP_Cut_Free_Segment_Bridge.LP_Cut_Domain_SEG_Free_Checker
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_seg_projected_captured_step:
  fixes pi :: "'f lp_cut_symbol afs"
    and measure :: "('f lp_cut_symbol,'w) term"
  assumes step: "precise_answer_transition P ss event us"
    and known: "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) ss"
  shows "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> lp_iproject pi (lp_ieval t eta) measure)"
  using step known
  by (cases rule: precise_answer_transition.cases)
    (auto simp: list_all_iff lp_ieval_subst[symmetric]
      intro: lp_iproject_subst
      dest: subsetD[OF lpc_answer_prune_set_subset])


lemma precise_seg_projected_captured_actual:
  fixes pi :: "'f lp_cut_symbol afs"
    and measure :: "('f lp_cut_symbol,'w) term"
  assumes actual: "precise_actual_return P ss eta"
    and known: "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) ss"
  shows "lp_iproject pi (lp_ieval t eta) measure"
proof -
  obtain us tail where path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some eta) tail"
    using actual by (auto simp: precise_actual_return_def)
  have preserved: "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) us"
    using path known
    by (induct rule: rtrancl_induct)
      (auto simp: precise_answer_steps_def dest: precise_seg_projected_captured_step)
  show ?thesis using precise_seg_projected_captured_step[OF event preserved] by simp
qed


lemma precise_seg_observed_projected_captured_term:
  fixes pi :: "'f lp_cut_symbol afs"
    and measure :: "('f lp_cut_symbol,'w) term"
  assumes actual: "precise_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term t \<subseteq> set vs"
    and observed: "lp_iproject pi (lp_ieval t eta) measure"
  shows "lp_iproject pi
    (lp_ieval (lpc_seg_position_template vs t) rho) measure"
proof -
  obtain theta where source: "precise_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using precise_seg_observed_actual[OF actual] by blast
  have preserved: "lp_iproject pi (lp_ieval t theta) measure"
    by (rule precise_seg_projected_captured_actual[OF source]) (simp add: observed)
  show ?thesis unfolding rho
    by (simp only: lpc_seg_position_eval[OF distinct vars] preserved)
qed


end
end
