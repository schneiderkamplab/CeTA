theory LP_Cut_SEG_Projected_Captured
  imports LP_Cut_SEG_Captured LP_Cut_Return_Projection
begin

text \<open>Continuation arguments need not be ground before filtering.
Only their finite observations must survive resolution and backtracking.
Each saved frame keeps its own environment; no equality of unfiltered
runtime terms is assumed.\<close>

lemma lpc_seg_projected_captured_step:
  fixes pi :: "'f lp_cut_symbol afs"
    and measure :: "('f lp_cut_symbol,'w) term"
  assumes step: "lpc_answer_transition P ss event us"
    and known: "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) ss"
  shows "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> lp_iproject pi (lp_ieval t eta) measure)"
  using step known
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: list_all_iff lp_ieval_subst[symmetric]
      intro: lp_iproject_subst
      dest: subsetD[OF lpc_answer_prune_set_subset])

lemma lpc_seg_projected_captured_actual:
  fixes pi :: "'f lp_cut_symbol afs"
    and measure :: "('f lp_cut_symbol,'w) term"
  assumes actual: "lpc_actual_return P ss eta"
    and known: "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) ss"
  shows "lp_iproject pi (lp_ieval t eta) measure"
proof -
  obtain us tail where path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some eta) tail"
    using actual by (auto simp: lpc_actual_return_def)
  have preserved: "list_all (\<lambda>e. lp_iproject pi (lp_ieval t (snd e)) measure) us"
    using path known
    by (induct rule: rtrancl_induct)
      (auto simp: lpc_answer_steps_def dest: lpc_seg_projected_captured_step)
  show ?thesis using lpc_seg_projected_captured_step[OF event preserved] by simp
qed

lemma lpc_seg_observed_projected_captured_term:
  fixes pi :: "'f lp_cut_symbol afs"
    and measure :: "('f lp_cut_symbol,'w) term"
  assumes actual: "lpc_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and distinct: "distinct vs"
    and vars: "vars_term t \<subseteq> set vs"
    and observed: "lp_iproject pi (lp_ieval t eta) measure"
  shows "lp_iproject pi
    (lp_ieval (lpc_seg_position_template vs t) rho) measure"
proof -
  obtain theta where source: "lpc_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpc_seg_observed_actual[OF actual] by blast
  have preserved: "lp_iproject pi (lp_ieval t theta) measure"
    by (rule lpc_seg_projected_captured_actual[OF source]) (simp add: observed)
  show ?thesis unfolding rho
    by (simp only: lpc_seg_position_eval[OF distinct vars] preserved)
qed

end
